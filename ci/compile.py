#!/usr/bin/env python3
"""Direct Lean DAG compiler: at most two processes, two Lean threads each.

Only CI executes this script. Each local module is freshly compiled with
`lake env lean -j2 -o ... source.lean`; Lake never builds local modules.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

from audit import lean_code

ROOT = Path(__file__).resolve().parent.parent
LOCAL_PREFIX = "ZetaBetaHankel"
TARGETS = ("ZetaBetaHankel.Zeta357VerifiedChain", "ZetaBetaHankel.Audit", "ZetaBetaHankel.Zeta357NativeAudit")
MAX_PROCESSES = 2
LEAN_THREADS = 2
TIMEOUT_SECONDS = 20 * 60
OUTPUT_ROOT = ROOT / ".lake/build/lib/lean"
LOG_ROOT = ROOT / "logs/modules"
MANIFEST = ROOT / "logs/compile-results.json"


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def imports(path: Path) -> list[str]:
    result: list[str] = []
    for line in lean_code(path.read_text(encoding="utf-8")).splitlines():
        match = re.match(r"^\s*(?:public\s+)?import\s+(.+?)\s*$", line)
        if match:
            names = match.group(1).split()
            if not all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.']*", n) for n in names):
                raise ValueError(f"Unparsed import declaration in {path}: {line}")
            result.extend(names)
    return list(dict.fromkeys(result))


def module_path(module: str, suffix: str) -> Path:
    return Path(module.replace(".", "/") + suffix)


def make_graph(root: Path, targets: tuple[str, ...] = TARGETS) -> dict[str, dict]:
    graph: dict[str, dict] = {}
    active: list[str] = []

    def visit(name: str) -> None:
        if name in active:
            raise ValueError("Local import cycle: " + " -> ".join(active + [name]))
        if name in graph:
            return
        if name == "ZetaBetaHankel.EvidenceAudit":
            raise ValueError("EvidenceAudit must remain a separate fresh final invocation")
        source = root / module_path(name, ".lean")
        if not source.is_file():
            raise ValueError(f"Missing local module/source: {name}: {source}")
        all_imports = imports(source)
        local_imports = [n for n in all_imports
                         if n == LOCAL_PREFIX or n.startswith(LOCAL_PREFIX + ".")]
        active.append(name)
        for dependency in local_imports:
            visit(dependency)
        active.pop()
        graph[name] = {"source": source.relative_to(root).as_posix(),
                       "sha256": sha(source), "imports": all_imports,
                       "dependencies": local_imports, "status": "pending"}

    for target in targets:
        visit(target)
    return graph


def stop(process: subprocess.Popen) -> None:
    if process.poll() is None:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    process.wait()


def compile_graph() -> int:
    LOG_ROOT.mkdir(parents=True, exist_ok=True)
    graph = make_graph(ROOT)
    preflight = ROOT / "logs/provenance.json"
    if not preflight.is_file():
        raise ValueError("Missing preflight provenance")
    original_provenance = json.loads(preflight.read_text())
    metadata = {
        "targets": list(TARGETS), "max_processes": MAX_PROCESSES,
        "lean_threads_per_process": LEAN_THREADS, "timeout_seconds_per_module": TIMEOUT_SECONDS,
        "compiler_command_template": ["lake", "env", "lean", "-j2", "-o", "OUTPUT.olean", "SOURCE.lean"],
        "commit": original_provenance["commit"],
        "toolchain": original_provenance["toolchain"],
        "mathlib_commit": original_provenance["mathlib_commit"],
        "compiler_output": original_provenance["compiler_output"],
        "lake_compiler_output": original_provenance["lake_compiler_output"],
        "preflight_provenance_sha256": sha(preflight),
        "status": "running", "modules": graph,
    }

    def save() -> None:
        temp = MANIFEST.with_suffix(".json.tmp")
        temp.write_text(json.dumps(metadata, indent=2) + "\n")
        temp.replace(MANIFEST)

    # Clear every scheduled module's artifacts, including modules that could
    # later become blocked. An old local .olean can never supply a failed input.
    for name, entry in graph.items():
        output = OUTPUT_ROOT / module_path(name, ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        for previous in output.parent.glob(output.name + "*"):
            if previous.is_file():
                previous.unlink()
        ilean = output.with_suffix(".ilean")
        if ilean.is_file():
            ilean.unlink()
        entry["output"] = output.relative_to(ROOT).as_posix()
    running: dict[str, tuple[subprocess.Popen, object, float]] = {}
    save()

    def interrupted(signum, _frame):
        raise KeyboardInterrupt(f"Received signal {signum}")

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    try:
        while True:
            progress = False
            # Complete active jobs before scheduling another, so len(running)
            # is a strict cap on simultaneously alive Lean/Lake process groups.
            for name in list(running):
                process, stream, started = running[name]
                elapsed = time.monotonic() - started
                timed_out = elapsed >= TIMEOUT_SECONDS and process.poll() is None
                if timed_out:
                    stop(process)
                returncode = process.poll()
                if returncode is None:
                    continue
                stream.close()
                entry = graph[name]
                output = ROOT / entry["output"]
                unchanged = sha(ROOT / entry["source"]) == entry["sha256"]
                passed = returncode == 0 and not timed_out and output.is_file() and unchanged
                entry.update({"status": "passed" if passed else "failed",
                              "returncode": returncode, "elapsed_seconds": round(elapsed, 3),
                              "timed_out": timed_out, "source_unchanged": unchanged})
                if passed:
                    entry["output_sha256"] = sha(output)
                else:
                    # A nonzero exit may leave an artifact. Do not keep it.
                    for partial in output.parent.glob(output.name + "*"):
                        if partial.is_file():
                            partial.unlink()
                    if timed_out:
                        entry["failure_reason"] = "TIMEOUT_1200_SECONDS"
                    elif not unchanged:
                        entry["failure_reason"] = "SOURCE_CHANGED_DURING_COMPILE"
                    elif returncode == 0:
                        entry["failure_reason"] = "MISSING_OLEAN"
                    else:
                        entry["failure_reason"] = "LEAN_NONZERO_EXIT"
                print(f"MODULE={name}; STATUS={entry['status'].upper()}; SECONDS={elapsed:.1f}; LOG={entry['log']}", flush=True)
                del running[name]
                progress = True

            # Propagate dependency failures immediately, but continue every
            # independent branch so one run captures all reachable errors.
            changed = True
            while changed:
                changed = False
                for name, entry in graph.items():
                    if entry["status"] != "pending":
                        continue
                    bad = [d for d in entry["dependencies"] if graph[d]["status"] in {"failed", "blocked"}]
                    if bad:
                        entry.update({"status": "blocked", "blocked_by": bad})
                        print(f"MODULE={name}; STATUS=BLOCKED; DEPENDENCIES={','.join(bad)}", flush=True)
                        changed = progress = True

            for name, entry in graph.items():
                if len(running) >= MAX_PROCESSES:
                    break
                if entry["status"] != "pending":
                    continue
                if not all(graph[d]["status"] == "passed" for d in entry["dependencies"]):
                    continue
                output = ROOT / entry["output"]
                source = ROOT / entry["source"]
                if sha(source) != entry["sha256"]:
                    entry.update({"status": "failed", "failure_reason": "SOURCE_CHANGED_BEFORE_COMPILE"})
                    progress = True
                    continue
                logfile = LOG_ROOT / (name + ".log")
                command = ["lake", "env", "lean", f"-j{LEAN_THREADS}", "-o",
                           entry["output"], entry["source"]]
                stream = logfile.open("wb")
                try:
                    process = subprocess.Popen(command, cwd=ROOT, stdout=stream,
                                               stderr=subprocess.STDOUT, start_new_session=True)
                except OSError:
                    stream.close()
                    raise
                running[name] = (process, stream, time.monotonic())
                entry.update({"status": "running", "command": command,
                              "log": logfile.relative_to(ROOT).as_posix()})
                print(f"MODULE={name}; STATUS=STARTED; ACTIVE={len(running)}", flush=True)
                progress = True

            if progress:
                save()
            if not running:
                pending = [n for n, e in graph.items() if e["status"] == "pending"]
                if pending:
                    raise ValueError(f"Scheduler stalled with unresolved modules: {pending}")
                break
            if not progress:
                time.sleep(0.25)
    except BaseException:
        metadata["status"] = "interrupted"
        for name, (process, stream, started) in running.items():
            stop(process)
            stream.close()
            graph[name].update({"status": "failed", "failure_reason": "COMPILATION_INTERRUPTED",
                                "elapsed_seconds": round(time.monotonic() - started, 3)})
        save()
        raise

    failures = [n for n, e in graph.items() if e["status"] != "passed"]
    metadata["status"] = "failed" if failures else "passed"
    metadata["failed_or_blocked"] = failures
    save()
    print(f"DIRECT_LEAN_DAG={'FAIL' if failures else 'PASS'}; MODULES={len(graph)}; FAILED_OR_BLOCKED={len(failures)}", flush=True)
    return 1 if failures else 0


if __name__ == "__main__":
    try:
        sys.exit(compile_graph())
    except (ValueError, OSError, KeyboardInterrupt) as error:
        print(f"DIRECT_LEAN_DAG=FAIL: {error}", file=sys.stderr)
        sys.exit(1)
