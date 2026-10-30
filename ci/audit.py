#!/usr/bin/env python3
"""Fail-closed source, provenance, and independent Lean axiom audit.

This script performs no Lean execution. build.sh invokes Lean and then supplies
its independent output. Passing this audit certifies the displayed theorem
statements and their explicit premises; it does not discharge those premises.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.33.0"
EXPECTED_MATHLIB = "db584cd6d46c92f209a44c0f1c829460d327499d"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ROOT = Path(__file__).resolve().parent.parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()


def expected(path: Path) -> list[str]:
    names = path.read_text(encoding="utf-8").splitlines()
    require(bool(names), f"Empty expected-name file: {path}")
    require(all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", n) for n in names),
            f"Malformed expected name in {path}")
    require(len(names) == len(set(names)), f"Duplicate expected names in {path}")
    return names


def lean_code(text: str) -> str:
    """Remove nested Lean comments and strings, retaining code token spacing."""
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif text.startswith("--", i):
            newline = text.find("\n", i)
            i = len(text) if newline < 0 else newline
            out.append(" ")
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError("Unterminated Lean string")
        else:
            out.append(text[i])
            i += 1
    require(depth == 0, "Unterminated Lean comment")
    return "".join(out)


def source_state() -> dict:
    require((ROOT / "lean-toolchain").read_text().strip() == EXPECTED_TOOLCHAIN,
            "Unexpected lean-toolchain")
    lakefile = (ROOT / "lakefile.toml").read_text()
    require(EXPECTED_MATHLIB in lakefile, "Pinned Mathlib revision missing from lakefile.toml")
    require(git("rev-parse", "HEAD", cwd=ROOT / ".lake/packages/mathlib") == EXPECTED_MATHLIB,
            "Checked-out Mathlib revision does not match the pin")
    version = (ROOT / "logs/version.log").read_text()
    lake_version = (ROOT / "logs/lake-lean-version.log").read_text()
    for output in (version, lake_version):
        require(bool(re.search(r"Lean \(version 4\.33\.0(?:,|\))", output)),
                "Compiler version is not exactly Lean 4.33.0")

    files = sorted((ROOT / "ZetaBetaHankel").rglob("*.lean"))
    if (ROOT / "ZetaBetaHankel.lean").exists():
        files.append(ROOT / "ZetaBetaHankel.lean")
    require(bool(files), "No Lean sources found")
    tracked = set(git("ls-files").splitlines())
    relevant = files + [ROOT / "lean-toolchain", ROOT / "lakefile.toml"]
    relevant += sorted((ROOT / "ci").glob("*"))
    relevant = [p for p in relevant if p.is_file()]
    for path in relevant:
        rel = path.relative_to(ROOT).as_posix()
        require(rel in tracked, f"Untracked audited file: {rel}")
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--", "ZetaBetaHankel",
                    "ZetaBetaHankel.lean", "lean-toolchain", "lakefile.toml", "ci"],
                   cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    for path in files:
        code = lean_code(path.read_text(encoding="utf-8"))
        prohibited = re.findall(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code)
        require(not prohibited, f"Prohibited source token in {path.relative_to(ROOT)}: {prohibited[:3]}")
    return {
        "commit": git("rev-parse", "HEAD"),
        "mathlib_commit": EXPECTED_MATHLIB,
        "toolchain": EXPECTED_TOOLCHAIN,
        "compiler_output": version.strip(),
        "lake_compiler_output": lake_version.strip(),
        "files": {p.relative_to(ROOT).as_posix(): {"bytes": p.stat().st_size, "sha256": sha(p)}
                  for p in relevant},
        "lean_source_count": len(files),
        "source_check": "NO_SORRY_ADMIT_AXIOM_UNSAFE_NATIVE_DECIDE",
        "scope": "THEOREM_STATEMENTS_WITH_EXPLICIT_PREMISES",
    }


def validate_log(log: str, axiom_names: list[str], type_names: list[str]) -> dict:
    require("\x1b" not in log, "Unexpected terminal escape sequence in independent audit")
    require("sorryAx" not in log, "sorryAx found in independent audit")
    require(not re.search(r"(?:^|\n).*\b(?:error|panic|PANIC)\b", log),
            "Compiler error or panic found in independent audit")
    # pp.width is fixed to 100000; accepting wrapped reports would make accidental
    # truncation ambiguous. Each report must therefore occupy exactly one line.
    report_re = re.compile(
        r"^'(?P<name>[^'\r\n]+)' (?:(?:depends on axioms: \[(?P<axioms>[^\]\r\n]*)\])|"
        r"(?P<none>does not depend on any axioms))\r?$", re.M)
    matches = list(report_re.finditer(log))
    counts = Counter(m.group("name") for m in matches)
    require(set(counts) == set(axiom_names),
            f"Axiom report set mismatch; missing={sorted(set(axiom_names)-set(counts))}; "
            f"unexpected={sorted(set(counts)-set(axiom_names))}")
    require(all(n == 1 for n in counts.values()),
            f"Duplicate axiom reports: {[name for name, n in counts.items() if n != 1]}")
    report_like = [line for line in log.splitlines()
                   if "depends on axioms:" in line or "does not depend on any axioms" in line]
    require(len(report_like) == len(matches), "Malformed, wrapped, or unparsed axiom report")
    parsed: dict[str, list[str]] = {}
    for match in matches:
        raw = match.group("axioms")
        axioms = [] if raw is None or not raw.strip() else [s.strip() for s in raw.split(",")]
        require(all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", a) for a in axioms),
                f"Malformed axiom list for {match.group('name')}")
        require(len(axioms) == len(set(axioms)), f"Duplicate axiom for {match.group('name')}")
        require(set(axioms) <= ALLOWED_AXIOMS,
                f"Nonstandard axioms for {match.group('name')}: {sorted(set(axioms)-ALLOWED_AXIOMS)}")
        parsed[match.group("name")] = axioms
    for name in type_names:
        # Fully qualified #check @ output can include universe parameters and
        # either an explicit @ or no @. The type follows on this or later lines.
        pattern = r"^@?" + re.escape(name) + r"(?:\.\{[^}\r\n]*\})?(?=\s|:)"
        require(len(re.findall(pattern, log, re.M)) == 1,
                f"Missing or duplicate fully qualified #check output for {name}")
    return {"axiom_report_count": len(matches), "type_report_count": len(type_names),
            "axioms": parsed, "audit": "PASS_STANDARD_ONLY",
            "scope": "THEOREM_STATEMENTS_WITH_EXPLICIT_PREMISES"}


def self_test() -> None:
    names = ["Example.first", "Example.second"]
    good = "Example.first : True\n@Example.second : True\n'Example.first' depends on axioms: [propext]\n'Example.second' does not depend on any axioms\n"
    validate_log(good, names, names)
    bad = [good.replace("[propext]", "[sorryAx]"),
           good.replace("[propext]", "[Example.trust]"),
           good.replace("[propext]", "[propext,\nClassical.choice]"),
           good + "'Example.first' depends on axioms: [propext]\n",
           good.replace("'Example.second' does not depend on any axioms\n", ""),
           good.replace("Example.first : True\n", ""),
           good + "'Example.third' depends on axioms: []\n",
           good + "error: unsolved goals\n"]
    for i, text in enumerate(bad):
        try:
            validate_log(text, names, names)
        except ValueError:
            continue
        raise ValueError(f"Negative audit self-test {i} was accepted")
    require(lean_code('/- axiom /- sorry -/ admit -/ theorem ok : True := by trivial -- unsafe\n')
            .strip() == "theorem ok : True := by trivial", "Comment lexer self-test failed")
    print("AUDITOR_SELF_TEST=PASS")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preflight", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    axiom_names = expected(ROOT / "ci/expected-axioms.txt")
    type_names = expected(ROOT / "ci/expected-types.txt")
    audit_source = (ROOT / "ZetaBetaHankel/EvidenceAudit.lean").read_text()
    require(re.findall(r"^#print axioms (\S+)\s*$", audit_source, re.M) == axiom_names,
            "EvidenceAudit #print declarations differ from expected names/order")
    require(re.findall(r"^#check @(\S+)\s*$", audit_source, re.M) == type_names,
            "EvidenceAudit #check declarations differ from expected names/order")
    state = source_state()
    provenance = ROOT / "logs/provenance.json"
    if args.preflight:
        provenance.write_text(json.dumps(state, indent=2) + "\n")
        print(f"SOURCE_VALIDATION=PASS; LEAN_SOURCES={state['lean_source_count']}; COMMIT={state['commit']}")
        return
    require(provenance.exists(), "Preflight provenance is missing")
    require(json.loads(provenance.read_text()) == state, "Audited sources or toolchain changed after preflight")
    logfile = ROOT / "logs/final-audit.log"
    result = validate_log(logfile.read_text(encoding="utf-8"), axiom_names, type_names)
    result.update({"commit": state["commit"], "mathlib_commit": EXPECTED_MATHLIB,
                   "audit_log_sha256": sha(logfile), "provenance_sha256": sha(provenance)})
    (ROOT / "logs/audit-result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"AXIOM_AUDIT=PASS_STANDARD_ONLY; EXACT_REPORTS={result['axiom_report_count']}")
    print(f"EXPLICIT_TYPES=PASS; EXACT_REPORTS={result['type_report_count']}")
    print("SCOPE=THEOREM_STATEMENTS_WITH_EXPLICIT_PREMISES")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f"AUDIT=FAIL: {error}", file=sys.stderr)
        sys.exit(1)
