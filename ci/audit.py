from pathlib import Path
import re
allowed = {"propext", "Classical.choice", "Quot.sound"}
text = "\n".join(p.read_text() for p in Path("logs").glob("*.log"))
reports = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", text, re.S)
assert reports, "No axiom reports found"
for name, raw in reports:
    axioms = {s.strip() for s in raw.split(",") if s.strip()}
    assert axioms <= allowed, (name, axioms - allowed)
assert "sorryAx" not in text
print("AXIOM_AUDIT=PASS_STANDARD_ONLY")
print("SCOPE=EXPLICIT_THEOREM_STATEMENTS_AND_PREMISES")
