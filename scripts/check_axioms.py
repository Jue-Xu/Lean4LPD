#!/usr/bin/env python3
"""Check the output of `lake env lean Lean4LPD/Audit.lean`.

Every audited declaration must depend on no axioms beyond Lean's three standard ones.
Usage: check_axioms.py audit.log
"""
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

text = open(sys.argv[1]).read()
if re.search(r":\d+:\d+: error|^error:", text, re.M):
    sys.exit("audit file did not elaborate cleanly:\n" + text[:2000])

reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
clean = re.findall(r"'([^']+)' does not depend on any axioms", text)
bad = []
for name, axioms in reports:
    used = {a.strip() for a in axioms.replace("\n", " ").split(",") if a.strip()}
    if not used <= ALLOWED:
        bad.append((name, sorted(used - ALLOWED)))

print(f"{len(reports) + len(clean)} declarations audited "
      f"({len(clean)} axiom-free, {len(reports)} using only standard axioms)"
      if not bad else f"{len(bad)} declarations use non-standard axioms")
for name, extra in bad:
    print(f"  {name}: {extra}")
if not reports and not clean:
    sys.exit("no axiom reports found")
sys.exit(1 if bad else 0)
