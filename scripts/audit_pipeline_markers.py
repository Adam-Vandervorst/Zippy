#!/usr/bin/env python3
"""CI marker audit for the equivalence pipeline artifacts.

Classifies every file under zipper-egg-tests/pipeline/ and proofs/pipeline/ as exactly one of
  REAL            — carries actual checks/goals (egg `(check …)`; smt `(assert (not …))` goal)
  TRIVIAL         — explicit TRIVIAL-NO-OBLIGATION marker (identical sides; nothing to prove)
  IDENT           — IDENTICAL-LITERAL marker: both sides materialised to byte-equal terms, no
                    equivalence obligation exists; requires the -virtual.egg machinery twin
  LAW-JUSTIFIED   — proof-carrying: all differing pairs are verified certified-law instances
  BUDGET          — explicit BUDGET-EXCEEDED marker (equivalence carried by named certificates)
and FAILS (exit 1) if any file is unclassifiable, contains a fake reflexive goal
`(assert (not true))`, claims to be real without any check/goal in it, or binds byte-identical
large terms under two let names in a REAL egg file (a vacuous hash-consing "equivalence").
"""
import pathlib, re, sys

root = pathlib.Path(__file__).resolve().parent.parent
dirs = [root / "zipper-egg-tests" / "pipeline", root / "proofs" / "pipeline"]

counts = {"REAL": 0, "TRIVIAL": 0, "LAW-JUSTIFIED": 0, "BUDGET": 0, "IDENT": 0}
problems = []
rows = []


def duplicate_big_lets(text):
    """Two DIFFERENT let names bound to byte-identical large RHS text: the signature of a vacuous
    'equivalence' between hash-cons-equal constructor terms (e.g. a pre-materialised zipper side
    vs the reference literal).  Such files must carry the IDENTICAL-LITERAL marker instead."""
    seen = {}
    for m in re.finditer(r"^\(let (\$\w+) (.+)\)\s*$", text, re.M):
        name, rhs = m.group(1), m.group(2)
        if len(rhs) < 80:
            continue
        if rhs in seen and seen[rhs] != name:
            return (seen[rhs], name)
        seen[rhs] = name
    return None


for d in dirs:
    for f in sorted(d.glob("*")):
        if f.suffix not in (".egg", ".smt2"):
            continue
        text = f.read_text()
        if "(assert (not true))" in text:
            problems.append(f"{f.relative_to(root)}: FAKE reflexive goal `(assert (not true))`")
        if "TRIVIAL-NO-OBLIGATION" in text:
            kind = "TRIVIAL"
        elif "IDENTICAL-LITERAL-NO-EQUIVALENCE-OBLIGATION" in text:
            kind = "IDENT"
            # the equivalence content must live somewhere: -zipper files defer to the virtual
            # (Iter/BodyK) twin, -space files to the data-agnostic optimiser comparison.
            if f.name.endswith("-zipper.egg"):
                twin = f.with_name(f.name.replace("-zipper.egg", "-zipper-virtual.egg"))
            elif f.name.endswith("-space.egg"):
                twin = f.with_name(f.name.replace("-space.egg", "-space-agnostic.egg"))
            else:
                twin = None
            if twin is not None and not twin.exists():
                problems.append(f"{f.relative_to(root)}: IDENTICAL-LITERAL but no {twin.name} twin "
                                "carrying the actual equivalence certificate")
        elif "LAW-JUSTIFIED" in text and "BUDGET-EXCEEDED" not in text and (
                "LAW-JUSTIFIED-NO-RESIDUAL" in text or "LAW-JUSTIFIED:" in text):
            kind = "LAW-JUSTIFIED"
        elif "BUDGET-EXCEEDED" in text:
            kind = "BUDGET"
        else:
            kind = "REAL"
            has_goal = ("(check" in text) if f.suffix == ".egg" else bool(
                re.search(r"\(assert \(not ", text))
            if not has_goal:
                problems.append(f"{f.relative_to(root)}: claims REAL but contains no check/goal")
            if f.suffix == ".egg":
                dup = duplicate_big_lets(text)
                if dup:
                    problems.append(f"{f.relative_to(root)}: lets {dup[0]} and {dup[1]} bind "
                                    "byte-identical large terms — a vacuous hash-consing "
                                    "'equivalence'; needs the IDENTICAL-LITERAL marker or a real "
                                    "structural side")
        counts[kind] += 1
        rows.append((str(f.relative_to(root)), kind))

width = max((len(r[0]) for r in rows), default=0)
for path, kind in rows:
    print(f"{path:<{width}}  {kind}")
print()
print("  ".join(f"{k}={v}" for k, v in counts.items()), f" total={sum(counts.values())}")

if problems:
    print("\nPROBLEMS:")
    for p in problems:
        print(f"  {p}")
    sys.exit(1)
print("\nmarker audit: OK")
