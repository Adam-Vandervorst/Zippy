#!/usr/bin/env python3
"""Every egglog rule in zipper-spec.egg (the certified movement spec), zipper.egg (the illustrative
zipper extension), zipper-impl.egg and formal.egg must carry an obligation
annotation on its (first) line:
   ; proof: proofs/<file>.smt2 [...]   — a universal certificate, or
   ; definitional (...)                — true by definition (no equation content), or
   ; demand-materialisation (...)      — a demand rule creating a term, asserting nothing.
The mapping must be TOTAL: an unannotated rule fails CI.

Cited certificates are checked against proofs/STATUS.tsv (written by proofs/run.sh — the
machine-readable prover verdicts), so an admitted-unproved (OPEN) or refuted (COUNTERMODEL)
obligation is visible here, not just in a comment nobody parses:
  - a cited file with verdict COUNTERMODEL always fails;
  - a cited file with verdict OPEN fails unless the rule's annotation itself acknowledges it
    with the token OPEN (e.g. `; proof: proofs/refine_cli.smt2 (OPEN: differential-covered)`),
    in which case it is counted separately as open-acknowledged;
  - a cited file absent from STATUS.tsv fails (it is not covered by proofs/run.sh)."""
import re, sys, pathlib
root = pathlib.Path(__file__).resolve().parent.parent

status = {}
status_file = root / "proofs" / "STATUS.tsv"
if status_file.exists():
    for line in status_file.read_text().splitlines():
        parts = line.split("\t")
        if len(parts) == 4:
            status[parts[0]] = parts[3]
else:
    print("proofs/STATUS.tsv missing — run proofs/run.sh to generate the prover verdicts")
    sys.exit(1)

bad = 0
totals = {}
for egg in ("zipper-spec.egg", "zipper.egg", "zipper-impl.egg", "formal.egg"):
    proofs = defs = open_acked = 0
    for i, l in enumerate((root / egg).read_text().splitlines(), 1):
        ls = l.strip()
        if not (ls.startswith("(rewrite") or ls.startswith("(rule ") or ls.startswith("(rule(")
                or ls == "(rule" or ls.startswith("(rule\n")):
            continue
        if "; proof:" in l:
            proofs += 1
            for m in re.findall(r"proofs/([\w{},/]+)\.smt2", l):
                br = re.match(r"([\w/]*)\{([\w,]+)\}", m)
                names = [br.group(1) + x for x in br.group(2).split(",")] if br else [m]
                for n in names:
                    if not (root / "proofs" / f"{n}.smt2").exists():
                        print(f"{egg}:{i}: missing obligation file proofs/{n}.smt2"); bad += 1
                        continue
                    verdict = status.get(n)
                    if verdict is None:
                        print(f"{egg}:{i}: proofs/{n}.smt2 not covered by proofs/run.sh "
                              "(no STATUS.tsv entry)"); bad += 1
                    elif verdict.startswith("COUNTERMODEL"):
                        print(f"{egg}:{i}: proofs/{n}.smt2 has a COUNTERMODEL — the cited "
                              "theorem is false"); bad += 1
                    elif verdict.startswith("OPEN"):
                        if "OPEN" in l.split("; proof:")[1]:
                            open_acked += 1
                        else:
                            print(f"{egg}:{i}: proofs/{n}.smt2 is OPEN (admitted-unproved) but "
                                  "the rule annotation does not acknowledge it"); bad += 1
        elif "; definitional" in l or "; demand-materialisation" in l:
            defs += 1
        else:
            print(f"{egg}:{i}: UNANNOTATED rule: {ls[:70]}"); bad += 1
    totals[egg] = (proofs, defs, open_acked)

for egg, (proofs, defs, open_acked) in totals.items():
    print(f"{egg}: {proofs} proof-backed ({open_acked} open-acknowledged), "
          f"{defs} definitional/demand")
print(f"problems: {bad}")
sys.exit(1 if bad else 0)
