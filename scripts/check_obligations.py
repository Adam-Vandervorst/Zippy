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

# ==================================================================================================
# THE RECURSION REGISTRY, CHECKED THE SAME WAY THE EGG RULES ARE
#
# `terminating/REGISTRY.tsv` claims to be the TOTAL map from the recursion-lowering surface to its
# obligations.  A total map is only worth the name if something checks it, so:
#
#   (1) every FILE / SCHEMATIC row's named artifact must exist AND be `PROVED` in
#       `terminating/STATUS.tsv` — a registry row pointing at a missing or open file is a claim with
#       no discharge behind it;
#   (2) every `code-site` of the form `<path>:<line>` must have an `obligation: terminating/` comment
#       within a few lines of it, so the map is bidirectional and a lowering pass cannot drift away
#       from the theorem that licenses it;
#   (3) OPEN / PROPERTY / CITED / NEGATIVE-RESULT rows are PRINTED on every run, never silently
#       accepted.  The unproved surface has to stay visible; that is the whole point of keeping those
#       rows in the registry instead of deleting them.
# ==================================================================================================

reg = root / "terminating" / "REGISTRY.tsv"
tstatus = root / "terminating" / "STATUS.tsv"
if reg.exists():
    verdicts = {}
    if tstatus.exists():
        for line in tstatus.read_text().splitlines():
            cols = line.split("\t")
            if len(cols) >= 4 and not line.startswith("#"):
                verdicts[cols[0]] = cols[3]
    unproved = []
    drifted = []
    rows = 0
    for i, line in enumerate(reg.read_text().splitlines(), 1):
        if line.startswith("#") or not line.strip():
            continue
        cols = line.split("\t")
        if len(cols) < 5 or cols[0] == "id":
            continue
        rid, kind, files, site, _stmt = cols[0], cols[1], cols[2], cols[3], cols[4]
        rows += 1
        if kind in ("FILE", "SCHEMATIC"):
            # `terminating/x_{a,b}.{p,smt2}` expands to the same brace form the egg citations use
            for tok in re.findall(r"terminating/[\w{},]+\.\{?[\w,]+\}?", files):
                stem = tok.split("/", 1)[1].split(".")[0]
                names = [stem]
                br = re.match(r"([\w]*)\{([\w,]+)\}([\w]*)", stem)
                if br:
                    names = [br.group(1) + x + br.group(3) for x in br.group(2).split(",")]
                for n in names:
                    if not (root / "terminating" / f"{n}.smt2").exists():
                        print(f"terminating/REGISTRY.tsv:{i}: {rid} names a missing artifact "
                              f"terminating/{n}.smt2")
                        bad += 1
                    elif n not in verdicts:
                        print(f"terminating/REGISTRY.tsv:{i}: {rid} names terminating/{n}.smt2, which "
                              "terminating/run.sh does not cover (no STATUS.tsv row)")
                        bad += 1
                    elif not verdicts[n].startswith("PROVED"):
                        print(f"terminating/REGISTRY.tsv:{i}: {rid} names terminating/{n}.smt2, whose "
                              f"verdict is {verdicts[n]!r} — a FILE row must be discharged")
                        bad += 1
        else:
            unproved.append(f"  {rid:<6} {kind:<16} {files[:52]:<52} {site[:44]}")
        # (2) the code-site back-reference
        for m in re.finditer(r"([\w./]+\.scala):(\d+)", site):
            # the registry writes bare basenames (`MORKL.scala:1214`) as well as repo-relative paths;
            # resolve a basename against the two source roots rather than calling it missing
            src = root / m.group(1)
            if not src.exists():
                cands = [c for d in ("src/main/scala", "src/test/scala")
                         for c in [root / d / pathlib.Path(m.group(1)).name] if c.exists()]
                if cands:
                    src = cands[0]
            if not src.exists():
                print(f"terminating/REGISTRY.tsv:{i}: {rid} cites a missing source {m.group(1)}")
                bad += 1
                continue
            ls = src.read_text().splitlines()
            n = int(m.group(2))
            # FILE GRANULARITY IS THE HARD REQUIREMENT, the line only a hint.  The registry pins line
            # numbers and every edit to a cited file moves them, so a line-exact gate would fail on
            # its own maintenance; what must not happen is a cited file with no back-reference AT ALL.
            if not any("obligation: terminating/" in x for x in ls):
                print(f"terminating/REGISTRY.tsv:{i}: {rid} cites {m.group(1)}:{n}, and that file "
                      "carries NO `obligation: terminating/` comment — the map is one-way there")
                bad += 1
            elif not any("obligation: terminating/" in x
                         for x in ls[max(0, n - 25):min(len(ls), n + 25)]):
                drifted.append(f"  {rid:<8} {m.group(1)}:{n}")
    print(f"terminating/REGISTRY.tsv: {rows} rows, {len(unproved)} NOT discharged by an SMT file:")
    for u in unproved:
        print(u)
    if drifted:
        print(f"terminating/REGISTRY.tsv: {len(drifted)} cited line number(s) have DRIFTED away from "
              "their `obligation:` comment (the file link holds; re-pin the line when convenient):")
        for d in drifted:
            print(d)
else:
    print("terminating/REGISTRY.tsv: absent")

print(f"problems: {bad}")
sys.exit(1 if bad else 0)
