#!/usr/bin/env python3
"""Fold proofs/pipeline/STATUS.tsv into the `pipeline/` block of proofs/STATUS.tsv.

`proofs/run.sh` does this at the end of a full corpus run — re-running every prover on ~200 files, which
is hours.  The pipeline artifacts are regenerated far more often than that (every `ZIPPY_REGENERATE=1
sbt --server 'testOnly morkl.EquivPipelineTest'` run), and each time the repo-wide table's `pipeline/`
rows go stale: rows for artifacts that no longer exist, verdicts that changed.  `scripts/proof_closure.py
--check` reports exactly that ("a status is reported for a file that does not exist").

This script applies run.sh's own rule without the prover runs: a marker file (TRIVIAL / LAW-JUSTIFIED /
IDENTICAL-STRUCTURE / SINGLE-SIDE / PROVER-BUDGET-EXCEEDED) is recorded as its marker; a goal file takes
the per-prover columns the test recorded in proofs/pipeline/STATUS.tsv.  The block is replaced IN PLACE
(same position in the table), nothing else is touched, and `proof_closure.py --annotate` should run
afterwards as run.sh does.
"""
import pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
REPO = ROOT / "proofs" / "STATUS.tsv"
PIPE = ROOT / "proofs" / "pipeline" / "STATUS.tsv"
PIPE_DIR = ROOT / "proofs" / "pipeline"
MARKERS = ["TRIVIAL-NO-OBLIGATION", "LAW-JUSTIFIED-NO-RESIDUAL", "IDENTICAL-STRUCTURE-NO-EQUIVALENCE-OBLIGATION",
           "SINGLE-SIDE-OBSERVATION", "PROVER-BUDGET-EXCEEDED"]

def main():
    pipe = {}
    for line in PIPE.read_text().splitlines():
        if not line.strip(): continue
        name, z3, vp, verdict = line.split("\t")
        pipe[name.removesuffix(".smt2")] = (z3, vp, verdict)
    rows = []
    for path in sorted(PIPE_DIR.glob("*.smt2")):
        f = path.stem
        text = path.read_text()
        marker = next((m for m in MARKERS if m in text), None)
        if marker:
            rows.append(f"pipeline/{f}\t-\t-\t{marker}")
        else:
            z3, vp, verdict = pipe.get(f, ("-", "-", "OPEN (NEW — unexpected)"))
            # run.sh records PROVED when either prover discharged the goal; keep the qualified
            # verdict the emitter wrote (Certified.qualify) so nothing is upgraded here
            rows.append(f"pipeline/{f}\t{z3}\t{vp}\t{verdict}")
    lines = REPO.read_text().rstrip("\n").split("\n")
    idx = [i for i, l in enumerate(lines) if l.startswith("pipeline/")]
    if idx:
        first, last = idx[0], idx[-1]
        lines = lines[:first] + rows + lines[last + 1:]
    else:
        lines += rows
    REPO.write_text("\n".join(lines) + "\n")
    print(f"folded {len(rows)} pipeline row(s) into {REPO.relative_to(ROOT)}")

if __name__ == "__main__":
    main()
