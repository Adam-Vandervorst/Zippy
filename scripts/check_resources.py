#!/usr/bin/env python3
"""RESOURCE CERTIFICATES OF THE CORNERSTONES (tasks.md D2): every claimed resource result contains its counted run.

`proofs/pipeline/resources/<stone>.tsv` (written by EquivPipelineTest) carries, per backend, the predicted
interval of every calibrated component and the counted value of the executor's run (`B` rows), then the
derivation (`D` rows).  `proofs/pipeline/resources/<stone>-alloc.tsv` is the selection certificate of the
stone's residual alternatives under `alloc`, and `proofs/pipeline/RESOURCES.tsv` indexes them.

This script re-checks, from the files alone: every counted value lies in its interval; no interval of a
certified row is empty or inverted; every index row names an existing certificate whose selected
candidate matches, and every certificate replays (`check_selection.decide`); every CLAIMS.tsv cornerstone
has a resource file and an index row.
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import check_selection  # noqa: E402

COMPONENTS = ["work", "alloc", "rounds", "touch"]


def rows(path):
    out = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            out.append(line.split("\t"))
    return out


def ivl(s):
    s = s.strip()
    assert s.startswith("[") and s.endswith("]"), s
    lo, hi = s[1:-1].split(",")
    return int(lo), (float("inf") if hi.strip() == "inf" else int(hi))


def check(root):
    problems = []
    res_dir = os.path.join(root, "proofs", "pipeline", "resources")
    index = os.path.join(root, "proofs", "pipeline", "RESOURCES.tsv")
    claims = os.path.join(root, "proofs", "pipeline", "CLAIMS.tsv")
    if not os.path.isdir(res_dir) or not os.path.exists(index):
        return ["proofs/pipeline/resources or RESOURCES.tsv is missing"]
    stones = sorted({c[0] for c in rows(claims) if c})
    idx = {c[0]: c for c in rows(index) if c}
    checked_rows = 0
    for st in stones:
        f = os.path.join(res_dir, f"{st}.tsv")
        if not os.path.exists(f):
            problems.append(f"{st}: no resource certificate"); continue
        b_rows = [c for c in rows(f) if c[0] == "B"]
        if len(b_rows) != 4:
            problems.append(f"{st}: {len(b_rows)} backend rows, not 4")
        for c in b_rows:
            backend = c[1]
            for i, comp in enumerate(COMPONENTS):
                try:
                    lo, hi = ivl(c[2 + i])
                except Exception:
                    problems.append(f"{st}/{backend}: unreadable interval {c[2 + i]!r}"); continue
                if lo > hi:
                    problems.append(f"{st}/{backend}/{comp}: inverted interval [{lo}, {hi}]")
                cnt = c[6 + i].strip()
                if cnt != "-":
                    v = int(cnt)
                    if not (lo <= v <= hi):
                        problems.append(f"{st}/{backend}/{comp}: counted {v} outside [{lo}, {hi}]")
                    checked_rows += 1
            if c[10].strip() not in ("CERTIFIED", "UNCERTIFIED"):
                problems.append(f"{st}/{backend}: certification column is {c[10]!r}")
        if st not in idx:
            problems.append(f"{st}: no RESOURCES.tsv row"); continue
        row = idx[st]
        cert = os.path.join(root, row[7])
        if not os.path.exists(cert):
            problems.append(f"{st}: certificate {row[7]} missing"); continue
        ps = check_selection.check_file(cert)
        problems.extend(f"{st}: {p}" for p in ps)
        text = open(cert, encoding="utf-8").read()
        _, _, _, sel, _ = check_selection.parse(text)
        if sel != row[2]:
            problems.append(f"{st}: index says selected {row[2]}, certificate says {sel}")
        if row[6].startswith("OPEN"):
            problems.append(f"{st}: the selected alternative's trace closure is OPEN")
        if row[4] != "-":
            lo, hi = ivl(row[3])
            if not (lo <= int(row[4]) <= hi):
                problems.append(f"{st}: selected alloc counted {row[4]} outside {row[3]}")
    return problems, checked_rows


def main(argv):
    root = argv[1] if len(argv) > 1 else ROOT
    out = check(root)
    if isinstance(out, list):
        for p in out:
            print(f"  !! {p}")
        print(f"resources: {len(out)} problem(s)")
        return 1
    problems, n = out
    for p in problems:
        print(f"  !! {p}")
    print(f"resources: {n} counted values checked against their intervals; {len(problems)} problem(s)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
