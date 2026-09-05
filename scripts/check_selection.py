#!/usr/bin/env python3
"""INDEPENDENT REPLAY OF SELECTION CERTIFICATES (tasks.md B2).

A selection certificate (`morkl.Pareto.Selection.render`) lists every candidate (alternative x backend)
with its interval per component, the objective, and the decision: rejections (NOT-ADMITTED, INFEASIBLE,
UNPROVEN, DOMINATED), the selected candidate, the kept incomparable survivors.  This script re-derives
the decision from the C rows and the header ALONE — no Scala, no shared code — and fails on any
difference.  A removal the certificate cannot justify by its own numbers is an error.

    python3 scripts/check_selection.py [files or directories...]     (default: proofs/decisions)
"""
import os, sys

INF = float("inf")
COMPONENTS = ["work", "alloc", "rounds", "touch"]
BACKENDS = ["reference", "trie", "graph", "zipper"]


def num(s):
    return INF if s == "inf" else int(s)


def fmt(x):
    return "inf" if x == INF else str(int(x))


def parse(text):
    hdr, cands, xs, sel, ks = {}, [], [], None, []
    for line in text.splitlines():
        if not line.strip():
            continue
        cols = line.split("\t")
        if line.startswith("# ") and len(cols) >= 2:
            hdr[cols[0][2:]] = cols[1]
            continue
        tag = cols[0]
        if tag == "C":
            b = {}
            for i, c in enumerate(COMPONENTS):
                b[c] = (num(cols[3 + 2 * i]), num(cols[4 + 2 * i]))
            cands.append({"alt": cols[1], "backend": cols[2], "b": b, "certified": cols[11] == "CERTIFIED", "closure": cols[12]})
        elif tag == "X":
            xs.append(line)
        elif tag == "S":
            sel = f"{cols[1]}/{cols[2]}"
        elif tag == "K":
            ks.append(line)
    return hdr, cands, xs, sel, ks


def key(c):
    return (c["alt"], BACKENDS.index(c["backend"]))


def ckey(c):
    return f"{c['alt']}/{c['backend']}"


def decide(hdr, cands):
    priority = hdr["priority"].split(",")
    dom = hdr["dominance"].split(",")
    cons = [] if hdr["constraints"] == "-" else [(k.split("<=")[0], int(k.split("<=")[1])) for k in hdr["constraints"].split(",")]
    cands = sorted(cands, key=key)
    rejected = []
    admitted = []
    for c in cands:
        ok = c["certified"] and not c["closure"].startswith("OPEN")
        if ok:
            admitted.append(c)
        else:
            why = []
            if not c["certified"]:
                why.append("spatial derivation not certified (an A6 rule is OPEN or the status table is absent)")
            if c["closure"].startswith("OPEN"):
                why.append("trace closure OPEN: " + c["closure"][5:])
            rejected.append((c, "NOT-ADMITTED", "; ".join(why)))
    feasible = []
    for c in admitted:
        r = None
        for comp, cap in cons:
            lo, hi = c["b"][comp]
            if lo > cap:
                r = ("INFEASIBLE", f"{comp} lo={fmt(lo)} > cap={cap}")
                break
            if hi > cap:
                r = ("UNPROVEN", f"{comp} hi={fmt(hi)} > cap={cap}")
                break
        if r:
            rejected.append((c, r[0], r[1]))
        else:
            feasible.append(c)

    def unknown(c):
        return {"touch"} if c["backend"] == "reference" else set()

    def dominates(x, y):
        if ckey(x) == ckey(y):
            return None
        comps = [comp for comp in dom if not (comp in unknown(x) and comp in unknown(y))]
        ev = [(comp, x["b"][comp][1], y["b"][comp][0]) for comp in comps]
        if all(xhi != INF and xhi <= ylo for _, xhi, ylo in ev) and any(xhi < ylo for _, xhi, ylo in ev):
            return ev
        return None

    survivors = []
    for y in feasible:
        winner = None
        for x in feasible:
            ev = dominates(x, y)
            if ev is not None:
                winner = (x, ev)
                break
        if winner:
            x, ev = winner
            rejected.append((y, "DOMINATED", f"by {ckey(x)}: " + " ".join(f"{comp} {fmt(a)}<={fmt(b)}" for comp, a, b in ev)))
        else:
            survivors.append(y)

    def rank(c):
        return ([v for comp in priority for v in (c["b"][comp][1], c["b"][comp][0])], c["alt"], BACKENDS.index(c["backend"]))

    ranked = sorted(survivors, key=rank)
    selected = ranked[0] if ranked else None
    kept = []
    for c in ranked[1:]:
        ov = [comp for comp in dom if not (selected["b"][comp][1] < c["b"][comp][0] or c["b"][comp][1] < selected["b"][comp][0])]
        kept.append((c, ov))
    rejected.sort(key=lambda t: key(t[0]))
    xs = [f"X\t{c['alt']}\t{c['backend']}\t{k}\t{d}" for c, k, d in rejected]
    ks = [f"K\t{c['alt']}\t{c['backend']}\tINCOMPARABLE with the selected: overlaps on {','.join(ov)}" for c, ov in sorted(kept, key=lambda t: key(t[0]))]
    return xs, (ckey(selected) if selected else None), ks


def check_file(path):
    text = open(path, encoding="utf-8").read()
    hdr, cands, xs, sel, ks = parse(text)
    problems = []
    for k in ("objective", "priority", "dominance", "constraints", "backends"):
        if k not in hdr:
            problems.append(f"header lacks `{k}`")
    if problems:
        return problems
    if not cands:
        return ["no candidate rows"]
    rx, rsel, rk = decide(hdr, cands)
    if rx != xs:
        problems.append("rejections differ from what the rows imply:\n    certificate: " + " | ".join(xs) + "\n    replay:      " + " | ".join(rx))
    if rsel != sel:
        problems.append(f"selected differs: certificate {sel}, replay {rsel}")
    if rk != ks:
        problems.append("kept rows differ:\n    certificate: " + " | ".join(ks) + "\n    replay:      " + " | ".join(rk))
    # every candidate is accounted for exactly once
    keys = sorted(ckey(c) for c in cands)
    acc = sorted([x.split("\t")[1] + "/" + x.split("\t")[2] for x in xs] + ([sel] if sel else []) + [k.split("\t")[1] + "/" + k.split("\t")[2] for k in ks])
    if keys != acc:
        problems.append(f"candidates {keys} are not partitioned by the decision rows {acc}")
    return problems


def main(argv):
    targets = argv[1:] or ["proofs/decisions"]
    files = []

    def is_certificate(path):
        with open(path, encoding="utf-8") as f:
            return f.readline().startswith("# SELECTION CERTIFICATE")

    for t in targets:
        if os.path.isdir(t):
            # a directory holds frontiers and indexes beside the certificates: only the certificates are replayed
            files += sorted(os.path.join(t, f) for f in os.listdir(t)
                            if f.endswith(".tsv") and not f.startswith(".") and is_certificate(os.path.join(t, f)))
        else:
            files.append(t)
    total = 0
    for f in files:
        ps = check_file(f)
        status = "OK" if not ps else "FAIL"
        print(f"  {status:4s} {f}")
        for p in ps:
            print(f"    !! {p}")
        total += len(ps)
    print(f"selection certificates: {len(files)} file(s), {total} problem(s)")
    return 1 if total or not files else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
