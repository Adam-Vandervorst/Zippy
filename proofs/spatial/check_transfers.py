#!/usr/bin/env python3
"""THE INDEPENDENT CHECKER OF THE EXACT-TIER TRANSFERS AND OF THE PRICING'S CONTAINMENT (tasks.md A6).

`morkl.SpatialTransferDump` writes two tables under proofs/spatial/out/:

  transfers.tsv   one row per (operation, abstract inputs) over the WHOLE small universe — paths over
                  {a, b} of length <= 2, at most three per value (64 values, 4096 pairs) — with the
                  abstract result the A3 domain (`SpatialDomain.scala`) computed, concretised;
  bounds.tsv      one row per (operation, backend, inputs, component) with the COUNTED executor total
                  and the A4 interval (`SpatialCostSemantics.scala`).

This script re-derives every concrete result with ITS OWN path-set algebra (Python sets of tuples; a
restriction is a prefix filter, a composition a concatenation, a range a slice of the canonical
string order with `normalize` transcribed from MORKL.scala) and requires the domain's exact-tier
result to EQUAL it — the exact tier is exact, gamma of the result is the singleton of the concrete
result (`docs/SPATIAL_DOMAIN.md` section 3).  It then re-checks every containment row: lo <= counted
<= hi, with `inf` above everything.  It also checks COVERAGE: every pair of universe values appears
for every binary operation, every value for every unary one, so the finite model is enumerated
exhaustively (the principle is `proofs/lean/Zippy/Spatial.lean#Zippy.Spatial.exhaustive`).

WHAT THIS DOES NOT SHOW, said plainly (see README.md): the pricing rows re-check the arithmetic of
containment on the Scala numbers; the counted totals come from the instrumented executors, which are
the semantics (A1's `SpatialSemanticsCheck` is the differential check of the event semantics against
them).  The universe is small; the argument that a structurally recursive transfer correct on every
one-level configuration is correct on every trie is written in README.md.

Output: proofs/spatial/STATUS.tsv — one row per registry entry (proofs/spatial/REGISTRY.tsv) with the
verdict PROVED (mechanized in Lean or checked here), CHECKED-PREMISE (a runtime-checked property),
or OPEN.  `scripts/proof_closure.py --check` refuses an OPEN row: no cost result is certified while a
transfer it depends on is open.
"""
import pathlib, sys, re

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
OUT = HERE / "out"

def parse_value(s):
    s = s.strip()
    if s == "{}":
        return frozenset()
    assert s.startswith("{") and s.endswith("}"), s
    body = s[1:-1].strip()
    if not body:
        return frozenset()
    out = set()
    for tok in body.split(" "):
        if tok == "ε":
            out.add(())
        else:
            out.add(tuple(tok.split(".")))
    return frozenset(out)

def show(v):
    if not v:
        return "{}"
    return "{" + " ".join(sorted(("ε" if not p else ".".join(p)) for p in v)) + "}"

# ---- the independent algebra ------------------------------------------------------------------------
def union(a, b): return a | b
def inter(a, b): return a & b
def sub(a, b): return a - b
def startswith(x, q): return len(q) <= len(x) and x[:len(q)] == q
def restrict(a, b): return frozenset(x for x in a if any(startswith(x, q) for q in b))
def raff(a, b): return frozenset(x for x in a if not any(startswith(x, q) for q in b))
def comp(a, b): return frozenset(x + y for x in a for y in b)
def tails_union(a): return frozenset(x[1:] for x in a if len(x) >= 1)
def tails_inter(a):
    heads = {x[0] for x in a if len(x) >= 1}
    if not heads:
        return frozenset()
    groups = [frozenset(x[1:] for x in a if len(x) >= 1 and x[0] == h) for h in heads]
    out = groups[0]
    for g in groups[1:]:
        out = out & g
    return out
def wrap(a, w): return frozenset((w,) + x for x in a)
def unwrap(a, w): return frozenset(x[1:] for x in a if len(x) >= 1 and x[0] == w)

def normalize(size, start, end):
    """RangeBounds.normalize (MORKL.scala:233), transcribed"""
    def lower(b):
        return 0 if b == 0 else (b - 1 if b > 0 else size + b)
    def upper(b):
        if b == 0: return size
        if start == 0 and b > 0: return b
        if b > 0: return b - 1
        return size + b
    lo = min(max(lower(start), 0), size)
    hi = min(max(upper(end), 0), size)
    return (0, 0) if hi <= lo else (lo, hi)

def path_key(p):
    # pathValueOrdering: lexicographic on items, a prefix before its extensions (epsilon first)
    return p

def rng(a, lo, hi):
    lo2, hi2 = normalize(len(a), lo, hi)
    if hi2 <= lo2:
        return frozenset()
    ordered = sorted(a, key=path_key)
    return frozenset(ordered[lo2:hi2])

BINARY = {"union": union, "inter": inter, "sub": sub, "restrict": restrict, "raff": raff, "comp": comp}
SAME = {"union-same": union, "inter-same": inter, "sub-same": sub}

def universe():
    alpha = ["a", "b"]
    paths = [()] + [(x,) for x in alpha] + [(x, y) for x in alpha for y in alpha]
    import itertools
    vals = set()
    for k in range(0, 4):
        for c in itertools.combinations(paths, k):
            vals.add(frozenset(c))
    return vals

def check_transfers(problems):
    f = OUT / "transfers.tsv"
    if not f.is_file():
        problems.append("transfers.tsv is missing: run `sbt \"testOnly morkl.SpatialTransferDump\"` first")
        return {}
    rows = [l.split("\t") for l in f.read_text().splitlines() if l.strip() and not l.startswith("#")]
    U = universe()
    seen = {}
    counts = {}
    for op, l, r, res in rows:
        a = parse_value(l)
        got = parse_value(res.split("|")[0]) if "|" not in res else None
        if got is None:
            problems.append(f"{op} {l} {r}: the exact tier returned {res.count('|') + 1} alternatives, not one value")
            continue
        if op in BINARY:
            want = BINARY[op](a, parse_value(r))
            seen.setdefault(op, set()).add((a, parse_value(r)))
        elif op in SAME:
            want = SAME[op](a, a)
            seen.setdefault(op, set()).add(a)
        elif op == "tails-union": want = tails_union(a); seen.setdefault(op, set()).add(a)
        elif op == "tails-inter": want = tails_inter(a); seen.setdefault(op, set()).add(a)
        elif op == "wrap": want = wrap(a, r); seen.setdefault(op, set()).add(a)
        elif op == "unwrap": want = unwrap(a, r); seen.setdefault(op, set()).add(a)
        elif op == "range":
            lo, hi = (int(x) for x in r.split(","))
            want = rng(a, lo, hi); seen.setdefault(op, set()).add((a, lo, hi))
        else:
            problems.append(f"unknown operation {op}"); continue
        counts[op] = counts.get(op, 0) + 1
        if want != got:
            problems.append(f"{op} {l} {r}: domain says {show(got)}, the independent algebra says {show(want)}")
    # coverage: the whole universe, every operation
    for op in BINARY:
        pairs = seen.get(op, set())
        if len(pairs) != len(U) * len(U):
            problems.append(f"{op}: {len(pairs)} of {len(U) * len(U)} universe pairs covered")
    for op in ("tails-union", "tails-inter", "wrap", "unwrap", "union-same", "inter-same", "sub-same"):
        if len(seen.get(op, set())) != len(U):
            problems.append(f"{op}: {len(seen.get(op, set()))} of {len(U)} universe values covered")
    windows = {(lo, hi) for (_, lo, hi) in seen.get("range", set())}
    if len(seen.get("range", set())) != len(U) * len(windows) or len(windows) < 8:
        problems.append(f"range: {len(seen.get('range', set()))} rows over {len(windows)} windows")
    return counts

def check_bounds(problems):
    f = OUT / "bounds.tsv"
    if not f.is_file():
        problems.append("bounds.tsv is missing: run `sbt \"testOnly morkl.SpatialTransferDump\"` first")
        return 0, 0
    n = 0; bad = 0
    for l in f.read_text().splitlines():
        if not l.strip() or l.startswith("#"): continue
        op, backend, lhs, rhs, comp, counted, lo, hi = l.split("\t")
        n += 1
        c = int(counted); lo = int(lo); hi = float("inf") if hi == "inf" else int(hi)
        if not (lo <= c <= hi):
            bad += 1
            if bad <= 10:
                problems.append(f"bounds {op}/{backend} {lhs} {rhs} {comp}: counted {c} not in [{lo}, {hi}]")
        if hi == float("inf"):
            bad += 1
            problems.append(f"bounds {op}/{backend} {lhs} {rhs} {comp}: an INFINITE upper endpoint on a closed exact program")
    return n, bad

def lean_theorems():
    """the theorems Spatial.lean declares (a build is `scripts/check_lean.sh`'s job; this checks the names the registry cites exist)"""
    src = (ROOT / "proofs/lean/Zippy/Spatial.lean").read_text()
    names = set()
    ns = []
    for line in src.splitlines():
        m = re.match(r"^namespace (\w+)", line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r"^end (\w+)", line)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = re.match(r"^theorem (\w+)", line)
        if m: names.add(".".join(ns + [m.group(1)]))
    return names

def main():
    problems = []
    counts = check_transfers(problems)
    n, bad = check_bounds(problems)
    thms = lean_theorems()
    reg = ROOT / "proofs/spatial/REGISTRY.tsv"
    status_rows = []
    for line in reg.read_text().splitlines():
        if not line.strip() or line.startswith("#"): continue
        rid, kind, witness, site, stmt = line.split("\t")[:5]
        if kind.startswith("MECHANIZED"):
            missing = [w for w in witness.split(",") if w.strip().split("#")[1] not in thms]
            verdict = "PROVED" if not missing and not problems else ("OPEN" if missing else "PROVED")
            if missing:
                problems.append(f"{rid}: cites Lean theorem(s) that do not exist: {missing}")
                verdict = "OPEN"
            status_rows.append((rid, "lean", "-", verdict))
        elif kind.startswith("CHECKED"):
            ok = not any(p.startswith(rid.split("-", 2)[-1].lower()) for p in problems) and counts.get(rid.split("A6-EXACT-")[-1].lower(), 0) > 0 if rid.startswith("A6-EXACT-") else True
            failed = [p for p in problems if p.startswith("bounds")] if rid == "A6-PRICING" else [p for p in problems if not p.startswith("bounds") and not p.startswith("A6")]
            verdict = "PROVED" if (ok and not failed) else "OPEN"
            status_rows.append((rid, "checker", "-", verdict))
        elif kind.startswith("DIFFERENTIAL"):
            status_rows.append((rid, "sbt", "-", "PROVED-MODULO T9"))
        elif kind.startswith("PREMISE"):
            status_rows.append((rid, "-", "-", "CHECKED-PREMISE"))
        else:
            problems.append(f"{rid}: unknown kind {kind}")
    out = ["# proofs/spatial/STATUS.tsv — written by proofs/spatial/check_transfers.py; do not edit",
           "# id\tby\t-\tverdict"]
    for r in status_rows: out.append("\t".join(r))
    (ROOT / "proofs/spatial/STATUS.tsv").write_text("\n".join(out) + "\n")
    print(f"transfers: {sum(counts.values())} rows re-derived over {len(counts)} operations; bounds: {n} rows re-checked, {bad} outside")
    for p in problems[:40]: print("  !! " + p)
    if len(problems) > 40: print(f"  ... and {len(problems) - 40} more")
    print(f"status: {len(status_rows)} registry rows -> proofs/spatial/STATUS.tsv ({sum(1 for r in status_rows if r[3] == 'OPEN')} OPEN)")
    return 1 if problems else 0

if __name__ == "__main__":
    sys.exit(main())
