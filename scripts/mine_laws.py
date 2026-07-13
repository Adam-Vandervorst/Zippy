#!/usr/bin/env python3
"""LAW MINING: enumerate candidate reduction laws for compositions of Space operators that the
optimizer currently leaves unreduced, state each denotationally (the proofs/laws/ encoding), and
throw the provers at every candidate:
    z3 unsat  (or vampire refutation)  -> PROVED       (a real law)
    z3 sat                             -> COUNTERMODEL (the candidate is FALSE — kept in the
                                          table as documentation of the screening)
    both give up                       -> UNKNOWN
Results land in proofs/laws/MINED.tsv; the PROVED+profitable ones get implemented in Lower and
promoted to generated certificates (gen_law_obligations.py).
"""
import pathlib, subprocess, sys

root = pathlib.Path(__file__).resolve().parent.parent
out = root / "proofs" / "laws" / "MINED.tsv"
tmp = pathlib.Path("/tmp/mine_law.smt2")

PRELUDE = (root / "scripts" / "gen_law_obligations.py").read_text()
PRELUDE = PRELUDE.split('PRELUDE = """')[1].split('"""')[0]

SETS = "(declare-fun A (Path) Bool)\n(declare-fun B (Path) Bool)\n(declare-fun C (Path) Bool)\n(declare-fun P (Path) Bool)\n"
CONSTS = "(declare-const w Path)\n(declare-const q0 Path)\n(declare-const k Int)\n(declare-const j Int)\n"
LEMMAS = """(assert (forall ((a Path) (b Path) (c Path)) (= (append (append a b) c) (append a (append b c)))))
(assert (forall ((v Path) (p Path) (q Path)) (=> (= (append v p) (append v q)) (= p q))))
(assert (forall ((v Path) (p Path)) (= (isPrefix v p) (exists ((q Path)) (= p (append v q))))))
"""  # certified: law_append_assoc / law_append_inj / law_isprefix_append


def wrap(w, s):
    return lambda p: f"(exists ((qq Path)) (and (= {p} (append {w} qq)) {s('qq')}))"
def unwrap(s, w):
    return lambda p: s(f"(append {w} {p})")
def comp(a, b):
    return lambda p: f"(exists ((uu Path) (vv Path)) (and (= {p} (append uu vv)) {a('uu')} {b('vv')}))"
def restrict(a, pr):
    return lambda p: f"(and {a(p)} (exists ((qq Path)) (and {pr('qq')} (isPrefix qq {p}))))"
def tailsu(s):
    return lambda p: f"(exists ((hh Int)) {s(f'(cons hh {p})')})"
A = lambda p: f"(A {p})"
B = lambda p: f"(B {p})"
C = lambda p: f"(C {p})"
Pp = lambda p: f"(P {p})"
def union(x, y): return lambda p: f"(or {x(p)} {y(p)})"
def inter(x, y): return lambda p: f"(and {x(p)} {y(p)})"
def sub(x, y): return lambda p: f"(and {x(p)} (not {y(p)}))"
EMPTY = lambda p: "false"
def eq(l, r): return f"(forall ((p Path)) (= {l('p')} {r('p')}))"

KP = "(cons k nil)"   # single-item path k
JP = "(cons j nil)"

# name, goal, extra assumptions
CANDS = [
    # ---- unwrap pushed through the set operations ----
    ("unwrap-over-union",  eq(unwrap(union(A, B), "w"), union(unwrap(A, "w"), unwrap(B, "w"))), ""),
    ("unwrap-over-inter",  eq(unwrap(inter(A, B), "w"), inter(unwrap(A, "w"), unwrap(B, "w"))), ""),
    ("unwrap-over-sub",    eq(unwrap(sub(A, B), "w"),   sub(unwrap(A, "w"), unwrap(B, "w"))), ""),
    ("unwrap-over-comp-NAIVE", eq(unwrap(comp(A, B), "w"), comp(unwrap(A, "w"), B)), ""),
    # ---- wrap merges (equal constant prefix; distinct single heads) ----
    ("wrap-merge-union",   eq(union(wrap("w", A), wrap("w", B)), wrap("w", union(A, B))), ""),
    ("wrap-merge-inter",   eq(inter(wrap("w", A), wrap("w", B)), wrap("w", inter(A, B))), LEMMAS),
    ("wrap-merge-sub",     eq(sub(wrap("w", A), wrap("w", B)),   wrap("w", sub(A, B))), LEMMAS),
    ("wrap-disjoint-inter", "(=> (distinct k j) " + eq(inter(wrap(KP, A), wrap(JP, B)), EMPTY) + ")", ""),
    ("wrap-disjoint-sub",   "(=> (distinct k j) " + eq(sub(wrap(KP, A), wrap(JP, B)), wrap(KP, A)) + ")", ""),
    # ---- restriction pushed through the set operations (subject on the left) ----
    ("restrict-over-union", eq(restrict(union(A, B), Pp), union(restrict(A, Pp), restrict(B, Pp))), ""),
    ("restrict-inter-left", eq(restrict(inter(A, B), Pp), inter(restrict(A, Pp), B)), ""),
    ("restrict-sub-left",   eq(restrict(sub(A, B), Pp),   sub(restrict(A, Pp), B)), ""),
    ("restrict-prefixes-union", eq(restrict(A, union(Pp, C)), union(restrict(A, Pp), restrict(A, C))), ""),
    ("restrict-wrap-both",  eq(restrict(wrap("w", A), wrap("w", Pp)), wrap("w", restrict(A, Pp))), LEMMAS),
    ("restrict-over-restrict-NAIVE", eq(restrict(restrict(A, Pp), C), restrict(A, inter(Pp, C))), ""),
    # ---- composition ----
    ("comp-wrap-left-assoc", eq(comp(wrap("w", A), B), wrap("w", comp(A, B))), LEMMAS),
    ("comp-over-union-left", eq(comp(union(A, B), C), union(comp(A, C), comp(B, C))), ""),
    ("comp-over-union-right", eq(comp(A, union(B, C)), union(comp(A, B), comp(A, C))), ""),
    ("comp-over-inter-left-NAIVE", eq(comp(inter(A, B), C), inter(comp(A, C), comp(B, C))), ""),
    # ---- tails-union ----
    ("tailsu-over-union",  eq(tailsu(union(A, B)), union(tailsu(A), tailsu(B))), ""),
    ("tailsu-over-inter-NAIVE", eq(tailsu(inter(A, B)), inter(tailsu(A), tailsu(B))), ""),
    ("tailsu-wrap-single", eq(tailsu(wrap(KP, A)), A), ""),
]

results = []
for name, goal, assume in CANDS:
    text = PRELUDE + SETS + CONSTS + assume + f"(assert (not {goal}))\n(check-sat)\n"
    tmp.write_text(text)
    z = subprocess.run(["z3", "-T:20", str(tmp)], capture_output=True, text=True).stdout.strip().splitlines()
    zr = z[-1] if z else "?"
    verdict = {"unsat": "PROVED", "sat": "COUNTERMODEL"}.get(zr)
    vr = "-"
    if verdict is None:
        v = subprocess.run(["/Applications/vampire", "--input_syntax", "smtlib2", "-t", "20s", str(tmp)],
                           capture_output=True, text=True).stdout
        vr = "proved" if "Refutation found" in v else "-"
        verdict = "PROVED" if vr == "proved" else "UNKNOWN"
    results.append((name, zr, vr, verdict))
    print(f"{name:34s} z3={zr:8s} vampire={vr:7s} => {verdict}")

with open(out, "w") as f:
    f.write("# candidate\tz3\tvampire\tverdict\n")
    for r in results:
        f.write("\t".join(r) + "\n")
print(f"\n{sum(1 for r in results if r[3]=='PROVED')} PROVED, "
      f"{sum(1 for r in results if r[3]=='COUNTERMODEL')} COUNTERMODEL, "
      f"{sum(1 for r in results if r[3]=='UNKNOWN')} UNKNOWN -> {out}")
