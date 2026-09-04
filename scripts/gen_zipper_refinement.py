#!/usr/bin/env python3
"""THE UNIVERSAL ZIPPER REFINEMENT, AS FIRST-ORDER OBLIGATIONS (plan.md 2A.4).

Writes `proofs/zipper_refinement.smt2` and its nine step files `proofs/zipper_refinement_<ctor>.smt2`.

WHY TEN FILES AND NOT ONE.  The theorem is an induction over the TERM datatype of the key-free local
algebra: for every term `t` and path `p`, the zipper observation `mem (zip t) p` equals the set
denotation `den t p`.  Stated as one query -- the induction schema instance plus the negated
conclusion -- z3 has to discover every constructor's step inside one search, and it does not (240 s
timeout, measured 2026-09-04).  Split, each step is a small first-order consequence of ONE certified
per-operator leg (`impl_union.smt2`, `threeway_composition_zip.smt2`, ...), asserted as a DERIVED-FROM
axiom, and the main file assumes the nine steps (each `; DERIVED-FROM:` its file) and concludes by the
schema alone.  `proofs/run.sh` runs each file as ONE `(check-sat)` -- it reads the LAST z3 line, so a
multi-goal file would let an early `sat` hide behind a final `unsat` -- which is the other reason.

WHAT IS AND IS NOT COVERED.  `TailsUnion`/`TailsIntersection` need the set of PRESENT heads, which an
uninterpreted `Trie` sort does not carry; the two `threeway_tails*_trie.smt2` legs certify those over
concrete key lists, and the FULL theorem over every constructor is
`proofs/lean/Zippy/Zipper.lean#Zippy.Zip.refinement`, of which these files are the first-order
shadow.  The `% MECHANIZED-IN:` marker on the main file points at it.

The induction schema is `; ASSUMED: T1` (structural induction over a free datatype);
`Zippy.Zip.term_induction` in Zipper.lean is its discharge for exactly this `Term`.
"""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "proofs"

PRELUDE = """(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(define-fun-rec append ((p Path) (q Path)) Path
  (match p ((nil q) ((cons h t) (cons h (append t q))))))
(define-fun-rec isPrefix ((r Path) (p Path)) Bool
  (match r ((nil true)
            ((cons h t) (match p ((nil false)
                                  ((cons h2 t2) (and (= h h2) (isPrefix t t2)))))))))
; ---- the zipper: an abstract cursor sort with its two movements ----
(declare-sort Trie 0)
(declare-fun term (Trie) Bool)
(declare-fun child (Trie Int) Trie)
(define-fun-rec mem ((t Trie) (p Path)) Bool
  (match p ((nil (term t)) ((cons k q) (mem (child t k) q)))))
"""

# the virtual nodes and the certified leg each one's observation law comes from
NODES = {
    "u":  ("impl_union.smt2",
           ["(forall ((a Trie) (b Trie) (p Path)) (= (mem (u a b) p) (or (mem a p) (mem b p))))"]),
    "i":  ("impl_intersection.smt2",
           ["(forall ((a Trie) (b Trie) (p Path)) (= (mem (i a b) p) (and (mem a p) (mem b p))))"]),
    "d":  ("impl_subtraction.smt2",
           ["(forall ((a Trie) (b Trie) (p Path)) (= (mem (d a b) p) (and (mem a p) (not (mem b p)))))"]),
    "w":  ("impl_wrap.smt2",
           ["(forall ((k Int) (t Trie)) (not (mem (w k t) nil)))",
            "(forall ((k Int) (t Trie) (j Int) (q Path)) (= (mem (w k t) (cons j q)) (and (= j k) (mem t q))))"]),
    "zc": ("threeway_composition_zip.smt2",
           ["(forall ((a Trie) (b Trie) (p Path))\n  (= (mem (zc a b) p) (exists ((q Path) (r Path)) (and (= p (append q r)) (mem a q) (mem b r)))))"]),
    "rs": ("threeway_restriction_zip.smt2",
           ["(forall ((a Trie) (b Trie) (p Path))\n  (= (mem (rs a b) p) (and (mem a p) (exists ((r Path)) (and (mem b r) (isPrefix r p))))))"]),
}
DECLS = {"u": "(declare-fun u (Trie Trie) Trie)", "i": "(declare-fun i (Trie Trie) Trie)",
         "d": "(declare-fun d (Trie Trie) Trie)", "w": "(declare-fun w (Int Trie) Trie)",
         "zc": "(declare-fun zc (Trie Trie) Trie)", "rs": "(declare-fun rs (Trie Trie) Trie)"}

def nodes(names):
    out = []
    for n in names:
        leg, laws = NODES[n]
        out.append(DECLS[n])
        for law in laws:
            out.append(f"; DERIVED-FROM: {leg}\n(assert {law})")
    return "\n".join(out) + "\n"

TERM = """; ---- the syntax of the key-free local algebra, with opaque leaves ----
(declare-datatypes ((Term 0))
  (((leaf (src Trie))
    (tunion (l1 Term) (r1 Term))
    (tinter (l2 Term) (r2 Term))
    (tsub (l3 Term) (r3 Term))
    (tcomp (l4 Term) (r4 Term))
    (twrap (k5 Int) (s5 Term))
    (tunwrap (k6 Int) (s6 Term))
    (trestr (l7 Term) (r7 Term))
    (traff (l8 Term) (r8 Term)))))
"""

ZIP = {
    "leaf":    "(assert (forall ((t Trie)) (= (zip (leaf t)) t)))",
    "tunion":  "(assert (forall ((a Term) (b Term)) (= (zip (tunion a b)) (u (zip a) (zip b)))))",
    "tinter":  "(assert (forall ((a Term) (b Term)) (= (zip (tinter a b)) (i (zip a) (zip b)))))",
    "tsub":    "(assert (forall ((a Term) (b Term)) (= (zip (tsub a b)) (d (zip a) (zip b)))))",
    "tcomp":   "(assert (forall ((a Term) (b Term)) (= (zip (tcomp a b)) (zc (zip a) (zip b)))))",
    "twrap":   "(assert (forall ((k Int) (s Term)) (= (zip (twrap k s)) (w k (zip s)))))",
    "tunwrap": "(assert (forall ((k Int) (s Term)) (= (zip (tunwrap k s)) (child (zip s) k))))",
    "trestr":  "(assert (forall ((a Term) (b Term)) (= (zip (trestr a b)) (rs (zip a) (zip b)))))",
    "traff":   "(assert (forall ((a Term) (b Term)) (= (zip (traff a b)) (d (zip a) (rs (zip a) (zip b))))))",
}
DEN = {
    "leaf":    ["(assert (forall ((t Trie) (p Path)) (= (den (leaf t) p) (mem t p))))"],
    "tunion":  ["(assert (forall ((a Term) (b Term) (p Path)) (= (den (tunion a b) p) (or (den a p) (den b p)))))"],
    "tinter":  ["(assert (forall ((a Term) (b Term) (p Path)) (= (den (tinter a b) p) (and (den a p) (den b p)))))"],
    "tsub":    ["(assert (forall ((a Term) (b Term) (p Path)) (= (den (tsub a b) p) (and (den a p) (not (den b p))))))"],
    "tcomp":   ["(assert (forall ((a Term) (b Term) (p Path))\n  (= (den (tcomp a b) p) (exists ((q Path) (r Path)) (and (= p (append q r)) (den a q) (den b r))))))"],
    "twrap":   ["(assert (forall ((k Int) (s Term)) (not (den (twrap k s) nil))))",
                "(assert (forall ((k Int) (s Term) (j Int) (q Path)) (= (den (twrap k s) (cons j q)) (and (= j k) (den s q)))))"],
    "tunwrap": ["(assert (forall ((k Int) (s Term) (p Path)) (= (den (tunwrap k s) p) (den s (cons k p)))))"],
    "trestr":  ["(assert (forall ((a Term) (b Term) (p Path))\n  (= (den (trestr a b) p) (and (den a p) (exists ((r Path)) (and (den b r) (isPrefix r p)))))))"],
    "traff":   ["(assert (forall ((a Term) (b Term) (p Path))\n  (= (den (traff a b) p) (and (den a p) (not (exists ((r Path)) (and (den b r) (isPrefix r p))))))))"],
}
NEEDS = {"leaf": [], "tunion": ["u"], "tinter": ["i"], "tsub": ["d"], "tcomp": ["zc"], "twrap": ["w"],
         "tunwrap": [], "trestr": ["rs"], "traff": ["d", "rs"]}
STEP = {
    "leaf":    "(forall ((t Trie)) (P (leaf t)))",
    "tunion":  "(forall ((a Term) (b Term)) (=> (and (P a) (P b)) (P (tunion a b))))",
    "tinter":  "(forall ((a Term) (b Term)) (=> (and (P a) (P b)) (P (tinter a b))))",
    "tsub":    "(forall ((a Term) (b Term)) (=> (and (P a) (P b)) (P (tsub a b))))",
    "tcomp":   "(forall ((a Term) (b Term)) (=> (and (P a) (P b)) (P (tcomp a b))))",
    "twrap":   "(forall ((k Int) (s Term)) (=> (P s) (P (twrap k s))))",
    "tunwrap": "(forall ((k Int) (s Term)) (=> (P s) (P (tunwrap k s))))",
    "trestr":  "(forall ((a Term) (b Term)) (=> (and (P a) (P b)) (P (trestr a b))))",
    "traff":   "(forall ((a Term) (b Term)) (=> (and (P a) (P b)) (P (traff a b))))",
}
P = "(define-fun P ((t Term)) Bool (forall ((p Path)) (= (mem (zip t) p) (den t p))))\n"

def defs(ctor):
    return ("(declare-fun zip (Term) Trie)\n; the transpiler on the syntax -- the clause for this constructor\n"
            + ZIP[ctor] + "\n(declare-fun den (Term Path) Bool)\n; the set-of-paths semantics -- the clause for this constructor\n"
            + "\n".join(DEN[ctor]) + "\n")

def main():
    steps = []
    for ctor in ZIP:
        text = (f"; ZIPPER REFINEMENT, STEP `{ctor}` (plan.md 2A.4): the induction step of\n"
                f"; proofs/zipper_refinement.smt2 for this constructor, from its certified per-operator leg.\n"
                f"; Generated by scripts/gen_zipper_refinement.py; verdict tracked in proofs/STATUS.tsv.\n"
                + PRELUDE + nodes(NEEDS[ctor]) + TERM + defs(ctor) + P
                + f"(assert (not {STEP[ctor]}))\n(check-sat)\n")
        (OUT / f"zipper_refinement_{ctor}.smt2").write_text(text)
        steps.append(ctor)
    main_text = ("; UNIVERSAL ZIPPER REFINEMENT over the SYNTAX of the key-free local algebra (plan.md 2A.4).\n"
                 ";\n"
                 "; For every term of the local algebra and every path, the zipper `transpileZ` builds observes exactly\n"
                 "; the set `eval` denotes.  Induction over the Term datatype; each constructor's step is its own\n"
                 "; obligation `zipper_refinement_<ctor>.smt2` (assumed below as DERIVED-FROM it) and this file\n"
                 "; concludes by the schema alone.  See scripts/gen_zipper_refinement.py for why ten files.\n"
                 ";\n"
                 "; OUT OF SCOPE HERE: TailsUnion/TailsIntersection (they need the set of PRESENT heads, which an\n"
                 "; uninterpreted Trie sort does not carry; `threeway_tails*_trie.smt2` certify them over key lists).\n"
                 "; The FULL theorem over every constructor, boundaries named, is the Lean theorem:\n"
                 ";\n"
                 "; % MECHANIZED-IN: proofs/lean/Zippy/Zipper.lean#Zippy.Zip.refinement\n"
                 ";\n"
                 "; Generated by scripts/gen_zipper_refinement.py; verdict tracked in proofs/STATUS.tsv.\n"
                 + PRELUDE + nodes(["u", "i", "d", "w", "zc", "rs"]) + TERM
                 + "(declare-fun zip (Term) Trie)\n; the transpiler on the syntax, one clause per constructor\n"
                 + "\n".join(ZIP.values()) + "\n"
                 + "(declare-fun den (Term Path) Bool)\n; the set-of-paths semantics, one clause per constructor\n"
                 + "\n".join(x for v in DEN.values() for x in v) + "\n" + P
                 + "; the nine induction steps, each certified in its own file\n"
                 + "\n".join(f"; DERIVED-FROM: zipper_refinement_{c}.smt2\n(assert {STEP[c]})" for c in steps) + "\n"
                 + "; the structural-induction schema over Term at P\n; ASSUMED: T1\n"
                 + "(assert (=> (and " + "\n                 ".join(STEP[c] for c in steps) + ")\n"
                 + "            (forall ((t Term)) (P t))))\n"
                 + "(assert (not (forall ((t Term)) (P t))))\n(check-sat)\n")
    (OUT / "zipper_refinement.smt2").write_text(main_text)
    print(f"wrote proofs/zipper_refinement.smt2 and {len(steps)} step files")

if __name__ == "__main__":
    main()
