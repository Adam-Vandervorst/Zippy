#!/usr/bin/env python3
"""Generate the PER-LAW certificate corpus under proofs/laws/ + the law REGISTRY.

Each law is one small ∀-statement over the SET-OF-PATHS denotation (sets as Path->Bool
predicates; wrap/unwrap/composition via the quantified append axioms — the same first-order
prelude as the pipeline), asserted NEGATED so z3 "unsat" / vampire "Refutation found" = PROVED
and z3 "sat" = COUNTERMODEL (the statement is FALSE — proofs/run.sh fails loudly on it).

Induction is never smuggled: files needing it carry an EXPLICIT structural-induction schema
instance (the datatype induction axiom instantiated at the named predicate P — valid for Path),
so plain FO provers prove base + step and conclude; files building on a previously certified
lemma assert it with a comment naming the certifying file.

REGISTRY.tsv (law <TAB> kind <TAB> certificates <TAB> note) covers
  - every optimiser source law (SC.sourceLaws — checked in sync by scripts/check_laws.py),
  - the formal.egg set-algebra rule family,
  - the extended algebra: composition assoc/right-distributivity, De Morgan/absorption/
    distributivity, wrap-as-composition, restriction idempotence/chains, raffination partition,
    head·tails∪ covering (a SUBSET statement — stated as a ∀-implication), guard hoisting,
    Iter fusion.
kinds: FILE (∀-certificate in laws/, verdict tracked in proofs/STATUS.tsv), SCHEMATIC (a schema
certified once, per-instance matching replayed syntactically by the pipeline), GROUND (executor-
evaluated ground steps, gated by eval and the randomized differentials), DEFINITIONAL.
"""
import pathlib

root = pathlib.Path(__file__).resolve().parent.parent
outdir = root / "proofs" / "laws"
outdir.mkdir(parents=True, exist_ok=True)

PRELUDE = """(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-fun append (Path Path) Path)
(assert (forall ((q Path)) (= (append nil q) q)))
(assert (forall ((h Int) (t Path) (q Path)) (= (append (cons h t) q) (cons h (append t q)))))
(declare-fun isPrefix (Path Path) Bool)
(assert (forall ((p Path)) (isPrefix nil p)))
(assert (forall ((h Int) (t Path)) (not (isPrefix (cons h t) nil))))
(assert (forall ((h Int) (t Path) (h2 Int) (t2 Path))
  (= (isPrefix (cons h t) (cons h2 t2)) (and (= h h2) (isPrefix t t2)))))
; certified lemmas assumed below: proofs/lemma_append_cons.smt2, proofs/lemma_append_nil.smt2
(assert (forall ((k2 Int) (p Path) (q Path) (r Path))
  (= (= (cons k2 p) (append q r))
     (or (and (= q nil) (= r (cons k2 p)))
         (exists ((q2 Path)) (and (= q (cons k2 q2)) (= p (append q2 r))))))))
(assert (forall ((q Path)) (= (append q nil) q)))
"""

APPEND_ASSOC = """; assumed: proofs/laws/law_append_assoc.smt2 (certified there via a schema instance)
(assert (forall ((a Path) (b Path) (c Path)) (= (append (append a b) c) (append a (append b c)))))
"""
APPEND_INJ = """; assumed: proofs/laws/law_append_inj.smt2 (certified there via a schema instance)
(assert (forall ((w Path) (p Path) (q Path)) (=> (= (append w p) (append w q)) (= p q))))
"""
ISPREFIX_APPEND = """; assumed: proofs/laws/law_isprefix_append.smt2 (certified there via a schema instance)
(assert (forall ((w Path) (p Path)) (= (isPrefix w p) (exists ((q Path)) (= p (append w q))))))
"""

SETS = "(declare-fun A (Path) Bool)\n(declare-fun B (Path) Bool)\n(declare-fun C (Path) Bool)\n"
CONSTS = "(declare-const w Path)\n(declare-const u Path)\n(declare-const q0 Path)\n"


def wr(s, x="w"):        # p ∈ wrap(x, s)
    return lambda p: f"(exists ((qq Path)) (and (= {p} (append {x} qq)) ({s} qq)))" if isinstance(s, str) else None


def mem_wrap(x, s, p):   # s: function p-> formula
    return f"(exists ((qq Path)) (and (= {p} (append {x} qq)) {s('qq')}))"


def mem_unwrap(s, x, p):
    return s(f"(append {x} {p})")


def mem_comp(a, b, p):
    return (f"(exists ((uu Path) (vv Path)) (and (= {p} (append uu vv)) {a('uu')} {b('vv')}))")


def mem_restrict(a, pref, p):
    return f"(and {a(p)} (exists ((qq Path)) (and {pref('qq')} (isPrefix qq {p}))))"


def mem_tailsu(s, p):
    return f"(exists ((hh Int)) {s(f'(cons hh {p})')})"


def mem_tailsi(x, p):
    return (f"(and (exists ((hh Int) (tt Path)) {x('(cons hh tt)')}) "
            f"(forall ((hh Int)) (=> (exists ((tt Path)) {x('(cons hh tt)')}) "
            f"{x(f'(cons hh {p})')})))")


def mem_head(x, p):
    return (f"(exists ((hh Int)) (and (= {p} (cons hh nil)) "
            f"(exists ((tt Path)) {x('(cons hh tt)')})))")


def mem_iterc(s, b, p):
    return f"(and (exists ((hh Int) (tt Path)) {s('(cons hh tt)')}) {b(p)})"


A = lambda p: f"(A {p})"
B = lambda p: f"(B {p})"
C = lambda p: f"(C {p})"
EMPTY = lambda p: "false"
def SING(c):
    return lambda p: f"(= {p} {c})"
def UNION(x, y):
    return lambda p: f"(or {x(p)} {y(p)})"
def INTER(x, y):
    return lambda p: f"(and {x(p)} {y(p)})"
def SUB(x, y):
    return lambda p: f"(and {x(p)} (not {y(p)}))"
def WRAP(x, s):
    return lambda p: mem_wrap(x, s, p)
def UNWRAP(s, x):
    return lambda p: mem_unwrap(s, x, p)
def COMP(a, b):
    return lambda p: mem_comp(a, b, p)
def RESTRICT(a, pr):
    return lambda p: mem_restrict(a, pr, p)
def TAILSU(s):
    return lambda p: mem_tailsu(s, p)
def TAILSI(x):
    return lambda p: mem_tailsi(x, p)
def HEAD(x):
    return lambda p: mem_head(x, p)
def ITERC(s, b):
    return lambda p: mem_iterc(s, b, p)
RAFF = lambda x, y: SUB(x, RESTRICT(x, y))


def eq(l, r):
    return f"(forall ((p Path)) (= {l('p')} {r('p')}))"


def conj(*stmts):
    return "(and\n  " + "\n  ".join(stmts) + ")" if len(stmts) > 1 else stmts[0]


# (filename, description, decls, assumptions, goal)
LAWS = []


def law(name, desc, goal, decls=SETS, assume=""):
    LAWS.append((name, desc, decls, assume, goal))


# ---- schema-instance lemmas (the only induction, made explicit) ----
law("law_append_assoc", "path append is associative",
    "(forall ((a Path) (b Path) (c Path)) (= (append (append a b) c) (append a (append b c))))",
    decls="", assume="""; explicit structural-induction schema instance (valid for the Path datatype)
(define-fun P ((a Path)) Bool (forall ((b Path) (c Path)) (= (append (append a b) c) (append a (append b c)))))
(assert (=> (and (P nil) (forall ((h Int) (t Path)) (=> (P t) (P (cons h t))))) (forall ((a Path)) (P a))))
""")
law("law_append_inj", "append is left-cancellative (injective in its second argument)",
    "(forall ((w Path) (p Path) (q Path)) (=> (= (append w p) (append w q)) (= p q)))",
    decls="", assume="""; explicit structural-induction schema instance (valid for the Path datatype)
(define-fun P ((w Path)) Bool (forall ((p Path) (q Path)) (=> (= (append w p) (append w q)) (= p q))))
(assert (=> (and (P nil) (forall ((h Int) (t Path)) (=> (P t) (P (cons h t))))) (forall ((w Path)) (P w))))
""")
law("law_isprefix_append", "isPrefix w p  <=>  exists q. p = append w q",
    "(forall ((w Path) (p Path)) (= (isPrefix w p) (exists ((q Path)) (= p (append w q)))))",
    decls="", assume="""; explicit structural-induction schema instance (valid for the Path datatype)
(define-fun P ((w Path)) Bool (forall ((p Path)) (= (isPrefix w p) (exists ((q Path)) (= p (append w q))))))
(assert (=> (and (P nil) (forall ((h Int) (t Path)) (=> (P t) (P (cons h t))))) (forall ((w Path)) (P w))))
""")

# ---- the boolean set algebra ----
law("law_union_idem", "A ∪ A = A", eq(UNION(A, A), A))
law("law_inter_idem", "A ∩ A = A", eq(INTER(A, A), A))
law("law_sub_self", "A \\ A = ∅", eq(SUB(A, A), EMPTY))
law("law_union_comm", "A ∪ B = B ∪ A", eq(UNION(A, B), UNION(B, A)))
law("law_inter_comm", "A ∩ B = B ∩ A", eq(INTER(A, B), INTER(B, A)))
law("law_union_assoc", "(A ∪ B) ∪ C = A ∪ (B ∪ C)", eq(UNION(UNION(A, B), C), UNION(A, UNION(B, C))))
law("law_inter_assoc", "(A ∩ B) ∩ C = A ∩ (B ∩ C)", eq(INTER(INTER(A, B), C), INTER(A, INTER(B, C))))
law("law_union_unit", "A ∪ ∅ = A = ∅ ∪ A",
    conj(eq(UNION(A, EMPTY), A), eq(UNION(EMPTY, A), A)))
law("law_inter_empty", "A ∩ ∅ = ∅ = ∅ ∩ A",
    conj(eq(INTER(A, EMPTY), EMPTY), eq(INTER(EMPTY, A), EMPTY)))
law("law_sub_empty", "∅ \\ A = ∅  and  A \\ ∅ = A",
    conj(eq(SUB(EMPTY, A), EMPTY), eq(SUB(A, EMPTY), A)))
law("law_inter_distrib", "∩ distributes over ∪ (both sides)",
    conj(eq(INTER(UNION(A, B), C), UNION(INTER(A, C), INTER(B, C))),
         eq(INTER(A, UNION(B, C)), UNION(INTER(A, B), INTER(A, C)))))
law("law_sub_distrib", "(A ∪ B) \\ C = (A \\ C) ∪ (B \\ C)",
    eq(SUB(UNION(A, B), C), UNION(SUB(A, C), SUB(B, C))))
law("law_demorgan_sub", "the De Morgan family for subtraction",
    conj(eq(SUB(A, UNION(B, C)), SUB(SUB(A, B), C)),
         eq(SUB(A, UNION(B, C)), INTER(SUB(A, B), SUB(A, C))),
         eq(SUB(A, INTER(B, C)), UNION(SUB(A, B), SUB(A, C)))))
law("law_absorption", "A ∪ (A ∩ B) = A  and  A ∩ (A ∪ B) = A",
    conj(eq(UNION(A, INTER(A, B)), A), eq(INTER(A, UNION(A, B)), A)))
law("law_singleton_disq", "p ≠ q  ⇒  {p} \\ {q} = {p}  and  {p} ∩ {q} = ∅",
    conj(eq(SUB(SING("w"), SING("u")), SING("w")),
         eq(INTER(SING("w"), SING("u")), EMPTY)),
    decls=SETS + CONSTS + "(assert (distinct w u))\n")

# ---- wrap / unwrap ----
law("law_wrap_set", "wrap: ∅-absorption, ε-unit, singleton fusion, ∪-distribution",
    conj(eq(WRAP("w", EMPTY), EMPTY),
         eq(WRAP("nil", A), A),
         eq(WRAP("w", SING("u")), SING("(append w u)")),
         eq(WRAP("w", UNION(A, B)), UNION(WRAP("w", A), WRAP("w", B)))),
    decls=SETS + CONSTS)
law("law_unwrap_set", "unwrap: ∅, ε, wrap-inverses, ∪-distribution, singleton characterization, incomparable heads",
    conj(eq(UNWRAP(EMPTY, "w"), EMPTY),
         eq(UNWRAP(A, "nil"), A),
         eq(UNWRAP(WRAP("w", A), "w"), A),
         eq(UNWRAP(WRAP("(append w q0)", A), "w"), WRAP("q0", A)),
         eq(UNWRAP(WRAP("w", A), "(append w q0)"), UNWRAP(A, "q0")),
         eq(UNWRAP(UNION(A, B), "w"), UNION(UNWRAP(A, "w"), UNWRAP(B, "w"))),
         "(forall ((p Path)) (= " + mem_unwrap(SING("u"), "w", "p") + " (= u (append w p))))",
         "(forall ((h Int) (k Int)) (=> (distinct h k) " +
         eq(UNWRAP(WRAP("(cons h nil)", A), "(cons k nil)"), EMPTY) + "))"),
    decls=SETS + CONSTS, assume=APPEND_ASSOC + APPEND_INJ)
law("law_unwrap_merge", "unwrap(unwrap(A, a), b) = unwrap(A, a·b)",
    eq(UNWRAP(UNWRAP(A, "w"), "u"), UNWRAP(A, "(append w u)")),
    decls=SETS + CONSTS, assume=APPEND_ASSOC)

# ---- composition ----
law("law_comp_set", "composition: ∅-absorption, ∪-distribution, singleton = wrap",
    conj(eq(COMP(EMPTY, B), EMPTY),
         eq(COMP(A, EMPTY), EMPTY),
         eq(COMP(UNION(A, B), C), UNION(COMP(A, C), COMP(B, C))),
         eq(COMP(A, UNION(B, C)), UNION(COMP(A, B), COMP(A, C))),
         eq(COMP(SING("w"), B), WRAP("w", B)),
         eq(COMP(UNION(SING("w"), A), B), UNION(WRAP("w", B), COMP(A, B)))),
    decls=SETS + CONSTS)
law("law_comp_assoc", "(A·B)·C = A·(B·C)",
    # the nested-existential form defeats both provers; naming the intermediate compositions
    # as defined predicates (same content) lets resolution index them — both provers then prove.
    "(forall ((p Path)) (= (exists ((u Path) (v Path)) (and (= p (append u v)) (AB u) (C v))) "
    "(exists ((u Path) (v Path)) (and (= p (append u v)) (A u) (BC v)))))",
    decls=SETS + "(declare-fun AB (Path) Bool)\n(declare-fun BC (Path) Bool)\n"
    "(assert (forall ((p Path)) (= (AB p) " + mem_comp(A, B, "p") + ")))\n"
    "(assert (forall ((p Path)) (= (BC p) " + mem_comp(B, C, "p") + ")))\n",
    assume=APPEND_ASSOC)
law("law_comp_rdistrib", "composition distributes over ∪ on the right (and left)",
    conj(eq(COMP(A, UNION(B, C)), UNION(COMP(A, B), COMP(A, C))),
         eq(COMP(UNION(A, B), C), UNION(COMP(A, C), COMP(B, C)))))
law("law_wrap_as_comp", "wrap w A = {w}·A (wrap IS composition with a singleton)",
    eq(WRAP("w", A), COMP(SING("w"), A)),
    decls=SETS + CONSTS)

# ---- restriction / raffination ----
law("law_restrict_set", "restriction: ∅ cases, ε-prefix identity, ∪-distribution (prefixes), singleton = wrap∘unwrap",
    conj(eq(RESTRICT(EMPTY, B), EMPTY),
         eq(RESTRICT(A, EMPTY), EMPTY),
         eq(RESTRICT(A, SING("nil")), A),
         eq(RESTRICT(A, UNION(B, C)), UNION(RESTRICT(A, B), RESTRICT(A, C))),
         eq(RESTRICT(A, SING("w")), WRAP("w", UNWRAP(A, "w")))),
    decls=SETS + CONSTS, assume=ISPREFIX_APPEND)
law("law_restrict_self", "A <| A = A (every path has itself as a prefix)",
    eq(RESTRICT(A, A), A), assume=ISPREFIX_APPEND)
law("law_restrict_idem", "restriction chains: (A<|B)<|B = A<|B and (A<|B)<|C = (A<|C)<|B",
    conj(eq(RESTRICT(RESTRICT(A, B), B), RESTRICT(A, B)),
         eq(RESTRICT(RESTRICT(A, B), C), RESTRICT(RESTRICT(A, C), B))))
law("law_raffination_partition", "(A\\|B) ∪ (A<|B) = A and (A\\|B) ∩ (A<|B) = ∅",
    conj(eq(UNION(RAFF(A, B), RESTRICT(A, B)), A),
         eq(INTER(RAFF(A, B), RESTRICT(A, B)), EMPTY)))

# ---- tails / head ----
law("law_tailsu_set", "tails∪: ∅, {ε}, singletons, ∪-distribution, wrap-heads",
    conj(eq(TAILSU(EMPTY), EMPTY),
         eq(TAILSU(SING("nil")), EMPTY),
         "(forall ((h Int)) " + eq(TAILSU(SING("(cons h nil)")), SING("nil")) + ")",
         "(forall ((h Int) (t Path)) " + eq(TAILSU(SING("(cons h t)")), SING("t")) + ")",
         eq(TAILSU(UNION(A, B)), UNION(TAILSU(A), TAILSU(B))),
         "(forall ((h Int)) " +
         eq(TAILSU(UNION(WRAP("(cons h nil)", A), B)), UNION(A, TAILSU(B))) + ")",
         "(forall ((h Int)) " + eq(TAILSU(WRAP("(cons h nil)", A)), A) + ")"),
    decls=SETS)
law("law_tailsi_set", "tails∩ head-fold: empty-heads, single-head, and the accumulator step (heads abstracted as a predicate)",
    conj("(=> (forall ((h Int) (t Path)) (not (A (cons h t)))) (forall ((p Path)) (not " +
         mem_tailsi(A, "p") + ")))",
         "(forall ((h0 Int)) (=> (and (exists ((t Path)) (A (cons h0 t))) "
         "(forall ((h Int) (t Path)) (=> (A (cons h t)) (= h h0)))) "
         "(forall ((p Path)) (= " + mem_tailsi(A, "p") + " (A (cons h0 p))))))",
         # accumulator step: acc == ∀h∈H. A(h·p); adding head h0 refines it pointwise
         "(forall ((h0 Int) (p Path)) (= "
         "(and (forall ((h Int)) (=> (InH h) (A (cons h p)))) (A (cons h0 p))) "
         "(forall ((h Int)) (=> (or (InH h) (= h h0)) (A (cons h p))))))",
         # and when InH is EXACTLY the heads (nonempty), the accumulated ∀ IS the tails∩ membership
         "(=> (and (forall ((h Int)) (= (InH h) (exists ((t Path)) (A (cons h t))))) "
         "(exists ((h Int) (t Path)) (A (cons h t)))) "
         "(forall ((p Path)) (= (forall ((h Int)) (=> (InH h) (A (cons h p)))) " +
         mem_tailsi(A, "p") + ")))"),
    decls=SETS + "(declare-fun InH (Int) Bool)\n")
law("law_head_set", "head: ∅, {ε}, ∪-distribution, singleton cases",
    conj(eq(HEAD(EMPTY), EMPTY),
         eq(HEAD(SING("nil")), EMPTY),
         eq(HEAD(UNION(A, B)), UNION(HEAD(A), HEAD(B))),
         "(forall ((h Int) (t Path)) " +
         eq(HEAD(SING("(cons h t)")), SING("(cons h nil)")) + ")"),
    decls=SETS)
law("law_head_tails_cover", "head(A)·tails∪(A) ⊇ A on ε-free A (a SUBSET statement, as a ∀-implication)",
    "(forall ((p Path)) (=> (and (A p) (distinct p nil)) " +
    mem_comp(HEAD(A), TAILSU(A), "p") + "))",
    decls=SETS)

# ---- invariant-body iteration ----
law("law_iterc_set", "IterC (invariant body over heads): ∅ source, ε-singleton source (NO heads: ∅ — the ε case the rule split fixed), non-ε singleton, ∪-distribution",
    conj(eq(ITERC(EMPTY, B), EMPTY),
         eq(ITERC(SING("nil"), B), EMPTY),
         "(forall ((h Int) (t Path)) " + eq(ITERC(SING("(cons h t)"), B), B) + ")",
         eq(ITERC(UNION(A, C), B), UNION(ITERC(A, B), ITERC(C, B)))),
    decls=SETS)
law("law_guard_hoist", "hoisting an invariant wrap / composition factor / body-union out of IterC",
    conj(eq(ITERC(A, WRAP("w", B)), WRAP("w", ITERC(A, B))),
         eq(ITERC(A, UNION(B, C)), UNION(ITERC(A, B), ITERC(A, C))),
         eq(ITERC(A, COMP(C, B)), COMP(C, ITERC(A, B)))),
    decls=SETS + CONSTS)
law("law_iter_fusion", "nested invariant iterations fuse and commute",
    conj(eq(ITERC(A, ITERC(A, B)), ITERC(A, B)),
         eq(ITERC(A, ITERC(C, B)), ITERC(C, ITERC(A, B)))),
    decls=SETS)

MINIMAL = "\n".join(PRELUDE.splitlines()[:9]) + "\n"   # axioms only — the certified-lemma
# assumptions blow up the default saturation strategy on the pure-induction schema files.
SCHEMA_FILES = {"law_append_assoc", "law_append_inj", "law_isprefix_append"}

for name, desc, decls, assume, goal in LAWS:
    pre = MINIMAL if name in SCHEMA_FILES else PRELUDE
    text = (f"; LAW CERTIFICATE — {desc}\n"
            f"; Generated by scripts/gen_law_obligations.py; verdict tracked in proofs/STATUS.tsv.\n"
            f"{pre}{decls}{assume}"
            f"(assert (not {goal}))\n(check-sat)\n")
    (outdir / f"{name}.smt2").write_text(text)
print(f"wrote {len(LAWS)} law files to proofs/laws/")

# ---- REGISTRY ----
REG = [
    # SC.sourceLaws (must stay in sync — checked by scripts/check_laws.py)
    ("constant-ops", "GROUND", "threeway_*.smt2,impl_*.smt2", "ground per-op evaluation; eval-gated + differentials"),
    ("algebraic-identities", "FILE", "laws/law_union_unit.smt2,laws/law_inter_empty.smt2,laws/law_sub_empty.smt2,laws/law_union_idem.smt2,laws/law_inter_idem.smt2,laws/law_sub_self.smt2", "the set-algebra identity family"),
    ("iterate-singleton-deref", "SCHEMATIC", "keyfold_iter.smt2", "head-dependent iteration over a singleton source"),
    ("literal-space-ops", "GROUND", "threeway_*.smt2,impl_*.smt2", "ground per-op evaluation; eval-gated + differentials"),
    ("singleton-const-literal", "DEFINITIONAL", "-", "representation change (singleton constant as literal)"),
    ("concat-singleton-iter", "SCHEMATIC", "keyfold_iter.smt2", "iteration body concat with the head singleton"),
    ("iter-union-indep", "FILE", "laws/law_guard_hoist.smt2", "gated hoist; the bare-hoist unsoundness is documented in formal.egg (fail-check)"),
    ("unwrap-merge", "FILE", "laws/law_unwrap_merge.smt2", "adjacent unwraps merge"),
    ("wrap-iter", "FILE", "laws/law_guard_hoist.smt2", "invariant wrap hoisted out of iteration"),
    ("iter-ident", "SCHEMATIC", "keyfold_iter.smt2", "identity iteration"),
    ("concat-path", "DEFINITIONAL", "laws/law_append_assoc.smt2", "path constant folding (canonical right rotation)"),
    ("iterate-literal-union", "SCHEMATIC", "keyfold_iter.smt2", "iteration over exact ground keys = union of body instances"),
    ("unwrap-concat-unwraps", "FILE", "laws/law_unwrap_merge.smt2", "unwrap chains as one concat unwrap"),
    ("singleton-composition-wrap", "FILE", "laws/law_wrap_as_comp.smt2", "singleton composition IS wrap"),
    ("singleton-space-op-path-op", "FILE", "laws/law_wrap_set.smt2,laws/law_unwrap_set.smt2", "singleton space ops as path ops"),
    ("restriction-singleton-unwrap", "FILE", "laws/law_restrict_set.smt2", "restriction by a singleton = wrap of unwrap"),
    ("iter-tails", "FILE", "laws/law_tailsu_set.smt2,keyfolds.smt2", "iteration realizing tails-union"),
    ("tailsunion-singleton", "FILE", "laws/law_tailsu_set.smt2", "tails of singleton sources"),
    ("range-singleton", "GROUND", "-", "trusted positional boundary (fallbacks.md); executor-evaluated"),
    ("unwrap-wrap", "FILE", "laws/law_unwrap_set.smt2", "unwrap of a wrap (all comparability cases)"),
    # formal.egg set-algebra family
    ("union-idem", "FILE", "laws/law_union_idem.smt2", "formal.egg"),
    ("inter-idem", "FILE", "laws/law_inter_idem.smt2", "formal.egg"),
    ("sub-self", "FILE", "laws/law_sub_self.smt2", "formal.egg"),
    ("union-comm", "FILE", "laws/law_union_comm.smt2", "formal.egg (acu)"),
    ("inter-comm", "FILE", "laws/law_inter_comm.smt2", "formal.egg (acu)"),
    ("union-assoc", "FILE", "laws/law_union_assoc.smt2", "formal.egg (directed rotation)"),
    ("inter-assoc", "FILE", "laws/law_inter_assoc.smt2", "formal.egg (directed rotation)"),
    ("union-unit", "FILE", "laws/law_union_unit.smt2", "formal.egg"),
    ("inter-empty", "FILE", "laws/law_inter_empty.smt2", "formal.egg"),
    ("sub-empty", "FILE", "laws/law_sub_empty.smt2", "formal.egg"),
    ("inter-distrib", "FILE", "laws/law_inter_distrib.smt2", "formal.egg"),
    ("sub-distrib", "FILE", "laws/law_sub_distrib.smt2", "formal.egg"),
    ("demorgan-sub", "FILE", "laws/law_demorgan_sub.smt2", "formal.egg + the De Morgan family"),
    ("singleton-disq", "FILE", "laws/law_singleton_disq.smt2", "formal.egg (neg ruleset)"),
    ("append-assoc", "FILE", "laws/law_append_assoc.smt2", "path monoid (schema instance)"),
    ("append-inj", "FILE", "laws/law_append_inj.smt2", "lemma: left cancellation (schema instance)"),
    ("isprefix-append", "FILE", "laws/law_isprefix_append.smt2", "lemma: prefix characterization (schema instance)"),
    ("wrap-set", "FILE", "laws/law_wrap_set.smt2", "formal.egg wrap rules"),
    ("unwrap-set", "FILE", "laws/law_unwrap_set.smt2", "formal.egg unwrap + drop-prefix rules"),
    ("comp-set", "FILE", "laws/law_comp_set.smt2", "formal.egg composition rules"),
    ("tailsu-set", "FILE", "laws/law_tailsu_set.smt2", "formal.egg tails-union rules"),
    ("tailsi-set", "FILE", "laws/law_tailsi_set.smt2", "formal.egg tails-intersection fold"),
    ("restrict-set", "FILE", "laws/law_restrict_set.smt2", "formal.egg restriction rules"),
    ("head-set", "FILE", "laws/law_head_set.smt2", "formal.egg head rules"),
    ("restrict-self", "FILE", "laws/law_restrict_self.smt2", "formal.egg"),
    ("unwrap-merge-set", "FILE", "laws/law_unwrap_merge.smt2", "formal.egg"),
    ("iterc-set", "FILE", "laws/law_iterc_set.smt2", "formal.egg IterC rules (incl. the ε-singleton fix)"),
    # the extended algebra (previously-missing laws, enumerated)
    ("comp-assoc", "FILE", "laws/law_comp_assoc.smt2", "composition associativity"),
    ("comp-rdistrib", "FILE", "laws/law_comp_rdistrib.smt2", "composition right (and left) distributivity over ∪"),
    ("absorption", "FILE", "laws/law_absorption.smt2", "absorption laws"),
    ("wrap-as-comp", "FILE", "laws/law_wrap_as_comp.smt2", "Wrap1 k x = {k}·x"),
    ("restrict-idem", "FILE", "laws/law_restrict_idem.smt2", "restriction idempotence and chains"),
    ("raffination-partition", "FILE", "laws/law_raffination_partition.smt2", "(x\\|y) ∪ (x<|y) = x, disjoint"),
    ("head-tails-cover", "FILE", "laws/law_head_tails_cover.smt2", "head(x)·tails∪(x) ⊇ x on ε-free x (subset as ∀-implication)"),
    ("guard-hoist", "FILE", "laws/law_guard_hoist.smt2", "invariant guard/wrap/composition hoisting"),
    ("iter-fusion", "FILE", "laws/law_iter_fusion.smt2", "nested invariant iterations fuse/commute"),
]
with open(outdir / "REGISTRY.tsv", "w") as f:
    f.write("# law\tkind\tcertificates\tnote\n")
    for row in REG:
        f.write("\t".join(row) + "\n")
print(f"wrote REGISTRY.tsv with {len(REG)} rows")
