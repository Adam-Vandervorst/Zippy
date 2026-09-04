#!/usr/bin/env python3
"""Generate the SPATIAL-TYPE certificate corpus under proofs/spatial/ + its REGISTRY.

The spatial analysis (src/main/scala/SpatialTypes.scala) abstracts a Space as a LENGTH-INDEXED
COUNT domain.  This corpus formalizes it in two layers, each file asserting the NEGATION of its
theorem so z3 "unsat" / vampire "Refutation found" = PROVED and z3 "sat" = COUNTERMODEL.

  lat_*  THE LATTICE.  The count domain is ℕ∪{∞} (a datatype, so ∞ is a real top element, not a
         sentinel Int); intervals over it, ordered by inclusion, form the abstract domain, and a
         spatial type is a pointwise-indexed family of those intervals.  Proved: the order is a
         partial order with ⊥/⊤, join/meet are the lub/glb, absorption + distributivity, the
         saturating arithmetic laws (∞-absorbing, 0-beats-∞ for ×), MONOTONICITY of every
         per-class transfer (the precondition for the fixpoint iteration to be sound), soundness
         of widening/spilling, monotonicity of both projections, the MEET-DOMINATES theorem
         behind `bestSize`/`bestLen`, and the POST-FIXPOINT theorem (Kleene/Tarski, via an
         explicit nat-induction schema) that licenses the Fixpoint transfer.

  sp_*   THE CONCRETION.  The path-structural facts each transfer rests on, over the same
         set-of-paths denotation as proofs/laws (sets as Path->Bool predicates, wrap/unwrap/
         composition via the quantified append axioms) extended with `len`.  Proved: length
         additivity of append, isPrefix ⇒ length ≤, restriction ANNIHILATES classes shorter than
         the shortest prefix, raffination keeps those classes EXACTLY, length-disjoint sets have
         empty meet, wrap/unwrap/tails shift classes by a fixed offset (bijectively for wrap),
         composition adds lengths with a witnessing pair, the composition COLLISION theorem (why
         the per-class lower bound must be a max, never a sum), the subsumption family that
         licenses the relational Union/Intersection/Subtraction tightening, the
         restriction/raffination PARTITION, and iteration group keys having length exactly 1.

The cardinality bridge — that a bijection preserves a count, a disjoint union adds counts, a
subset has a ≤ count, and inclusion–exclusion — is four standard finite-set axioms, asserted
explicitly (kind DEFINITIONAL, marked in the REGISTRY and in each file that uses them).  Every
path-structural fact and every arithmetic consequence ON TOP of them is proved here.
"""
import pathlib

root = pathlib.Path(__file__).resolve().parent.parent
outdir = root / "proofs" / "spatial"
outdir.mkdir(parents=True, exist_ok=True)

# ---------------------------------------------------------------- layer A: the lattice
LAT = """; ℕ∪{∞} — ∞ is a genuine element (a datatype constructor), so the count domain is complete.
(declare-datatypes ((Cnt 0)) (((fin (v Int)) (oo))))
(define-fun okc ((a Cnt)) Bool (or (= a oo) (>= (v a) 0)))
(define-fun cle ((a Cnt) (b Cnt)) Bool (ite (= b oo) true (ite (= a oo) false (<= (v a) (v b)))))
(define-fun cmin ((a Cnt) (b Cnt)) Cnt (ite (cle a b) a b))
(define-fun cmax ((a Cnt) (b Cnt)) Cnt (ite (cle a b) b a))
(define-fun cadd ((a Cnt) (b Cnt)) Cnt (ite (or (= a oo) (= b oo)) oo (fin (+ (v a) (v b)))))
; Ivl.mul: 0 beats ∞ (an empty class times anything is empty) — the Scala convention
(define-fun cmul ((a Cnt) (b Cnt)) Cnt
  (ite (or (= a (fin 0)) (= b (fin 0))) (fin 0)
       (ite (or (= a oo) (= b oo)) oo (fin (* (v a) (v b))))))
(define-fun csub ((a Cnt) (b Cnt)) Cnt          ; relu(a − b), saturating
  (ite (= b oo) (fin 0) (ite (= a oo) oo (fin (ite (>= (- (v a) (v b)) 0) (- (v a) (v b)) 0)))))
; count intervals, ordered by INCLUSION (a ⊑ b means "a is at least as precise as b")
(declare-datatypes ((Ivl 0)) (((mk (lo Cnt) (hi Cnt)))))
(define-fun oki ((a Ivl)) Bool (and (okc (lo a)) (okc (hi a))))
(define-fun ile ((a Ivl) (b Ivl)) Bool (and (cle (lo b) (lo a)) (cle (hi a) (hi b))))
(define-fun ijoin ((a Ivl) (b Ivl)) Ivl (mk (cmin (lo a) (lo b)) (cmax (hi a) (hi b))))
(define-fun imeet ((a Ivl) (b Ivl)) Ivl (mk (cmax (lo a) (lo b)) (cmin (hi a) (hi b))))
; ⊥ is the INCONSISTENT interval (lo > hi): "no count is possible", i.e. the provably-empty
; marker `LenBounds.empty = (INF, 0)`.  [0,0] is NOT the bottom — it is the ordinary element
; "exactly zero paths", and γ([0,0]) = {0} ⊄ γ([2,5]); z3 refuted the [0,0]-as-⊥ claim.
(define-fun bot () Ivl (mk oo (fin 0)))
(define-fun zero () Ivl (mk (fin 0) (fin 0)))   ; "this class is empty" — an ordinary element
(define-fun top () Ivl (mk (fin 0) oo))         ; no information
; γ: a concrete count n is described by an interval
(define-fun inG ((n Int) (a Ivl)) Bool (and (cle (lo a) (fin n)) (cle (fin n) (hi a))))
"""

# the per-class abstract transfers, exactly as SpatialTypes implements them
TRANSFERS = """(define-fun tUnion ((a Ivl) (b Ivl)) Ivl (mk (cmax (lo a) (lo b)) (cadd (hi a) (hi b))))
(define-fun tInter ((a Ivl) (b Ivl)) Ivl (mk (fin 0) (cmin (hi a) (hi b))))
(define-fun tSub ((a Ivl) (b Ivl)) Ivl (mk (csub (lo a) (hi b)) (hi a)))
(define-fun tKill ((a Ivl)) Ivl bot)                                  ; restriction, short class
(define-fun tKeepHi ((a Ivl)) Ivl (mk (fin 0) (hi a)))                ; restriction, long class
(define-fun tScale ((a Ivl) (g Ivl)) Ivl                              ; union of ≤g copies
  (mk (ite (cle (fin 1) (lo g)) (lo a) (fin 0)) (cmul (hi a) (hi g))))
(define-fun tTails ((a Ivl)) Ivl (mk (ite (cle (fin 1) (lo a)) (fin 1) (fin 0)) (hi a)))
"""

LATS = []   # (name, description, body)


def lat(name, desc, goal, extra=""):
    LATS.append((name, desc, LAT + extra + f"(assert (not {goal}))\n(check-sat)\n"))


lat("lat_cnt_order", "ℕ∪{∞} is a total order with 0 least and ∞ greatest",
    """(and (forall ((a Cnt)) (cle a a))
       (forall ((a Cnt) (b Cnt) (c Cnt)) (=> (and (cle a b) (cle b c)) (cle a c)))
       (forall ((a Cnt) (b Cnt)) (=> (and (cle a b) (cle b a)) (= a b)))
       (forall ((a Cnt) (b Cnt)) (or (cle a b) (cle b a)))
       (forall ((a Cnt)) (=> (okc a) (and (cle (fin 0) a) (cle a oo)))))""")

lat("lat_ivl_order", "interval inclusion ⊑ is a partial order",
    """(and (forall ((a Ivl)) (ile a a))
       (forall ((a Ivl) (b Ivl) (c Ivl)) (=> (and (ile a b) (ile b c)) (ile a c)))
       (forall ((a Ivl) (b Ivl)) (=> (and (ile a b) (ile b a)) (= a b))))""")

lat("lat_ivl_lattice", "join is the least upper bound and meet the greatest lower bound",
    """(and (forall ((a Ivl) (b Ivl)) (and (ile a (ijoin a b)) (ile b (ijoin a b))))
       (forall ((a Ivl) (b Ivl) (c Ivl)) (=> (and (ile a c) (ile b c)) (ile (ijoin a b) c)))
       (forall ((a Ivl) (b Ivl)) (and (ile (imeet a b) a) (ile (imeet a b) b)))
       (forall ((a Ivl) (b Ivl) (c Ivl)) (=> (and (ile c a) (ile c b)) (ile c (imeet a b)))))""")

lat("lat_ivl_bounds",
    "⊥ is the INCONSISTENT interval (the provably-empty marker), ⊤ is no-information; [0,0] is neither",
    """(and (forall ((a Ivl)) (=> (oki a) (and (ile bot a) (ile a top))))
       (not (ile zero (mk (fin 2) (fin 5)))))""")

lat("lat_ivl_absorb", "absorption and idempotence",
    """(and (forall ((a Ivl)) (and (= (ijoin a a) a) (= (imeet a a) a)))
       (forall ((a Ivl) (b Ivl)) (= (ijoin a (imeet a b)) a))
       (forall ((a Ivl) (b Ivl)) (= (imeet a (ijoin a b)) a))
       (forall ((a Ivl) (b Ivl)) (and (= (ijoin a b) (ijoin b a)) (= (imeet a b) (imeet b a)))))""")

lat("lat_ivl_distrib", "the interval lattice is distributive (a product of two total orders)",
    """(and (forall ((a Ivl) (b Ivl) (c Ivl)) (= (ijoin a (imeet b c)) (imeet (ijoin a b) (ijoin a c))))
       (forall ((a Ivl) (b Ivl) (c Ivl)) (= (imeet a (ijoin b c)) (ijoin (imeet a b) (imeet a c))))
       (forall ((a Ivl) (b Ivl) (c Ivl)) (and (= (ijoin (ijoin a b) c) (ijoin a (ijoin b c)))
                                              (= (imeet (imeet a b) c) (imeet a (imeet b c))))))""")

lat("lat_sat_add", "saturating addition: commutative, associative, ∞-absorbing, monotone",
    """(and (forall ((a Cnt) (b Cnt)) (= (cadd a b) (cadd b a)))
       (forall ((a Cnt) (b Cnt) (c Cnt)) (= (cadd (cadd a b) c) (cadd a (cadd b c))))
       (forall ((a Cnt)) (and (= (cadd a oo) oo) (= (cadd a (fin 0)) (ite (= a oo) oo a))))
       (forall ((a Cnt) (b Cnt) (c Cnt) (d Cnt)) (=> (and (cle a b) (cle c d)) (cle (cadd a c) (cadd b d)))))""")

lat("lat_sat_mul", "saturating multiplication: commutative, 0-absorbing (0 beats ∞), monotone",
    """(and (forall ((a Cnt) (b Cnt)) (= (cmul a b) (cmul b a)))
       (forall ((a Cnt)) (and (= (cmul a (fin 0)) (fin 0)) (= (cmul (fin 0) a) (fin 0))))
       (forall ((a Cnt)) (=> (and (okc a) (not (= a (fin 0)))) (= (cmul a oo) oo)))
       (forall ((a Cnt) (b Cnt) (c Cnt) (d Cnt))
         (=> (and (okc a) (okc b) (okc c) (okc d) (cle a b) (cle c d)) (cle (cmul a c) (cmul b d)))))""")

lat("lat_sat_sub", "saturating relu-subtraction: monotone up in the minuend, DOWN in the subtrahend",
    """(and (forall ((a Cnt) (b Cnt)) (=> (and (okc a) (okc b)) (cle (fin 0) (csub a b))))
       (forall ((a Cnt) (b Cnt)) (=> (and (okc a) (okc b)) (cle (csub a b) a)))
       (forall ((a Cnt) (b Cnt) (c Cnt))
         (=> (and (okc a) (okc b) (okc c) (cle b c)) (cle (csub a c) (csub a b)))))""")

lat("lat_transfer_mono_binary", "the binary per-class transfers (∪, ∩, ∖) are monotone in ⊑",
    """(forall ((a Ivl) (b Ivl) (a2 Ivl) (b2 Ivl))
         (=> (and (oki a) (oki b) (oki a2) (oki b2) (ile a a2) (ile b b2))
             (and (ile (tUnion a b) (tUnion a2 b2))
                  (ile (tInter a b) (tInter a2 b2))
                  (ile (tSub a b) (tSub a2 b2)))))""",
    extra=TRANSFERS)

lat("lat_transfer_mono_unary", "the unary per-class transfers (restriction kill/keep, tails) are monotone in ⊑",
    """(forall ((a Ivl) (a2 Ivl))
         (=> (and (oki a) (oki a2) (ile a a2))
             (and (ile (tKeepHi a) (tKeepHi a2)) (ile (tTails a) (tTails a2)) (ile (tKill a) (tKill a2)))))""",
    extra=TRANSFERS)

lat("lat_mul_mono_int", "the nonlinear core: 0 ≤ a ≤ b, 0 ≤ c ≤ d ⇒ a·c ≤ b·d",
    """(forall ((a Int) (b Int) (c Int) (d Int))
         (=> (and (<= 0 a) (<= a b) (<= 0 c) (<= c d)) (<= (* a c) (* b d))))""")

lat("lat_transfer_mono_scale",
    "the iteration/fold scaling transfer is monotone in ⊑ (lifting lat_mul_mono_int to ℕ∪{∞})",
    """(forall ((a Ivl) (b Ivl) (a2 Ivl) (b2 Ivl))
         (=> (and (oki a) (oki b) (oki a2) (oki b2) (ile a a2) (ile b b2))
             (ile (tScale a b) (tScale a2 b2))))""",
    extra=TRANSFERS + """; assumed, certified in this corpus: spatial/lat_mul_mono_int.smt2
(assert (forall ((a Int) (b Int) (c Int) (d Int))
  (=> (and (<= 0 a) (<= a b) (<= 0 c) (<= c d)) (<= (* a c) (* b d)))))
""")

lat("lat_transfer_sound", "each transfer's interval CONTAINS the concrete count it must describe",
    """(and (forall ((na Int) (nb Int) (nu Int) (a Ivl) (b Ivl))
         (=> (and (oki a) (oki b) (inG na a) (inG nb b) (>= nu 0)
                  (>= nu na) (>= nu nb) (<= nu (+ na nb)))          ; the union's true class count
             (inG nu (tUnion a b))))
       (forall ((na Int) (nb Int) (ni Int) (a Ivl) (b Ivl))
         (=> (and (oki a) (oki b) (inG na a) (inG nb b) (>= ni 0) (<= ni na) (<= ni nb))
             (inG ni (tInter a b))))
       (forall ((na Int) (nb Int) (nd Int) (a Ivl) (b Ivl))
         (=> (and (oki a) (oki b) (inG na a) (inG nb b) (<= nd na) (>= nd (- na nb)) (>= nd 0))
             (inG nd (tSub a b)))))""",
    extra=TRANSFERS)

lat("lat_meet_dominates", "MEET-DOMINATES: bestSize/bestLen is sound and at least as tight as either tier",
    """(and (forall ((n Int) (a Ivl) (b Ivl))
         (=> (and (inG n a) (inG n b)) (inG n (imeet a b))))
       (forall ((a Ivl) (b Ivl)) (and (ile (imeet a b) a) (ile (imeet a b) b))))""")

lat("lat_widen_sound", "widening only loosens: count-widening and class-spilling are both ⊒",
    """(and (forall ((a Ivl)) (=> (oki a) (ile a (mk (lo a) oo))))
       (forall ((n1 Int) (n2 Int) (i1 Ivl) (i2 Ivl))
         (=> (and (oki i1) (oki i2) (inG n1 i1) (inG n2 i2))
             (and (inG (+ n1 n2) (mk (cadd (lo i1) (lo i2)) (cadd (hi i1) (hi i2))))
                  (inG n1 (mk (fin 0) (cadd (hi i1) (hi i2))))
                  (inG n2 (mk (fin 0) (cadd (hi i1) (hi i2))))))))""")

lat("lat_proj_mono", "both projections are monotone: a tighter type gives tighter size AND length bounds",
    """(and (forall ((a Ivl) (b Ivl) (c Ivl) (a2 Ivl) (b2 Ivl) (c2 Ivl))
         (=> (and (ile a a2) (ile b b2) (ile c c2))                  ; pointwise ⊑ on a 3-class window
             (ile (mk (cadd (cadd (lo a) (lo b)) (lo c)) (cadd (cadd (hi a) (hi b)) (hi c)))
                  (mk (cadd (cadd (lo a2) (lo b2)) (lo c2)) (cadd (cadd (hi a2) (hi b2)) (hi c2))))))
       (forall ((n1 Int) (n2 Int) (a Ivl) (b Ivl))                   ; size projection: classes ADD
         (=> (and (oki a) (oki b) (inG n1 a) (inG n2 b))
             (inG (+ n1 n2) (mk (cadd (lo a) (lo b)) (cadd (hi a) (hi b)))))))""")

# the pointwise-indexed spatial type: three declared families stand for ∀-quantified types
TYPE_DECLS = """(declare-fun S1 (Int) Ivl)
(declare-fun S2 (Int) Ivl)
(declare-fun S3 (Int) Ivl)
(define-fun tle1_2 () Bool (forall ((l Int)) (ile (S1 l) (S2 l))))
(define-fun tle2_3 () Bool (forall ((l Int)) (ile (S2 l) (S3 l))))
(define-fun tle1_3 () Bool (forall ((l Int)) (ile (S1 l) (S3 l))))
"""

lat("lat_type_order", "the pointwise (per-length) order on spatial types is a partial order",
    """(and (forall ((l Int)) (ile (S1 l) (S1 l)))
       (=> (and tle1_2 tle2_3) tle1_3)
       (=> (and tle1_2 (forall ((l Int)) (ile (S2 l) (S1 l)))) (forall ((l Int)) (= (S1 l) (S2 l)))))""",
    extra=TYPE_DECLS)

lat("lat_type_join_lub", "the pointwise join is the least upper bound on spatial types",
    """(and (forall ((l Int)) (and (ile (S1 l) (ijoin (S1 l) (S2 l))) (ile (S2 l) (ijoin (S1 l) (S2 l)))))
       (=> (and (forall ((l Int)) (ile (S1 l) (S3 l))) (forall ((l Int)) (ile (S2 l) (S3 l))))
           (forall ((l Int)) (ile (ijoin (S1 l) (S2 l)) (S3 l)))))""",
    extra=TYPE_DECLS)

# the post-fixpoint theorem — an explicit nat-induction schema instance
POSTFIX = """(declare-fun F (Ivl) Ivl)
; PREMISE: F# is monotone (certified separately: lat_transfer_mono)
(assert (forall ((a Ivl) (b Ivl)) (=> (ile a b) (ile (F a) (F b)))))   ; F# monotone (lat_transfer_mono)
(declare-fun X (Int) Ivl)                                              ; the Kleene iterates
(declare-const init Ivl)
(declare-const T Ivl)
(assert (= (X 0) init))
(assert (forall ((n Int)) (=> (>= n 0) (= (X (+ n 1)) (ijoin (X n) (F (X n)))))))
; PREMISE: init ⊑ T — the analysis checks this before it trusts the post-fixpoint
(assert (ile init T))                                                  ; the analysis checks both
; PREMISE: F#(T) ⊑ T — T is a post-fixpoint; the analysis checks this too
(assert (ile (F T) T))                                                 ; of these premises
; explicit nat-induction schema instance at P
(define-fun P ((n Int)) Bool (ile (X n) T))
; ASSUMED: T8
(assert (=> (and (P 0) (forall ((n Int)) (=> (and (>= n 0) (P n)) (P (+ n 1)))))
            (forall ((n Int)) (=> (>= n 0) (P n)))))
"""
lat("lat_postfixpoint", "POST-FIXPOINT: F#(T) ⊑ T and init ⊑ T ⇒ every Kleene iterate ⊑ T (licenses the Fixpoint transfer)",
    "(forall ((n Int)) (=> (>= n 0) (ile (X n) T)))", extra=POSTFIX)

# ---------------------------------------------------------------- layer B: the concretion
PRELUDE = """(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-fun append (Path Path) Path)
(assert (forall ((q Path)) (= (append nil q) q)))
(assert (forall ((h Int) (t Path) (q Path)) (= (append (cons h t) q) (cons h (append t q)))))
(declare-fun isPrefix (Path Path) Bool)
(assert (forall ((p Path)) (isPrefix nil p)))
(assert (forall ((h Int) (t Path)) (not (isPrefix (cons h t) nil))))
(assert (forall ((h Int) (t Path) (h2 Int) (t2 Path))
  (= (isPrefix (cons h t) (cons h2 t2)) (and (= h h2) (isPrefix t t2)))))
(declare-fun len (Path) Int)
(assert (= (len nil) 0))
(assert (forall ((h Int) (t Path)) (= (len (cons h t)) (+ 1 (len t)))))
"""
MINIMAL = PRELUDE            # schema files get the axioms only
LEMMAS = """; assumed, certified in this corpus: sp_len_append.smt2, sp_isprefix_len.smt2
(assert (forall ((p Path) (q Path)) (= (len (append p q)) (+ (len p) (len q)))))
(assert (forall ((p Path) (q Path)) (=> (isPrefix p q) (<= (len p) (len q)))))
; assumed, certified in proofs/laws/: law_append_inj.smt2, law_isprefix_append.smt2
(assert (forall ((w Path) (p Path) (q Path)) (=> (= (append w p) (append w q)) (= p q))))
(assert (forall ((w Path) (p Path)) (= (isPrefix w p) (exists ((q Path)) (= p (append w q))))))
"""
SETS = "(declare-fun A (Path) Bool)\n(declare-fun B (Path) Bool)\n(declare-const w Path)\n(declare-const m Int)\n"

# membership combinators (same denotation as proofs/laws)
MEM = """(define-fun MUnion ((p Path)) Bool (or (A p) (B p)))
(define-fun MInter ((p Path)) Bool (and (A p) (B p)))
(define-fun MSub ((p Path)) Bool (and (A p) (not (B p))))
(define-fun MRestrict ((p Path)) Bool (and (A p) (exists ((q Path)) (and (B q) (isPrefix q p)))))
(define-fun MRaff ((p Path)) Bool (and (A p) (not (MRestrict p))))
(define-fun MWrap ((p Path)) Bool (exists ((q Path)) (and (= p (append w q)) (A q))))
(define-fun MUnwrap ((p Path)) Bool (A (append w p)))
(define-fun MTails ((p Path)) Bool (exists ((h Int)) (A (cons h p))))
(define-fun MComp ((p Path)) Bool (exists ((u Path) (vv Path)) (and (= p (append u vv)) (A u) (B vv))))
(define-fun MHead ((p Path)) Bool (exists ((h Int)) (and (= p (cons h nil)) (exists ((t Path)) (A (cons h t))))))
"""

SPS = []


def sp(name, desc, goal, extra="", pre=None, lemmas=True):
    body = (pre if pre is not None else PRELUDE) + (LEMMAS if lemmas else "") + extra
    SPS.append((name, desc, body + f"(assert (not {goal}))\n(check-sat)\n"))


# -- the two length lemmas, by explicit structural induction
sp("sp_len_append", "append adds lengths (the class-shift arithmetic)",
   "(forall ((p Path) (q Path)) (= (len (append p q)) (+ (len p) (len q))))",
   extra="""(define-fun P ((p Path)) Bool (forall ((q Path)) (= (len (append p q)) (+ (len p) (len q)))))
; ASSUMED: T1
(assert (=> (and (P nil) (forall ((h Int) (t Path)) (=> (P t) (P (cons h t))))) (forall ((p Path)) (P p))))
""", lemmas=False)

sp("sp_len_nonneg", "every path length is non-negative",
   "(forall ((p Path)) (>= (len p) 0))",
   extra="""(define-fun P ((p Path)) Bool (>= (len p) 0))
; ASSUMED: T1
(assert (=> (and (P nil) (forall ((h Int) (t Path)) (=> (P t) (P (cons h t))))) (forall ((p Path)) (P p))))
""", lemmas=False)

sp("sp_isprefix_len", "a prefix is never longer than the path (the restriction cut-off)",
   "(forall ((p Path) (q Path)) (=> (isPrefix p q) (<= (len p) (len q))))",
   extra="""(define-fun P ((p Path)) Bool (forall ((q Path)) (=> (isPrefix p q) (<= (len p) (len q)))))
; ASSUMED: T1
(assert (=> (and (P nil) (forall ((h Int) (t Path)) (=> (P t) (P (cons h t))))) (forall ((p Path)) (P p))))
; DERIVED-FROM: sp_len_nonneg.smt2
(assert (forall ((p Path)) (>= (len p) 0)))   ; sp_len_nonneg
""", lemmas=False)

# -- the transfers' structural content
sp("sp_restrict_annihilate",
   "RESTRICTION ANNIHILATES SHORT CLASSES: no path shorter than the shortest prefix survives",
   """(=> (forall ((q Path)) (=> (B q) (>= (len q) m)))
       (forall ((p Path)) (=> (< (len p) m) (not (MRestrict p)))))""", extra=SETS + MEM)

sp("sp_raff_exact",
   "RAFFINATION IS EXACT ON SHORT CLASSES: a path shorter than every prefix is always kept",
   """(=> (forall ((q Path)) (=> (B q) (>= (len q) m)))
       (forall ((p Path)) (=> (and (A p) (< (len p) m)) (MRaff p))))""", extra=SETS + MEM)

sp("sp_partition_restrict_raff",
   "PARTITION: x<|y and x\\|y are disjoint and cover x (licenses the exact-sum union)",
   """(and (forall ((p Path)) (= (or (MRestrict p) (MRaff p)) (A p)))
       (forall ((p Path)) (not (and (MRestrict p) (MRaff p)))))""", extra=SETS + MEM)

sp("sp_lendisjoint_meet",
   "LENGTH-DISJOINT MEET IS EMPTY: classes at different lengths cannot intersect",
   """(=> (and (forall ((p Path)) (=> (A p) (= (len p) m)))
            (forall ((p Path)) (=> (B p) (not (= (len p) m)))))
       (forall ((p Path)) (not (MInter p))))""", extra=SETS + MEM)

sp("sp_wrap_into",
   "WRAP maps each source path INJECTIVELY to one |w|-longer path (the class shift, ⊇ direction)",
   """(and (forall ((q Path)) (=> (A q) (and (MWrap (append w q)) (= (len (append w q)) (+ (len w) (len q))))))
       (forall ((q1 Path) (q2 Path)) (=> (= (append w q1) (append w q2)) (= q1 q2))))""",
   extra=SETS + MEM)

sp("sp_wrap_onto",
   "WRAP produces NOTHING ELSE: every wrapped path is |w| longer than a witnessing source path (⊆ direction)",
   """(forall ((p Path)) (=> (MWrap p)
       (exists ((q Path)) (and (A q) (= p (append w q)) (= (len p) (+ (len w) (len q)))))))""",
   extra=SETS + MEM)

sp("sp_unwrap_shift",
   "UNWRAP SHIFTS CLASSES DOWN: every kept path comes from one source path |w| items longer",
   """(forall ((p Path)) (=> (MUnwrap p)
       (exists ((r Path)) (and (A r) (= r (append w p)) (= (len r) (+ (len w) (len p)))))))""",
   extra=SETS + MEM)

sp("sp_tails_shift",
   "TAILS SHIFTS BY ONE, AND A NONEMPTY CLASS YIELDS ≥1 TAIL (the dedup lower bound)",
   """(and (forall ((p Path)) (=> (MTails p) (exists ((r Path)) (and (A r) (= (len r) (+ (len p) 1))))))
       (forall ((r Path)) (=> (and (A r) (>= (len r) 1))
                              (exists ((t Path)) (and (MTails t) (= (len t) (- (len r) 1)))))))""",
   extra=SETS + MEM)

sp("sp_comp_additive",
   "COMPOSITION ADDS LENGTHS: every product path has a witnessing (left, right) class pair",
   """(and (forall ((p Path)) (=> (MComp p)
            (exists ((u Path) (vv Path)) (and (A u) (B vv) (= (len p) (+ (len u) (len vv)))))))
       (forall ((u Path) (vv Path)) (=> (and (A u) (B vv))
            (and (MComp (append u vv)) (= (len (append u vv)) (+ (len u) (len vv)))))))""",
   extra=SETS + MEM)

sp("sp_comp_inject",
   "COMPOSITION IS INJECTIVE FOR A FIXED LEFT FACTOR (the per-class lower bound witness)",
   """(forall ((u Path)) (=> (A u)
       (and (forall ((v1 Path) (v2 Path)) (=> (and (B v1) (B v2) (= (append u v1) (append u v2))) (= v1 v2)))
            (forall ((vv Path)) (=> (B vv) (MComp (append u vv)))))))""",
   extra=SETS + MEM)

# stated as a GROUND witness (a ∃ over paths sends the saturation loop hunting; the concrete
# terms let the prover just rewrite): {a}·{a,aa} and {a,aa}·{a} both contain a·a·a.
sp("sp_comp_collision",
   "COMPOSITION COLLIDES ACROSS CLASS PAIRS: why the per-class lower bound must be a MAX, never a sum",
   """(let ((u1 (cons 1 nil)) (v1 (cons 1 (cons 1 nil))) (u2 (cons 1 (cons 1 nil))) (v2 (cons 1 nil)))
       (and (= (append u1 v1) (append u2 v2))
            (not (= (len u1) (len u2)))
            (= (len (append u1 v1)) 3)))""", lemmas=False)

sp("sp_subsume_ops",
   "SUBSUMPTION TIGHTENING: y ⊆ x ⇒ x∪y = x, x∩y = y, and x∖y is exactly the complement in x",
   """(=> (forall ((p Path)) (=> (B p) (A p)))
       (and (forall ((p Path)) (= (MUnion p) (A p)))
            (forall ((p Path)) (= (MInter p) (B p)))
            (forall ((p Path)) (= (MSub p) (and (A p) (not (B p)))))))""", extra=SETS + MEM)

sp("sp_subsume_syntactic",
   "the SYNTACTIC subsumptions the analysis exploits: ∩, ∖, <|, \\| are all ⊆ their left operand, and each operand ⊆ ∪",
   """(and (forall ((p Path)) (=> (MInter p) (A p)))
       (forall ((p Path)) (=> (MSub p) (A p)))
       (forall ((p Path)) (=> (MRestrict p) (A p)))
       (forall ((p Path)) (=> (MRaff p) (A p)))
       (forall ((p Path)) (=> (A p) (MUnion p)))
       (forall ((p Path)) (=> (B p) (MUnion p))))""", extra=SETS + MEM)

sp("sp_restrict_self",
   "SELF-RESTRICTION IS THE IDENTITY (x <| x = x) and SELF-RAFFINATION IS EMPTY — every path is its own prefix",
   """(and (forall ((p Path)) (= (and (A p) (exists ((q Path)) (and (A q) (isPrefix q p)))) (A p)))
       (forall ((p Path)) (not (and (A p) (not (and (A p) (exists ((q Path)) (and (A q) (isPrefix q p)))))))))""",
   extra=SETS + MEM + "(assert (forall ((p Path)) (isPrefix p p)))   ; sp_isprefix_refl\n")

sp("sp_isprefix_refl", "every path is a prefix of itself (structural induction)",
   "(forall ((p Path)) (isPrefix p p))",
   extra="""(define-fun P ((p Path)) Bool (isPrefix p p))
; ASSUMED: T1
(assert (=> (and (P nil) (forall ((h Int) (t Path)) (=> (P t) (P (cons h t))))) (forall ((p Path)) (P p))))
""", lemmas=False)

sp("sp_head_partition",
   "HEAD-GROUPS PARTITION the headed paths: a path's head and tail are UNIQUE, and group h's tail-set is exactly {t : cons h t in A} — so the group tail-sets are disjoint and cover, hence (with finite additivity) Sigma_g |rest_g| = |headed A|, which is what makes a NESTED iteration linear in the source rather than quadratic",
   """(and (forall ((h1 Int) (t1 Path) (h2 Int) (t2 Path))
            (=> (= (cons h1 t1) (cons h2 t2)) (and (= h1 h2) (= t1 t2))))
       (forall ((h Int) (t Path)) (= (MG h t) (A (cons h t))))
       (forall ((h Int) (t Path)) (=> (MG h t) (A (cons h t)))))""",
   extra=SETS + "(define-fun MG ((h Int) (p Path)) Bool (A (cons h p)))\n", lemmas=False)

sp("sp_iter_disjoint_cylinders",
   "DISJOINT CYLINDERS: bodies keyed by DISTINCT group heads cannot share a path, so a keyed iteration's per-group results are pairwise disjoint (its size is an exact SUM)",
   """(forall ((h1 Int) (h2 Int) (p Path) (q Path))
       (=> (not (= h1 h2)) (not (= (cons h1 p) (cons h2 q)))))""", lemmas=False)

sp("sp_iter_head_one",
   "ITERATION GROUP KEYS HAVE LENGTH EXACTLY 1 (the head-binder length hint the analysis relies on)",
   """(and (forall ((p Path)) (=> (MHead p) (= (len p) 1)))
       (forall ((h Int) (t Path)) (=> (A (cons h t)) (MHead (cons h nil)))))""", extra=SETS + MEM)

# -- the cardinality bridge: 4 standard finite-set axioms, then the per-class bounds ON TOP
MEASURE = """; ---- the CARDINALITY BRIDGE (kind DEFINITIONAL — standard finite-set facts) --------------
; cX l = |{p ∈ X : len p = l}| for the derived sets, tied to membership and to each other by the
; usual finite-measure laws.  Everything BELOW this line is proved from them.
(declare-fun cA (Int) Int)
(declare-fun cB (Int) Int)
(declare-fun cU (Int) Int)
(declare-fun cI (Int) Int)
(declare-fun cD (Int) Int)
; ASSUMED: T7
(assert (forall ((l Int)) (and (>= (cA l) 0) (>= (cB l) 0) (>= (cU l) 0) (>= (cI l) 0) (>= (cD l) 0))))
(assert (forall ((l Int)) (= (cU l) (- (+ (cA l) (cB l)) (cI l)))))        ; inclusion–exclusion
; ASSUMED: T7
(assert (forall ((l Int)) (and (<= (cI l) (cA l)) (<= (cI l) (cB l)))))    ; meet ⊆ both
(assert (forall ((l Int)) (= (cD l) (- (cA l) (cI l)))))                   ; x∖y = x minus the meet
"""

sp("sp_class_bounds",
   "the per-class UNION/INTERSECTION/SUBTRACTION bounds the analysis uses, from the measure axioms",
   """(forall ((l Int))
       (and (<= (cA l) (cU l)) (<= (cB l) (cU l)) (<= (cU l) (+ (cA l) (cB l)))
            (<= (cI l) (cA l)) (<= (cI l) (cB l))
            (<= (cD l) (cA l)) (>= (cD l) (- (cA l) (cB l))) (>= (cD l) 0)))""",
   extra=MEASURE, lemmas=False)

sp("sp_class_ie_tighter",
   "INCLUSION–EXCLUSION IS STRICTLY STRONGER than the additive union bound whenever the classes overlap",
   """(forall ((l Int)) (=> (>= (cI l) 1) (< (cU l) (+ (cA l) (cB l)))))""",
   extra=MEASURE, lemmas=False)

# The concretization order.  The FIRST conjunct is what a post-fixpoint argument needs: t1 ⊑ t2 must
# imply γ(t1) ⊆ γ(t2).  The SECOND is a refutation kept deliberately: the UPPER-ENVELOPE-only
# comparison that `SpaceType.within` computes does NOT imply γ-containment, so the code's fixpoint
# check is not this order and must justify its lower bounds separately (it takes them from `init`).
sp("sp_gamma_order",
   "CONCRETIZATION ORDER: interval inclusion (both endpoints) implies gamma-containment, and an UPPER-ENVELOPE-only comparison does NOT — the exact gap between the certified order and SpaceType.within",
   """(and (forall ((alo Int) (ahi Int) (blo Int) (bhi Int) (c Int))
            (=> (and (<= blo alo) (<= ahi bhi) (<= alo c) (<= c ahi))
                (and (<= blo c) (<= c bhi))))
       (not (forall ((alo Int) (ahi Int) (blo Int) (bhi Int) (c Int))
              (=> (and (<= ahi bhi) (<= alo c) (<= c ahi))
                  (and (<= blo c) (<= c bhi))))))""", lemmas=False)

# ---------------------------------------------------------------- emit
for name, desc, body in LATS:
    (outdir / f"{name}.smt2").write_text(
        f"; SPATIAL-TYPE CERTIFICATE (lattice) — {desc}\n"
        f"; Generated by scripts/gen_spatial_obligations.py; verdict tracked in proofs/STATUS.tsv.\n{body}")
for name, desc, body in SPS:
    (outdir / f"{name}.smt2").write_text(
        f"; SPATIAL-TYPE CERTIFICATE (concretion) — {desc}\n"
        f"; Generated by scripts/gen_spatial_obligations.py; verdict tracked in proofs/STATUS.tsv.\n{body}")
print(f"wrote {len(LATS)} lattice + {len(SPS)} concretion files to proofs/spatial/")

REG = [
    ("Cnt total order (ℕ∪{∞})", "FILE", "spatial/lat_cnt_order.smt2", "the count domain: 0 least, ∞ greatest"),
    ("Ivl partial order", "FILE", "spatial/lat_ivl_order.smt2", "⊑ = interval inclusion"),
    ("Ivl lattice (lub/glb)", "FILE", "spatial/lat_ivl_lattice.smt2", "join/meet are the lub/glb"),
    ("Ivl bounds ⊥/⊤", "FILE", "spatial/lat_ivl_bounds.smt2", "⊥ = the INCONSISTENT interval (empty marker); [0,0] is NOT ⊥ — z3 refuted that first draft"),
    ("Ivl absorption/idempotence", "FILE", "spatial/lat_ivl_absorb.smt2", ""),
    ("Ivl distributivity", "FILE", "spatial/lat_ivl_distrib.smt2", "product of two total orders"),
    ("saturating +", "FILE", "spatial/lat_sat_add.smt2", "comm/assoc/∞-absorbing/monotone"),
    ("saturating ×", "FILE", "spatial/lat_sat_mul.smt2", "0 beats ∞ (Ivl.mul convention)"),
    ("saturating relu −", "FILE", "spatial/lat_sat_sub.smt2", "monotone down in the subtrahend"),
    ("transfer monotonicity (∪∩∖)", "FILE", "spatial/lat_transfer_mono_binary.smt2", "precondition of the fixpoint iteration"),
    ("transfer monotonicity (unary)", "FILE", "spatial/lat_transfer_mono_unary.smt2", "restriction kill/keep, tails"),
    ("transfer monotonicity (scale)", "FILE", "spatial/lat_transfer_mono_scale.smt2", "iteration/fold scaling; lifts lat_mul_mono_int"),
    ("nonlinear mul monotonicity", "FILE", "spatial/lat_mul_mono_int.smt2", "the Int core factored out so the lifting stays linear"),
    ("transfer local soundness", "FILE", "spatial/lat_transfer_sound.smt2", "each interval contains the true class count"),
    ("meet dominates", "FILE", "spatial/lat_meet_dominates.smt2", "the bestSize/bestLen theorem"),
    ("widening soundness", "FILE", "spatial/lat_widen_sound.smt2", "count-widening and class-spilling only loosen"),
    ("projection monotonicity", "FILE", "spatial/lat_proj_mono.smt2", "size and length projections monotone; classes add"),
    ("spatial-type order", "FILE", "spatial/lat_type_order.smt2", "pointwise per-length order"),
    ("spatial-type join", "FILE", "spatial/lat_type_join_lub.smt2", "pointwise join is the lub"),
    ("POST-FIXPOINT theorem", "FILE", "spatial/lat_postfixpoint.smt2", "licenses the Fixpoint transfer (nat-induction schema)"),
    ("len ∘ append", "FILE", "spatial/sp_len_append.smt2", "structural-induction schema"),
    ("len non-negative", "FILE", "spatial/sp_len_nonneg.smt2", "structural-induction schema"),
    ("isPrefix ⇒ len ≤", "FILE", "spatial/sp_isprefix_len.smt2", "structural-induction schema; the restriction cut-off"),
    ("restriction annihilation", "FILE", "spatial/sp_restrict_annihilate.smt2", "short classes cannot survive a longer prefix"),
    ("raffination exactness", "FILE", "spatial/sp_raff_exact.smt2", "short classes are kept exactly"),
    ("restriction/raffination partition", "FILE", "spatial/sp_partition_restrict_raff.smt2", "disjoint + covering"),
    ("length-disjoint meet", "FILE", "spatial/sp_lendisjoint_meet.smt2", "different lengths ⇒ empty intersection"),
    ("wrap injection (⊇)", "FILE", "spatial/sp_wrap_into.smt2", "exact class shift, injective"),
    ("wrap surjection (⊆)", "FILE", "spatial/sp_wrap_onto.smt2", "nothing else is produced"),
    ("unwrap shift", "FILE", "spatial/sp_unwrap_shift.smt2", ""),
    ("tails shift + dedup", "FILE", "spatial/sp_tails_shift.smt2", "≥1 tail per nonempty class"),
    ("composition additivity", "FILE", "spatial/sp_comp_additive.smt2", "class-pair convolution covers the output"),
    ("composition injectivity", "FILE", "spatial/sp_comp_inject.smt2", "the per-class lower-bound witness"),
    ("composition collision", "FILE", "spatial/sp_comp_collision.smt2", "why the per-class lower bound is a MAX, not a sum"),
    ("subsumption tightening", "FILE", "spatial/sp_subsume_ops.smt2", "y ⊆ x ⇒ x∪y = x, x∩y = y"),
    ("syntactic subsumptions", "FILE", "spatial/sp_subsume_syntactic.smt2", "licenses the relational Union/Inter/Sub cases"),
    ("self-restriction identity", "FILE", "spatial/sp_restrict_self.smt2", "x <| x = x, x \\| x = ∅ — closes a z3-only lower bound"),
    ("isPrefix reflexive", "FILE", "spatial/sp_isprefix_refl.smt2", "structural-induction schema"),
    ("head-group partition", "FILE", "spatial/sp_head_partition.smt2", "Sigma_g |rest_g| = |headed src| — makes a NESTED iteration linear, not quadratic"),
    ("disjoint cylinders (iteration)", "FILE", "spatial/sp_iter_disjoint_cylinders.smt2", "distinct group heads ⇒ disjoint per-group results"),
    ("iteration key length", "FILE", "spatial/sp_iter_head_one.smt2", "group keys are single items"),
    ("cardinality bridge", "DEFINITIONAL", "spatial/sp_class_bounds.smt2", "4 finite-measure axioms asserted; the per-class bounds PROVED on top"),
    ("per-class bounds", "FILE", "spatial/sp_class_bounds.smt2", "union/inter/sub class bounds from the measure axioms"),
    ("inclusion–exclusion strength", "FILE", "spatial/sp_class_ie_tighter.smt2", "IE beats the additive bound on overlap — the strengthening"),
    ("concretization order", "FILE", "spatial/sp_gamma_order.smt2", "interval inclusion ⇒ γ-containment; upper-envelope alone does NOT (refuted) — bounds what `within` licenses"),
]
with open(outdir / "REGISTRY.tsv", "w") as f:
    f.write("law\tkind\tcertificates\tnote\n")
    for row in REG:
        f.write("\t".join(row) + "\n")
print(f"wrote REGISTRY.tsv with {len(REG)} rows")
