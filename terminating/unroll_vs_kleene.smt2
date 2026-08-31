; =============================================================================
; O10(a) — THE INFLATIONARY UNROLLING IS NOT THE KLEENE CHAIN.
;
; Two different operators are called "unrolling a Fixpoint" in this repo:
;
;   THE EXECUTORS (eval MORKL.scala:333-341, exec/execT :652-670, expand
;   EquivPipeline.scala:75-84) iterate the KLEENE chain and accumulate:
;       C_0 = I,  C_{k+1} = F(C_k),        U_k = C_0 u ... u C_k
;   and return U_n at the least n with C_{n+1} = C_n.
;
;   THE DATA-AGNOSTIC PIPELINE (AgnosticPipeline.unrollControl
;   EquivPipeline.scala:328-331) builds the INFLATIONARY chain
;       A_0 = I,  A_{k+1} = A_k u F(A_k)
;   (`var acc = init; for _ <- 1 to k do acc = Union(acc, body[rec := acc])`)
;   and hands A_k to the provers as "the k-unrolling".
;
; The `-agnostic` certificates are advertised (EquivPipeline.scala:280-290) as
; "equivalence of the loop RULE".  They are only certificates ABOUT WHAT THE
; BACKENDS RUN if A_k = U_k, and that is FALSE IN GENERAL.  This file proves
; exactly when it holds and machine-checks two counterexamples showing that
; BOTH hypotheses are load-bearing — neither can be dropped, and neither is a
; proof-engineering convenience.
;
; THEOREM.  If F is subset-MONOTONE and I subset= F(I) then for every k
;       A_k = U_k = C_k.
; (Proved below by three inductions in the no_infinite_descent.smt2 style:
; base, step, then the bridging induction principle asserted.)
;
; COUNTEREXAMPLE 1 — MONOTONICITY IS NEEDED.  Over {a,b,c},
;       G({a}) = {b},   G({a,b}) = {c},   G({b}) = {},        I = {a}
; (this is the shape a non-monotone body such as `Subtraction(_, rec)` produces).
; Then C_0={a}, C_1={b}, C_2={}, so U_2 = {a,b}: the executors return {a,b}.
; But A_1 = {a,b} and A_2 = {a,b,c}: unrollControl claims `c` is reachable in
; two rounds when no executor ever produces it.  Goals CX1a/CX1b/CX1c below
; machine-check that G is non-monotone, that A_2 contains c, and that
; A_2 != U_2.
;
; COUNTEREXAMPLE 2 — I subset= F(I) IS ALSO NEEDED.  Over the same universe let
;       H(X) = {b : a in X} u {c : a in X and b in X},        I = {a}
; H IS monotone (goal CX2a proves it) but I is not below H(I) = {b}.  Then
; C_0={a}, C_1={b}, C_2=H({b})={}, U_2={a,b}, while A_1={a,b} and
; A_2 = {a,b} u H({a,b}) = {a,b,c}.  So monotonicity ALONE does not rescue
; unrollControl: the operator must also be inflationary at the initial value.
; `asFixpoint` (MORKL.scala:1214-1222) always is (its base IS the changing
; mention, so F(X) = X u T(X) syntactically); `asFixpointGeneral` (:1279) and
; `lowerMutualPassthrough` (:1235) are NOT — their `#arg#` component is
; REPLACED, not unioned, each round — which is why this second counterexample
; is the one that matters for the tagged encodings.
;
; WHAT THIS FILE DOES NOT CLAIM, AND WHERE THE CODE NOW STANDS.  It does not
; say any artifact in the repo is wrong: every `-agnostic` artifact came from a
; body the pipeline reached through `asFixpoint`, whose operator is
; inflationary by construction (its base IS the changing mention), so on those
; inputs A_k = U_k and the emitted certificates are about the operator the
; backends run.  What it said was that the GUARD WAS MISSING, and two fixes
; were open: rebuild the Kleene chain, or gate on monotonicity-plus-inflation.
;
; AS OF THIS CHANGE SET A THIRD, BETTER ROUTE HAS LANDED (plan item 1): the
; Fixpoint case of `unrollControl` no longer unrolls at all —
;     case Fixpoint(init, rec, body) =>
;       Fixpoint(unrollControl(init, k), rec, unrollControl(body, k))
; (EquivPipeline.scala:423) — the binder survives to the provers, so there is no
; inflationary chain left to be wrong about, and `AgnosticPipeline` now carries
; its own `monotoneInMention` gate (EquivPipeline.scala:376-399) for the places
; that still need one.  THIS FILE IS WHY THAT CHANGE WAS NECESSARY RATHER THAN
; COSMETIC, and it stays as the standing certificate: it is what licenses
; reading any PREVIOUSLY GENERATED `-agnostic` artifact as a statement about the
; executors, and it is what a future reintroduction of an inflationary unrolling
; has to answer to.
;
; STILL APPROXIMATE, and NOT covered here: recursive `Call`s that no
; `asFixpoint` lowering turns into a `Fixpoint` are still k-unrolled and cut
; with a shared free residual `Mention("residual_<r>_<depth>")`
; (EquivPipeline.scala:430-435).  That is a CUT, not an inflationary chain — a
; different approximation with a different obligation, registered as O10c in
; REGISTRY.tsv and OPEN.
;
; NON-VACUITY.  Both counterexample sections are pure EXISTENCE claims, so a
; contradictory axiom block would make them meaningless — and in an extensional
; set signature z3 cannot construct a model to rule that out (measured: a
; `(check-sat)` over this file's depth-0 axioms alone answers `timeout`, and so
; does a canary query that would answer `unsat` if the axioms were
; contradictory; evidence against inconsistency, not proof).  Rather than claim
; a check that was not obtained, the file carries a FOURTH section that settles
; it outright: the same two counterexamples re-run in a DECIDABLE, AXIOM-FREE
; (_ BitVec 3) encoding where every operator is a total `define-fun` and there
; is nothing to be inconsistent.  Each schematic section additionally PROVES a
; discriminating fact about its own operator (CX1a: G is not monotone; CX2a: H
; IS monotone) that the degenerate reading would make false.
;
; PROVER LOG.  z3 5.1.0 closes all 19 goals in 1.4 s wall.  The file follows the
; two instantiation disciplines that fixpoint_is_lfp.smt2 documents at length:
; an absorption stepping stone is proved and asserted with a trigger before it
; is needed (z3 cannot find the extensionality instance for
; `a subset= b => a u b = b` unaided in incremental mode), and every axiom that
; can manufacture a term carries a demand-driven pattern.
; =============================================================================
(declare-sort Node 0)
(declare-sort NSet 0)
(declare-fun mem (Node NSet) Bool)
(declare-fun subset (NSet NSet) Bool)
(declare-fun cup (NSet NSet) NSet)
(declare-const empty NSet)
(assert (forall ((x Node) (a NSet) (b NSet)) (= (mem x (cup a b)) (or (mem x a) (mem x b)))))
(assert (forall ((a NSet) (b NSet)) (= (subset a b) (forall ((x Node)) (=> (mem x a) (mem x b))))))
(assert (forall ((a NSet) (b NSet)) (=> (forall ((x Node)) (= (mem x a) (mem x b))) (= a b))))
(assert (forall ((x Node)) (not (mem x empty))))

; --- the three-element universe both counterexamples live in.  `sa`, `sb`, `sc`
; are the singletons; nothing below assumes the universe is EXACTLY these three.
(declare-const ea Node) (declare-const eb Node) (declare-const ec Node)
(declare-const sa NSet) (declare-const sb NSet) (declare-const sc NSet)
(assert (distinct ea eb ec))
(assert (forall ((x Node)) (= (mem x sa) (= x ea))))
(assert (forall ((x Node)) (= (mem x sb) (= x eb))))
(assert (forall ((x Node)) (= (mem x sc) (= x ec))))

; =============================================================================
; COUNTEREXAMPLE 1 — a NON-MONOTONE operator on which unrollControl and the
; executors disagree.  G is uninterpreted apart from the three point
; constraints the counterexample needs; the arguments {a}, {a,b}, {b} are
; pairwise distinct (they differ on a member), so the constraints are
; consistent by construction.
; =============================================================================
(declare-fun G (NSet) NSet)
(assert (= (G sa) sb))
(assert (= (G (cup sa sb)) sc))
(assert (= (G sb) empty))
; the two chains at k = 2, written out (no Int indexing needed for k <= 2):
;   Kleene:        C1 = G(I) = sb,   C2 = G(C1) = empty,  U2 = I u C1 u C2
;   inflationary:  A1 = I u G(I),    A2 = A1 u G(A1)
(define-fun cxU2 () NSet (cup (cup sa (G sa)) (G (G sa))))
(define-fun cxA1 () NSet (cup sa (G sa)))
(define-fun cxA2 () NSet (cup cxA1 (G cxA1)))

; --- CX1a: G really is NON-MONOTONE (so this counterexample is about the
; monotonicity hypothesis and nothing else).  Negated: assume G monotone.
(push)
(assert (forall ((x NSet) (y NSet)) (=> (subset x y) (subset (G x) (G y)))))
(check-sat) ; expect unsat
(pop)
; --- CX1b: the inflationary unrolling INVENTS `c` at k = 2.
(push)
(assert (not (mem ec cxA2)))
(check-sat) ; expect unsat
(pop)
; --- CX1c: ...and `c` is not in what any executor returns, so A_2 != U_2.
(push)
(assert (or (mem ec cxU2) (= cxA2 cxU2)))
(check-sat) ; expect unsat
(pop)

; =============================================================================
; COUNTEREXAMPLE 2 — a MONOTONE operator that is not inflationary at I, on
; which they still disagree.  H is pinned pointwise (hence total and monotone
; by construction) rather than by point constraints.
; =============================================================================
(declare-fun H (NSet) NSet)
(assert (forall ((x NSet)) (! (= (mem eb (H x)) (mem ea x)) :pattern ((H x)))))
(assert (forall ((x NSet)) (! (= (mem ec (H x)) (and (mem ea x) (mem eb x))) :pattern ((H x)))))
(assert (forall ((x NSet) (y Node)) (! (=> (mem y (H x)) (or (= y eb) (= y ec))) :pattern ((mem y (H x))))))
(define-fun cyU2 () NSet (cup (cup sa (H sa)) (H (H sa))))
(define-fun cyA1 () NSet (cup sa (H sa)))
(define-fun cyA2 () NSet (cup cyA1 (H cyA1)))

; --- CX2a: H IS monotone.  (Without this the section would prove nothing about
; the inflationary hypothesis - it would just be counterexample 1 again.)
(push)
(assert (not (forall ((x NSet) (y NSet)) (=> (subset x y) (subset (H x) (H y))))))
(check-sat) ; expect unsat
(pop)
; --- CX2b: but H is NOT inflationary at I = {a}: a is not in H({a}) = {b}.
(push)
(assert (subset sa (H sa)))
(check-sat) ; expect unsat
(pop)
; --- CX2c: and A_2 still differs from U_2 - it contains c, which U_2 does not.
(push)
(assert (or (not (mem ec cyA2)) (mem ec cyU2)))
(check-sat) ; expect unsat
(pop)

; =============================================================================
; THE THEOREM.  With BOTH hypotheses the three chains coincide at every k, so
; unrollControl's A_k is exactly what the executors accumulate.
; =============================================================================
; --- stepping stone: absorption (the extensionality instance; see the header).
(push)
(assert (not (forall ((a NSet) (b NSet)) (=> (subset a b) (= (cup a b) b)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet)) (! (=> (subset a b) (= (cup a b) b)) :pattern ((cup a b)))))

(declare-fun F (NSet) NSet)
(declare-const init NSet)
(assert (forall ((x NSet) (y NSet)) (!
  (=> (subset x y) (subset (F x) (F y))) :pattern ((F x) (F y)))))            ; MONOTONE
(assert (subset init (F init)))                                               ; INFLATIONARY AT I

(declare-fun C (Int) NSet)          ; Kleene iterate      `cur` in the executors
(declare-fun U (Int) NSet)          ; accumulated union   `acc` in the executors
(declare-fun A (Int) NSet)          ; inflationary chain  `acc` in unrollControl
(assert (= (C 0) init))
(assert (forall ((n Int)) (! (=> (>= n 0) (= (C (+ n 1)) (F (C n)))) :pattern ((C (+ n 1))))))
(assert (= (U 0) init))
(assert (forall ((n Int)) (! (=> (>= n 0) (= (U (+ n 1)) (cup (U n) (C (+ n 1))))) :pattern ((U (+ n 1))))))
(assert (= (A 0) init))
(assert (forall ((n Int)) (! (=> (>= n 0) (= (A (+ n 1)) (cup (A n) (F (A n))))) :pattern ((A (+ n 1))))))

; --- the Kleene chain ascends (base, step, bridge).
(push)
(assert (not (subset (C 0) (C 1))))
(check-sat) ; expect unsat
(pop)
(push)
(declare-const k0 Int)
(assert (>= k0 0))
(assert (subset (C k0) (C (+ k0 1))))
(assert (not (subset (C (+ k0 1)) (C (+ k0 2)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((n Int)) (! (=> (>= n 0) (subset (C n) (C (+ n 1)))) :pattern ((C (+ n 1))))))

; --- U_k = C_k (base, step, bridge): the accumulator collapses on an ascending
; chain, so "what the executor returns at round k" IS the k-th Kleene iterate.
(push)
(assert (not (= (U 0) (C 0))))
(check-sat) ; expect unsat
(pop)
(push)
(declare-const k1 Int)
(assert (>= k1 0))
(assert (= (U k1) (C k1)))
(assert (not (= (U (+ k1 1)) (C (+ k1 1)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((n Int)) (! (=> (>= n 0) (= (U n) (C n))) :pattern ((U n)))))

; --- A_k = C_k (base, step, bridge): the inflationary chain collapses too.
; A_{k+1} = A_k u F(A_k) = C_k u F(C_k) = C_k u C_{k+1} = C_{k+1}.
(push)
(assert (not (= (A 0) (C 0))))
(check-sat) ; expect unsat
(pop)
(push)
(declare-const k2 Int)
(assert (>= k2 0))
(assert (= (A k2) (C k2)))
(assert (not (= (A (+ k2 1)) (C (+ k2 1)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((n Int)) (! (=> (>= n 0) (= (A n) (C n))) :pattern ((A n)))))

; --- CONCLUSION: unrollControl's k-unrolling equals the executors' round-k
; result, for every k.  This is the sentence AgnosticPipeline needs and, until
; one of the two fixes above lands, may only claim under these two hypotheses.
(push)
(declare-const k3 Int)
(assert (>= k3 0))
(assert (not (= (A k3) (U k3))))
(check-sat) ; expect unsat
(pop)

; =============================================================================
; GROUND WITNESS FOR BOTH COUNTEREXAMPLES — the ANTI-VACUITY half.
;
; Everything above lives in an EXTENSIONAL SET signature, where z3 cannot build
; a model: a `(check-sat)` on the axioms alone answers `timeout`, not `sat`, so
; the sections above cannot be certified non-vacuous the usual way.  (Measured:
; z3 -T:30 on the depth-0 axioms of this file, and on those of
; fixpoint_is_lfp.smt2, both time out; a `canary` query whose answer would be
; `unsat` if the axioms were contradictory also times out rather than
; answering `unsat`, which is evidence against inconsistency but not proof.)
;
; This section removes the doubt entirely by re-running BOTH counterexamples in
; a DECIDABLE, AXIOM-FREE encoding: the three-element universe {a,b,c} as
; (_ BitVec 3), union as `bvor`, subset as `(= (bvor x y) y)`, and each operator
; as a TOTAL `define-fun`.  There is not one `assert` outside the goals, so
; there is nothing to be inconsistent; every goal below is decided by BV +
; quantifier expansion over 8 elements.  It is deliberately concrete — that is
; the point of a witness — and it is the ONLY place in this corpus where being
; ground is a feature rather than the degeneracy docs/traps.md warns about,
; because an existence claim is exactly what a concrete model settles.
; The numbers agree with the schematic sections: G gives A_2 = {a,b,c} vs
; U_2 = {a,b}; H likewise, while being monotone.
; =============================================================================
(define-fun bva () (_ BitVec 3) #b001)                       ; {a}
(define-fun bleq ((x (_ BitVec 3)) (y (_ BitVec 3))) Bool (= (bvor x y) y))
(define-fun gG ((x (_ BitVec 3))) (_ BitVec 3)
  (ite (= x #b001) #b010 (ite (= x #b011) #b100 #b000)))     ; G{a}={b}, G{a,b}={c}, else {}
(define-fun gH ((x (_ BitVec 3))) (_ BitVec 3)               ; H(X) = {b:a in X} u {c:a,b in X}
  (bvor (ite (= (bvand x #b001) #b001) #b010 #b000)
        (ite (= (bvand x #b011) #b011) #b100 #b000)))
(define-fun gU2 () (_ BitVec 3) (bvor (bvor bva (gG bva)) (gG (gG bva))))
(define-fun gA2 () (_ BitVec 3) (bvor (bvor bva (gG bva)) (gG (bvor bva (gG bva)))))
(define-fun hU2 () (_ BitVec 3) (bvor (bvor bva (gH bva)) (gH (gH bva))))
(define-fun hA2 () (_ BitVec 3) (bvor (bvor bva (gH bva)) (gH (bvor bva (gH bva)))))

; --- BV1: G is not monotone (negated: assume it is).
(push)
(assert (forall ((x (_ BitVec 3)) (y (_ BitVec 3))) (=> (bleq x y) (bleq (gG x) (gG y)))))
(check-sat) ; expect unsat
(pop)
; --- BV2: A_2 != U_2 for G (negated: assume equal).  A_2 = #b111, U_2 = #b011.
(push)
(assert (= gA2 gU2))
(check-sat) ; expect unsat
(pop)
; --- BV3: H IS monotone (negated: assume some pair violates it).
(push)
(assert (not (forall ((x (_ BitVec 3)) (y (_ BitVec 3))) (=> (bleq x y) (bleq (gH x) (gH y))))))
(check-sat) ; expect unsat
(pop)
; --- BV4: H is not inflationary at I = {a} (negated: assume it is).
(push)
(assert (bleq bva (gH bva)))
(check-sat) ; expect unsat
(pop)
; --- BV5: A_2 != U_2 for the MONOTONE H (negated: assume equal).
(push)
(assert (= hA2 hU2))
(check-sat) ; expect unsat
(pop)
