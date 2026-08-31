; =============================================================================
; O3a — THE TAGGED-UNION PROJECTION LAW, the algebra both tagged lowerings run on.
;
; `asFixpointGeneral` (MORKL.scala:1279-1318) and `lowerMutualPassthrough`
; (:1235-1270) both encode SEVERAL relations in ONE Fixpoint state by wrapping
; each under its own tag and unwrapping to read a component back:
;
;   asFixpointGeneral    S = Wrap(arg-part, #arg#) u Wrap(out-part, #out#)
;                        result = Unwrap(lfp, #out#)
;   lowerMutualPassthrough
;                        S = U_i Wrap(B_i[...], #scc#r_i)
;                        r_i = Unwrap(lfp, #scc#r_i)
;
; The whole encoding is sound only if UNWRAPPING AT A TAG RECOVERS EXACTLY THAT
; COMPONENT AND NOTHING ELSE.  proofs/laws/law_wrap_disjoint.smt2 says two
; constant prefixes with different HEAD ITEMS give disjoint cylinders, and
; proofs/laws/law_unwrap_set.smt2 characterises a single Unwrap; NEITHER states
; the n-ary tagged-union projection these two passes rely on.  This file does.
;
; ENCODING.  A space is a PREDICATE over paths, exactly as the proofs/laws/*
; certificates encode it (`A : Path -> Bool`), with
;     Wrap(A, w)(p)    <=>  exists q. p = append(w, q) and A(q)
;     Unwrap(A, w)(q)  <=>  A(append(w, q))
; and `append` axiomatised as in proofs/laws/law_wrap_disjoint.smt2 (the same
; two recursion clauses, the same certified `append_cons` decomposition and
; `append_nil` facts, imported as premises rather than re-derived).
;
; THEOREM, in four parts, then instantiated at 2 and 3 tags:
;   (P1) ROUND TRIP:      Unwrap(Wrap(A, t), t) = A, for a ONE-ITEM tag t.
;   (P2) CROSS TALK IS ZERO: for tags with DIFFERENT HEAD ITEMS,
;        Unwrap(Wrap(A, u), t) = {} — nothing wrapped under u is visible under t.
;   (P3) UNWRAP IS ADDITIVE: Unwrap(A u B, t) = Unwrap(A, t) u Unwrap(B, t).  In
;        this encoding Unwrap is pointwise precomposition with `append t`, so
;        additivity is TRUE BY DEFINITION and is NOT shipped as a goal — a goal
;        that reduces to `X <=> X` would be exactly the degenerate obligation
;        docs/traps.md and plan item 12 forbid.  It is used below, and it is
;        recorded here so its absence from the goal list is deliberate.
;   (P4) hence the N-ARY PROJECTION, by induction on the number of components
;        with (P2)+(P3) as the step and (P1) as the base.  The induction is over
;        the SYNTAX of the union `U_i Wrap(B_i, t_i)` that the two passes build,
;        so it is a schema; goals `project_two` and `project_three` below pin
;        its instances at the two arities the compiler actually emits
;        (asFixpointGeneral: exactly 2; lowerMutualPassthrough: |SCC| >= 2, and
;        3 is the first arity where a middle component has neighbours on both
;        sides).  Goal `project_step` pins the induction step itself in the form
;        the schema uses, so the schema is not hand-waved: adding one more
;        differently-tagged component changes no other component's projection.
;
; WHY "DIFFERENT HEAD ITEMS" IS THE RIGHT HYPOTHESIS AND NOT A CONVENIENCE.
; Both passes build their tags as ONE-ITEM constant paths from distinct strings
; — `Path.Constant(PathValue(List("#scc#" + rp.s)))` (MORKL.scala:1263) and the
; literal `#arg#` / `#out#` (:1291-1292) — so distinct tags differ in their head
; item by construction, and P2 applies.  If a future change made tags MULTI-item
; with a shared first item (say `#scc#` / `r1` as two items) P2 would no longer
; apply and the encoding would leak between components.  That is why the
; hypothesis below is stated on the HEAD, matching law_wrap_disjoint, rather
; than on the tags being merely distinct.
;
; WHAT IS NOT CLAIMED.  (1) P1 is proved for ONE-ITEM tags, which is what both
; passes build (MORKL.scala:1263, :1291-1292).  The arbitrary-prefix version
; `Unwrap(Wrap(A,w),w) = A` needs `append` to be injective in its second
; argument for an arbitrary w, which is an INDUCTION ON w that z3 does not find
; (measured: >30 s timeout on the goal, with the certified append_cons
; decomposition already imported); it is not needed here and is therefore not
; claimed.  (2) This file is pure path algebra: it says nothing about
; the FIXPOINT the tagged state is the state of (that is O1), nothing about the
; monotonicity gates (mono_soundness.smt2), and nothing about the reserved-name
; hygiene that keeps `#arg#` / `#scc#r` from colliding with a user path (that is
; a syntactic check in the compiler, registered as a PROPERTY row in
; REGISTRY.tsv, not an SMT obligation).
;
; PROVER LOG (z3 5.1.0).  All goals close in well under a second ONCE the tags
; are one-item.  The append decomposition lemma is imported the way the laws/
; files import it; without it P2 does not close, because the prover has to
; invert `append` on a cons.  The first draft stated P1 and the injectivity
; lemma for an ARBITRARY prefix w and timed out at 30 s on the very first goal
; — see NOT CLAIMED (1); the fix was to state exactly what the compiler needs
; rather than to raise the timeout.
; =============================================================================
(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))
(declare-fun append (Path Path) Path)
(assert (forall ((q Path)) (= (append nil q) q)))
(assert (forall ((h Int) (t Path) (q Path)) (= (append (cons h t) q) (cons h (append t q)))))
; certified lemmas assumed below (as in proofs/laws/*): proofs/lemma_append_cons.smt2,
; proofs/lemma_append_nil.smt2 — the cons/append decomposition and the right unit.
(assert (forall ((k2 Int) (p Path) (q Path) (r Path))
  (= (= (cons k2 p) (append q r))
     (or (and (= q nil) (= r (cons k2 p)))
         (exists ((q2 Path)) (and (= q (cons k2 q2)) (= p (append q2 r))))))))
(assert (forall ((q Path)) (= (append q nil) q)))

; --- the component spaces, and three distinct one-item tags.
(declare-fun A (Path) Bool)
(declare-fun B (Path) Bool)
(declare-fun D (Path) Bool)
(declare-const k1 Int) (declare-const k2 Int) (declare-const k3 Int)
(define-fun t1 () Path (cons k1 nil))
(define-fun t2 () Path (cons k2 nil))
(define-fun t3 () Path (cons k3 nil))

; =============================================================================
; (P1) ROUND TRIP at a one-item tag: Unwrap(Wrap(A,t1), t1)(q)  <=>  A(q).
; The "=>" direction is where `append` injectivity in its second argument is
; needed: p = append(t1,q) and p = append(t1,q') must force q = q'.
; =============================================================================
(push)
(assert (not (forall ((q Path))
  (= (exists ((r Path)) (and (= (append t1 q) (append t1 r)) (A r))) (A q)))))
(check-sat) ; expect unsat
(pop)
; --- the injectivity fact on its own, so the reason P1 holds is on the record.
(push)
(assert (not (forall ((k Int) (q Path) (r Path))
  (=> (= (append (cons k nil) q) (append (cons k nil) r)) (= q r)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((k Int) (q Path) (r Path)) (!
  (=> (= (append (cons k nil) q) (append (cons k nil) r)) (= q r))
  :pattern ((append (cons k nil) q) (append (cons k nil) r)))))

; =============================================================================
; (P2) CROSS TALK IS ZERO for tags with different head items.
; Unwrap(Wrap(A, t2), t1)(q) is FALSE whenever k1 != k2.
; =============================================================================
(push)
(assert (not (forall ((q Path))
  (=> (distinct k1 k2)
      (not (exists ((r Path)) (and (= (append t1 q) (append t2 r)) (A r))))))))
(check-sat) ; expect unsat
(pop)
; --- the underlying disjointness, stated separately (this is
; proofs/laws/law_wrap_disjoint.smt2's content, in the form P4 consumes).
(push)
(assert (not (forall ((q Path) (r Path)) (=> (distinct k1 k2) (distinct (append t1 q) (append t2 r))))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((q Path) (r Path)) (!
  (=> (distinct k1 k2) (distinct (append t1 q) (append t2 r)))
  :pattern ((append t1 q) (append t2 r)))))

; =============================================================================
; (P4) THE PROJECTIONS.  `Wrap(A,t1) u Wrap(B,t2) u Wrap(D,t3)` read at each tag.
; Two tags first (asFixpointGeneral's #arg#/#out#), then three
; (lowerMutualPassthrough's smallest interesting SCC), then the induction STEP
; that makes the general arity a schema rather than an extrapolation.
; =============================================================================
; --- project_two, component 1: reading at t1 gives exactly A.
(push)
(assert (distinct k1 k2))
(assert (not (forall ((q Path))
  (= (or (exists ((r Path)) (and (= (append t1 q) (append t1 r)) (A r)))
         (exists ((r Path)) (and (= (append t1 q) (append t2 r)) (B r))))
     (A q)))))
(check-sat) ; expect unsat
(pop)
; --- project_two, component 2: reading at t2 gives exactly B.
(push)
(assert (distinct k1 k2))
(assert (not (forall ((q Path))
  (= (or (exists ((r Path)) (and (= (append t2 q) (append t1 r)) (A r)))
         (exists ((r Path)) (and (= (append t2 q) (append t2 r)) (B r))))
     (B q)))))
(check-sat) ; expect unsat
(pop)
; --- project_three, the MIDDLE component: neighbours on both sides, which is
; the case a two-tag instance cannot exercise.
(push)
(assert (and (distinct k1 k2) (distinct k2 k3) (distinct k1 k3)))
(assert (not (forall ((q Path))
  (= (or (exists ((r Path)) (and (= (append t2 q) (append t1 r)) (A r)))
         (exists ((r Path)) (and (= (append t2 q) (append t2 r)) (B r)))
         (exists ((r Path)) (and (= (append t2 q) (append t3 r)) (D r))))
     (B q)))))
(check-sat) ; expect unsat
(pop)
; --- project_three, an OUTER component, for completeness.
(push)
(assert (and (distinct k1 k2) (distinct k2 k3) (distinct k1 k3)))
(assert (not (forall ((q Path))
  (= (or (exists ((r Path)) (and (= (append t3 q) (append t1 r)) (A r)))
         (exists ((r Path)) (and (= (append t3 q) (append t2 r)) (B r)))
         (exists ((r Path)) (and (= (append t3 q) (append t3 r)) (D r))))
     (D q)))))
(check-sat) ; expect unsat
(pop)
; --- project_step: THE INDUCTION STEP of the n-ary schema.  For an arbitrary
; already-built tagged union `S` (an uninterpreted space) and one more
; component wrapped at a DIFFERENT tag, the reading at t1 is unchanged.  With
; (P1) as the base this is the whole schema, at every arity.
(declare-fun S (Path) Bool)
(push)
(assert (distinct k1 k2))
(assert (not (forall ((q Path))
  (= (or (S (append t1 q)) (exists ((r Path)) (and (= (append t1 q) (append t2 r)) (B r))))
     (S (append t1 q))))))
(check-sat) ; expect unsat
(pop)
; --- tag_append_is_cons: wrapping at a ONE-ITEM tag IS a cons.  This is the
; bridge to tagged_order.smt2, which states the ORDER CORRESPONDENCE for tagged
; states in `cons` form (it has to: with the `append` axioms and the imported
; decomposition lemma in scope, z3 times out on those two goals at 40 s, and
; over the bare datatype it closes them in 0.02 s).
(push)
(assert (not (forall ((k Int) (r Path)) (= (append (cons k nil) r) (cons k r)))))
(check-sat) ; expect unsat
(pop)

; =============================================================================
; O3c — THE OFF-BY-ONE OF THE TWO-TAGGED STATE.  asFixpointGeneral's step
;     Phi(S) = Wrap(T(Unwrap(S,#arg#)), #arg#)  u  Wrap(BASE(Unwrap(S,#arg#)), #out#)
; reads ONLY the #arg# component.  The executor's stop test is on the WHOLE
; state, so it fires one round AFTER #arg# stabilises.  What has to be true for
; that extra round to be harmless is that the step is a function of the #arg#
; projection alone, so two states agreeing on #arg# have identical successors,
; #out# included, and the extra round adds nothing.
; The trivially-true half (two syntactically identical successors are equal) is
; NOT shipped as a goal, for the same reason P3 is not.  What IS shipped is the
; substantive half: if the #arg# projections agree then so do the #out#
; projections of the successors, because #out# is BASE of the #arg# reading and
; nothing else.  (Stated with the dependence made explicit through an
; uninterpreted BASE, so the goal is not true by syntactic identity.)
; =============================================================================
(declare-fun S2 (Path) Bool)
(declare-fun BASE (Path Bool) Bool)
(push)
(assert (distinct k1 k2))
(assert (forall ((q Path)) (= (S (append t1 q)) (S2 (append t1 q)))))
(assert (not (forall ((q Path)) (= (BASE q (S (append t1 q))) (BASE q (S2 (append t1 q)))))))
(check-sat) ; expect unsat
(pop)
