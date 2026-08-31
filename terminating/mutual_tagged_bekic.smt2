; =============================================================================
; O4 + O5 — THE TWO MUTUAL-RECURSION LOWERINGS.
;
; (C) `lowerMutualPassthrough` (MORKL.scala:1235-1270) collapses an SCC
; {r_1..r_m} into ONE Fixpoint over a TAGGED state
;       Psi(S) = U_i Wrap( B_i[ r_j := Unwrap(S, t_j) ], t_i )
; and projects each routine back as `r_i = Unwrap(lfp Psi, t_i)`.
; (D) `lowerMutualByElimination` (:1321-1336) takes a 2-cycle {f, g} in which g
; does NOT self-call, unfolds g into f (Gaussian elimination), and lowers the
; resulting self-recursion with `asFixpointGeneral`.
;
; Both are LEAST-FIXPOINT arguments, and neither had a certificate.  This file
; supplies both, at the LATTICE level: `leq` is an arbitrary partial order (the
; subset order on spaces), the bodies are arbitrary monotone operators, and the
; two tag operations are related to pairing by the two facts the path-algebra
; files prove:
;       pi_i(mk(x1,x2)) = x_i                          <- tagged_projection.smt2 (P1,P2,P4)
;       leq(mk(x1,x2), mk(y1,y2)) iff leq(x1,y1) and leq(x2,y2)
;                                                      <- tagged_order.smt2
; They are ASSUMED here and DISCHARGED there; that split is deliberate, because
; the path-level proof needs the `cons/nil` datatype and the lattice-level proof
; needs an abstract order, and mixing the two encodings in one file makes both
; provers time out (measured while building tagged_projection.smt2).
;
; THEOREM, part O4 (the tagged encoding is faithful).  With
;       Psi(S) = mk( B1(pi1 S, pi2 S), B2(pi1 S, pi2 S) )
;   (a) a tagged state is a fixpoint of Psi iff its two projections solve the
;       mutual system  x = B1(x,y),  y = B2(x,y);
;   (b) a tagged state mk(y1,y2) is a PRE-fixpoint of Psi iff (y1,y2) is a
;       componentwise pre-fixpoint;
;   (c) hence the least fixpoint of Psi projects to the COMPONENTWISE LEAST
;       solution — which is what `Unwrap(fix, tag(r_i))` is claimed to be.
; (b) is the load-bearing one: it is what makes "least in the tagged order"
; mean "least in each component", and it is exactly where tagged_order.smt2's
; "only if" direction (the one that needs distinct tag heads) is consumed.
;
; THEOREM, part O5 (Gaussian elimination is sound for the LEAST solution).  If
; B2 does not depend on its second argument — which is precisely the check
; `if callees(dropR.body).contains(drop) then None` at MORKL.scala:1328, "the
; dropped routine must not self-call" — then writing E for the least solution of
; the ELIMINATED equation  x = B1(x, B2(x, x)),  the least solution (R1,R2) of
; the original 2-system satisfies
;       R1 = E        and        R2 = B2(E, E).
; Both halves are proved: E-and-its-image IS a solution, and it is below every
; pre-fixpoint pair.
;
; THE NON-CLAIM, WHICH IS THE POINT OF WRITING O5 DOWN.  This is partial
; correctness with respect to the LEAST-FIXPOINT semantics ONLY.  The OPERATIONAL
; `eval` semantics is NOT preserved: GraphExecTest.scala:294-297 records that
; "naive eval of the ORIGINAL mutual recursion diverges (f({}) <-> g({}) loops);
; the lowered Fixpoint *converges* to the least fixpoint".  So the lowering can
; turn a non-terminating program into a terminating one.  That is a deliberate
; and tested improvement, not an accident — but it means `lowerMutualByElimination`
; and `lowerMutualPassthrough` may NOT be described as "meaning-preserving" with
; respect to what `eval` does to the source; only with respect to the declared
; least-fixpoint denotation.  The same non-claim belongs in the scaladoc of
; both functions (see the report's patch section).
;
; WHAT ELSE IS NOT CLAIMED.  Nothing about the SYNTACTIC gates that decide
; whether these lowerings fire (`mono` MORKL.scala:1247-1270 — and
; mono_soundness.smt2 REFUTES two of its arms), nothing about the passthrough
; test, and nothing about existence of the least fixpoint (that is O1(iv) plus
; no_infinite_descent.smt2; over a finite universe with monotone bodies it
; exists, and this file assumes the constants R1/R2/E denote it).
;
; PROVER LOG (z3 5.1.0).  All goals under 0.1 s.  The file is a pure
; partial-order encoding in the style of least_fixpoint_unique.smt2 — no `mem`,
; no extensionality, hence none of the instantiation trouble that
; fixpoint_is_lfp.smt2 documents.
; =============================================================================
(declare-sort L 0)
(declare-fun leq (L L) Bool)
(assert (forall ((x L)) (leq x x)))
(assert (forall ((x L) (y L) (z L)) (=> (and (leq x y) (leq y z)) (leq x z))))
(assert (forall ((x L) (y L)) (=> (and (leq x y) (leq y x)) (= x y))))

; --- the SCC bodies: arbitrary, monotone in both components.
(declare-fun B1 (L L) L)
(declare-fun B2 (L L) L)
(assert (forall ((x1 L) (y1 L) (x2 L) (y2 L))
  (=> (and (leq x1 x2) (leq y1 y2)) (leq (B1 x1 y1) (B1 x2 y2)))))
(assert (forall ((x1 L) (y1 L) (x2 L) (y2 L))
  (=> (and (leq x1 x2) (leq y1 y2)) (leq (B2 x1 y1) (B2 x2 y2)))))

; --- the tagged state: pairing, projection, and the order correspondence.
; Both axioms are theorems of tagged_projection.smt2 / tagged_order.smt2.
(declare-fun mk (L L) L)
(declare-fun pi1 (L) L)
(declare-fun pi2 (L) L)
(assert (forall ((x L) (y L)) (! (= (pi1 (mk x y)) x) :pattern ((mk x y)))))
(assert (forall ((x L) (y L)) (! (= (pi2 (mk x y)) y) :pattern ((mk x y)))))
(assert (forall ((x1 L) (y1 L) (x2 L) (y2 L)) (!
  (= (leq (mk x1 y1) (mk x2 y2)) (and (leq x1 x2) (leq y1 y2)))
  :pattern ((leq (mk x1 y1) (mk x2 y2))))))

; --- the combined tagged operator.
(define-fun Psi ((s L)) L (mk (B1 (pi1 s) (pi2 s)) (B2 (pi1 s) (pi2 s))))

; =============================================================================
; O4(a) — a fixpoint of Psi projects to a solution of the mutual system, and
; conversely.  (Both directions: the encoding must not lose solutions either.)
; =============================================================================
(push)
(declare-const s0 L)
(assert (= (Psi (mk (pi1 s0) (pi2 s0))) (mk (pi1 s0) (pi2 s0))))
(assert (not (and (= (B1 (pi1 s0) (pi2 s0)) (pi1 s0)) (= (B2 (pi1 s0) (pi2 s0)) (pi2 s0)))))
(check-sat) ; expect unsat
(pop)
(push)
(declare-const u1 L) (declare-const u2 L)
(assert (= (B1 u1 u2) u1))
(assert (= (B2 u1 u2) u2))
(assert (not (= (Psi (mk u1 u2)) (mk u1 u2))))
(check-sat) ; expect unsat
(pop)

; =============================================================================
; O4(b) — THE LOAD-BEARING ONE: tagged pre-fixpoint IFF componentwise
; pre-fixpoint.  This is where tagged_order.smt2's "only if" direction (which
; needs the tags to have distinct heads) is consumed.
; =============================================================================
(push)
(declare-const y1 L) (declare-const y2 L)
(assert (not (= (leq (Psi (mk y1 y2)) (mk y1 y2))
                (and (leq (B1 y1 y2) y1) (leq (B2 y1 y2) y2)))))
(check-sat) ; expect unsat
(pop)
; --- asserted with a DEMAND-DRIVEN trigger on the two component applications,
; so that "consider the tagged state mk(z1,z2)" — the step a hand proof takes
; without comment — actually happens: the goals below mention `B1 z1 z2` and
; `B2 z1 z2` but never `mk z1 z2`, and without this the tagged leastness axiom
; has nothing to match on and z3 times out at 40 s (measured).
(assert (forall ((z1 L) (z2 L)) (!
  (= (leq (Psi (mk z1 z2)) (mk z1 z2)) (and (leq (B1 z1 z2) z1) (leq (B2 z1 z2) z2)))
  :pattern ((B1 z1 z2) (B2 z1 z2)))))

; =============================================================================
; O4(c) — hence the least tagged fixpoint projects to the COMPONENTWISE LEAST
; solution.  `Sfix` is the least fixpoint of Psi among tagged states: it is a
; fixpoint, and it is below every tagged pre-fixpoint.
; =============================================================================
(declare-const Sfix L)
(assert (= (Psi Sfix) Sfix))
(assert (= (mk (pi1 Sfix) (pi2 Sfix)) Sfix))            ; Psi's output is a tagged pair
(assert (forall ((z1 L) (z2 L))
  (=> (leq (Psi (mk z1 z2)) (mk z1 z2)) (leq Sfix (mk z1 z2)))))
; --- the projections solve the system...
(push)
(assert (not (and (= (B1 (pi1 Sfix) (pi2 Sfix)) (pi1 Sfix))
                  (= (B2 (pi1 Sfix) (pi2 Sfix)) (pi2 Sfix)))))
(check-sat) ; expect unsat
(pop)
; --- ...and are componentwise below every pre-fixpoint pair.  This is the
; sentence `r_i = Unwrap(fix, tag_i)` needs.
(push)
(declare-const w1 L) (declare-const w2 L)
(assert (leq (B1 w1 w2) w1))
(assert (leq (B2 w1 w2) w2))
(assert (not (and (leq (pi1 Sfix) w1) (leq (pi2 Sfix) w2))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((z1 L) (z2 L)) (!
  (=> (and (leq (B1 z1 z2) z1) (leq (B2 z1 z2) z2)) (and (leq (pi1 Sfix) z1) (leq (pi2 Sfix) z2)))
  :pattern ((B1 z1 z2) (B2 z1 z2)))))

; =============================================================================
; O5 — GAUSSIAN ELIMINATION.  From here on B2 IGNORES ITS SECOND ARGUMENT: the
; dropped routine does not self-call (MORKL.scala:1328).  `E` is the least
; solution of the eliminated equation x = B1(x, B2(x,x)).
; =============================================================================
(assert (forall ((x L) (y L) (z L)) (! (= (B2 x y) (B2 x z)) :pattern ((B2 x y) (B2 x z)))))
(declare-const E L)
(assert (= (B1 E (B2 E E)) E))
(assert (forall ((y L)) (=> (leq (B1 y (B2 y y)) y) (leq E y))))

; --- (E, B2(E,E)) IS a solution of the original 2-system.
(push)
(assert (not (and (= (B1 E (B2 E E)) E) (= (B2 E (B2 E E)) (B2 E E)))))
(check-sat) ; expect unsat
(pop)
; asserted so that the term `B2(E, B2(E,E))` exists in the final goal's E-graph:
; without it the leastness lemmas below have nothing to match on at the pair
; (E, B2(E,E)) and the conclusion times out at 40 s (measured).
(assert (and (= (B1 E (B2 E E)) E) (= (B2 E (B2 E E)) (B2 E E))))
; --- and it is below every pre-fixpoint pair of the original 2-system, so it
; is THE least solution: eliminating g loses nothing.
(push)
(declare-const v1 L) (declare-const v2 L)
(assert (leq (B1 v1 v2) v1))
(assert (leq (B2 v1 v2) v2))
(assert (not (and (leq E v1) (leq (B2 E E) v2))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((z1 L) (z2 L)) (!
  (=> (and (leq (B1 z1 z2) z1) (leq (B2 z1 z2) z2)) (and (leq E z1) (leq (B2 E E) z2)))
  :pattern ((B1 z1 z2) (B2 z1 z2)))))
; --- CONCLUSION: the least solution of the 2-system IS (E, B2(E,E)); in
; particular the f-component of the mutual recursion equals the least solution
; of the eliminated self-recursion, which is what `lowerMutualByElimination`
; hands to `asFixpointGeneral`.
(push)
(assert (not (and (= (pi1 Sfix) E) (= (pi2 Sfix) (B2 E E)))))
(check-sat) ; expect unsat
(pop)
