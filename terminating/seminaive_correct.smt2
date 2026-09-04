; =============================================================================
; O13 — THE SEMI-NAIVE CORNERSTONE'S MISSING HALF: NAIVE == SEMI-NAIVE.
;
; `datalog-sn` (EquivPipelineTest.scala:543-551) and `pt_sn`
; (terminating/datalog_b.txt, "ANDERSEN POINTS-TO — SEMI-NAIVE") are hand-written
; semi-naive programs.  Both are shaped
;
;   r(e; all, delta) = all \/ r(e; all \/ (J(delta) \ all), J(delta) \ all)
;
; with J the one-step join `iter(e){ n, nbs -> n x \/(delta <| nbs) }` — the
; operator whose ONLY argument is the delta.  T4
; (datalog_b_seminaive_{lemmas,terminates}) proves this TERMINATES, with the
; measure mu(A,D) = 2*card(top\A) + [D != {}].  Nothing anywhere proved it
; computes the SAME ANSWER as its naive twin
;
;   r(e; all)       = all \/ r(e; all \/ J(all))
;
; which is the whole point of writing the semi-naive version.  That half is
; here, and with it the cornerstone's recursion is certified end to end.
;
; THE RECURRENCES, exactly as the two programs run them (`eval`'s Call rule
; iterates the argument tuple; MORKL.scala:284-297):
;   naive       N_0 = seed,              N_{n+1} = N_n u J(N_n)
;   semi-naive  A_0 = seed, D_0 = seed,  A_{n+1} = A_n u (J(D_n) \ A_n)
;                                        D_{n+1} = J(D_n) \ A_n
;
; THEOREM (three parts):
;   (1) A_n = N_n for EVERY n — the semi-naive state equals the naive state
;       round for round, not merely in the limit.  Consequently the two
;       programs return the same value, and by O1 (fixpoint_is_lfp.smt2) that
;       value is lfp(\R. seed u J(R)) over R >= seed.
;   (2) THE OFF-BY-ONE.  The semi-naive loop's stop test is on the WHOLE
;       argument tuple, so it cannot stop when `all` stalls: it needs one more
;       round for `delta` to empty.  Proved here: A_{n+1} = A_n  =>  D_{n+1} = {},
;       and then the state is stationary from n+1 on.  This is the semantic
;       companion of T4's `stalled_delta_empty` (datalog_b_seminaive_lemmas.smt2)
;       and of the `+ [D != {}]` term in T4's measure — the two files now agree
;       about the same extra round from the two sides, value and termination.
;   (3) LEASTNESS: every naive iterate is below every pre-fixpoint Y >= seed
;       with J(Y) subset= Y, so the common limit is the LEAST solution.
;
; THE HYPOTHESIS THAT DOES THE WORK — J IS ADDITIVE: J(X u Y) = J(X) u J(Y),
; and J({}) = {}.  Semi-naive evaluation is unsound without it, and this is not
; a technicality: additivity is precisely what lets `J(delta)` stand in for
; `J(all)` modulo what is already known.  It holds for the joins these two
; programs use because `Iteration(e; n, nbs -> Wrap(TailsUnion(Restriction(X,
; nbs)), n))` is built from Restriction and TailsUnion, both of which
; distribute over union pointwise, under an Iteration whose SOURCE (`e`) does
; not mention X — so the head-group decomposition is the same for X, Y and
; X u Y.  It is assumed as an axiom here and the assumption is DISCHARGED
; ELSEWHERE, per operator, by the universal rule certificates:
; proofs/keyfold_iter.smt2 + proofs/keyfolds.smt2 (Iteration = fold over exact
; keys), proofs/threeway_restriction_* and proofs/keys_restriction.smt2
; (Restriction), proofs/threeway_tailsunion_trie.smt2 (TailsUnion).
;
; WHAT IS NOT CLAIMED.  (a) That an ARBITRARY user-written delta operator is
; additive — the compiler does not check this, and `sn_tc`/`pt_sn` are
; hand-written, so the additivity side condition is on the AUTHOR of the
; semi-naive program, not on a pass.  Written down here so that the atlas's
; datalog-sn row can be read honestly: the naive-vs-semi-naive equality is
; certified GIVEN additivity of J, and additivity is per-program.  (b) Nothing
; about a semi-naive TRANSFORMATION: there is none in this compiler
; (`grep -rn 'semi.naive' src/main/scala` finds only comments), so there is no
; pass whose output this could certify — the obligation is about the SOURCE
; PROGRAM PAIR, and it is cited from the cornerstone that contains them.
;
; PROVER LOG (z3 5.1.0).  The file is staged the way fixpoint_is_lfp.smt2
; documents: eleven set-algebra stepping stones proved and asserted with
; demand-driven triggers BEFORE the Int-indexed chains enter the signature,
; because in incremental mode z3 must be handed each extensionality instance by
; name.  The most useful of the eleven is ANTISYMMETRY (L0) — with it every set
; EQUALITY below becomes two subset obligations, which E-matching handles;
; without it the round-n step goals do not close inside 240 s.
; =============================================================================
(declare-sort Node 0)
(declare-sort NSet 0)
(declare-fun mem (Node NSet) Bool)
(declare-fun subset (NSet NSet) Bool)
(declare-fun cup (NSet NSet) NSet)
(declare-fun setminus (NSet NSet) NSet)
(declare-const empty NSet)
(assert (forall ((x Node) (a NSet) (b NSet)) (= (mem x (cup a b)) (or (mem x a) (mem x b)))))
(assert (forall ((x Node) (a NSet) (b NSet)) (= (mem x (setminus a b)) (and (mem x a) (not (mem x b))))))
(assert (forall ((a NSet) (b NSet)) (= (subset a b) (forall ((x Node)) (=> (mem x a) (mem x b))))))
(assert (forall ((a NSet) (b NSet)) (=> (forall ((x Node)) (= (mem x a) (mem x b))) (= a b))))
(assert (forall ((x Node)) (not (mem x empty))))

; =============================================================================
; SET-ALGEBRA STEPPING STONES — each PROVED here, then asserted with a
; demand-driven trigger.  L0 (antisymmetry) is the one that makes the rest work.
; =============================================================================
; --- L0 antisymmetry: mutual inclusion is equality.  (The extensionality
; instance; every equality goal below is discharged through it.)
(push)
(assert (not (forall ((a NSet) (b NSet)) (=> (and (subset a b) (subset b a)) (= a b)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet)) (!
  (=> (and (subset a b) (subset b a)) (= a b)) :pattern ((subset a b) (subset b a)))))
; --- L1 reflexivity.
(push)
(assert (not (forall ((a NSet)) (subset a a))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet)) (! (subset a a) :pattern ((subset a a)))))
; --- L2 transitivity.
(push)
(assert (not (forall ((a NSet) (b NSet) (c NSet)) (=> (and (subset a b) (subset b c)) (subset a c)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet) (c NSet)) (!
  (=> (and (subset a b) (subset b c)) (subset a c)) :pattern ((subset a b) (subset b c)))))
; --- L3 absorption: a subset= b  =>  a u b = b.
(push)
(assert (not (forall ((a NSet) (b NSet)) (=> (subset a b) (= (cup a b) b)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet)) (! (=> (subset a b) (= (cup a b) b)) :pattern ((cup a b)))))
; --- L4 the two union injections.
(push)
(assert (not (forall ((a NSet) (b NSet)) (and (subset a (cup a b)) (subset b (cup a b))))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet)) (!
  (and (subset a (cup a b)) (subset b (cup a b))) :pattern ((cup a b)))))
; --- L5 union is the least upper bound.
(push)
(assert (not (forall ((a NSet) (b NSet) (c NSet))
  (=> (and (subset a c) (subset b c)) (subset (cup a b) c)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet) (c NSet)) (!
  (=> (and (subset a c) (subset b c)) (subset (cup a b) c)) :pattern ((cup a b) (subset a c)))))
; --- L6 difference is below its minuend.
(push)
(assert (not (forall ((a NSet) (b NSet)) (subset (setminus a b) a))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet)) (! (subset (setminus a b) a) :pattern ((setminus a b)))))
; --- L7 THE SEMI-NAIVE IDENTITY at the set level: adding "the new part" is the
; same as adding the whole thing.  a u (b \ a) = a u b.  This is what turns
; `A_n u (J(D_n) \ A_n)` into `A_n u J(D_n)` in every step goal below.
(push)
(assert (not (forall ((a NSet) (b NSet)) (= (cup a (setminus b a)) (cup a b)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet)) (!
  (= (cup a (setminus b a)) (cup a b)) :pattern ((cup a (setminus b a))))))
; --- L8 a difference below its subtrahend is empty (the delta-stalls lemma at
; the set level; the same statement datalog_b_seminaive_lemmas.smt2 needed).
(push)
(assert (not (forall ((a NSet) (b NSet)) (=> (subset b a) (= (setminus b a) empty)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet)) (!
  (=> (subset b a) (= (setminus b a) empty)) :pattern ((setminus b a)))))

; --- L9/L10 the two EMPTY units the "stationary from n+1" goal needs:
; {} \ a = {} and a u {} = a.
(push)
(assert (not (forall ((a NSet)) (= (setminus empty a) empty))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet)) (! (= (setminus empty a) empty) :pattern ((setminus empty a)))))
(push)
(assert (not (forall ((a NSet)) (= (cup a empty) a))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet)) (! (= (cup a empty) a) :pattern ((cup a empty)))))

; =============================================================================
; THE JOIN OPERATOR.  Uninterpreted except for ADDITIVITY and strictness — the
; two properties semi-naive evaluation actually needs (see the header for how
; each is discharged per operator by the proofs/ rule certificates).
; =============================================================================
(declare-fun J (NSet) NSet)
(assert (forall ((x NSet) (y NSet)) (! (= (J (cup x y)) (cup (J x) (J y))) :pattern ((J (cup x y))))))
(assert (= (J empty) empty))
; --- additivity implies monotonicity.  The goal deliberately carries the
; ABSORPTION CONJUNCT `x u y = y` alongside the conclusion: without it the term
; `(cup x y)` never enters the E-graph, the additivity axiom's trigger
; `(J (cup x y))` never fires, and z3 times out at 240 s (measured).  With it
; the goal closes immediately; only the monotonicity half is then asserted.
(push)
(assert (not (forall ((x NSet) (y NSet))
  (=> (subset x y) (and (= (cup x y) y) (subset (J x) (J y)))))))
(check-sat) ; expect unsat
(pop)
; PREMISE: F is monotone (as fixpoint_is_lfp.smt2; O3d)
(assert (forall ((x NSet) (y NSet)) (! (=> (subset x y) (subset (J x) (J y))) :pattern ((J x) (J y)))))

; =============================================================================
; THE TWO CHAINS.  P_n is the PREVIOUS naive state (P_0 = {}), carried so the
; invariant "N_n = P_n u D_n" can be stated without subtraction.
; =============================================================================
(declare-const seed NSet)
(declare-fun N (Int) NSet)                                     ; naive       `all`
(declare-fun A (Int) NSet)                                     ; semi-naive  `all`
(declare-fun D (Int) NSet)                                     ; semi-naive  `delta`
(declare-fun P (Int) NSet)                                     ; N_{n-1}, with P_0 = {}
(assert (= (N 0) seed))
(assert (forall ((n Int)) (! (=> (>= n 0) (= (N (+ n 1)) (cup (N n) (J (N n))))) :pattern ((N (+ n 1))))))
(assert (= (A 0) seed))
(assert (forall ((n Int)) (!
  (=> (>= n 0) (= (A (+ n 1)) (cup (A n) (setminus (J (D n)) (A n))))) :pattern ((A (+ n 1))))))
(assert (= (D 0) seed))
(assert (forall ((n Int)) (!
  (=> (>= n 0) (= (D (+ n 1)) (setminus (J (D n)) (A n)))) :pattern ((D (+ n 1))))))
(assert (= (P 0) empty))
(assert (forall ((n Int)) (! (=> (>= n 0) (= (P (+ n 1)) (N n))) :pattern ((P (+ n 1))))))

; =============================================================================
; (1) A_n = N_n, by simultaneous induction on the three invariants
;       Inv1: A_n = N_n            Inv2: N_n = P_n u D_n        Inv3: J(P_n) subset= N_n
; Inv2 and Inv3 are what make the step go through: they are the standard
; semi-naive invariants "the delta is exactly the newest layer" and "everything
; derivable from the OLD layer is already known".
; =============================================================================
; --- base: all three at n = 0.  N_0 = seed = A_0; P_0 u D_0 = {} u seed = seed;
; J(P_0) = J({}) = {} subset= N_0.  (This is where strictness J({}) = {} is used.)
(push)
(assert (not (and (= (A 0) (N 0)) (= (N 0) (cup (P 0) (D 0))) (subset (J (P 0)) (N 0)))))
(check-sat) ; expect unsat
(pop)
; --- step.
(push)
(declare-const k0 Int)
(assert (>= k0 0))
(assert (= (A k0) (N k0)))
(assert (= (N k0) (cup (P k0) (D k0))))
(assert (subset (J (P k0)) (N k0)))
(assert (not (and (= (A (+ k0 1)) (N (+ k0 1)))
                  (= (N (+ k0 1)) (cup (P (+ k0 1)) (D (+ k0 1))))
                  (subset (J (P (+ k0 1))) (N (+ k0 1))))))
(check-sat) ; expect unsat
(pop)
; --- BRIDGE (the induction principle; base and step above are its premises).
; ASSUMED: T8
(assert (forall ((n Int)) (!
  (=> (>= n 0) (and (= (A n) (N n)) (= (N n) (cup (P n) (D n))) (subset (J (P n)) (N n))))
  :pattern ((N n)))))

; =============================================================================
; (2) THE OFF-BY-ONE: once `all` stalls, `delta` is empty on the NEXT round and
; the whole state is stationary from there.  The semi-naive loop therefore runs
; exactly one round more than the naive one — which is what T4's measure
; 2*card(top\A) + [D != {}] pays for.
; =============================================================================
; --- a stalled `all` forces the next delta empty.
(push)
(declare-const k1 Int)
(assert (>= k1 0))
(assert (= (A (+ k1 1)) (A k1)))
(assert (not (= (D (+ k1 1)) empty)))
(check-sat) ; expect unsat
(pop)
; --- and then the state does not move again: A_{n+2} = A_{n+1}, D_{n+2} = {}.
(push)
(declare-const k2 Int)
(assert (>= k2 0))
(assert (= (D (+ k2 1)) empty))
(assert (not (and (= (A (+ k2 2)) (A (+ k2 1))) (= (D (+ k2 2)) empty))))
(check-sat) ; expect unsat
(pop)

; =============================================================================
; (3) LEASTNESS: every naive iterate — hence every semi-naive `all` — is below
; every pre-fixpoint above the seed.  With O1's (iii) this makes the common
; limit THE least fixpoint, not merely A fixpoint.
; =============================================================================
(push)
(assert (not (forall ((y NSet)) (=> (and (subset seed y) (subset (J y) y)) (subset (N 0) y)))))
(check-sat) ; expect unsat
(pop)
(push)
(declare-const k3 Int)
(assert (>= k3 0))
(assert (forall ((y NSet)) (=> (and (subset seed y) (subset (J y) y)) (subset (N k3) y))))
(assert (not (forall ((y NSet)) (=> (and (subset seed y) (subset (J y) y)) (subset (N (+ k3 1)) y)))))
(check-sat) ; expect unsat
(pop)
; ASSUMED: T8
(assert (forall ((n Int) (y NSet)) (!
  (=> (and (>= n 0) (subset seed y) (subset (J y) y)) (subset (N n) y))
  :pattern ((N n) (J y)))))
; --- and every naive iterate is ABOVE the seed (base, step, bridge) - the other
; half of "the limit is the least fixpoint ABOVE seed".
(push)
(assert (not (subset seed (N 0))))
(check-sat) ; expect unsat
(pop)
(push)
(declare-const k4 Int)
(assert (>= k4 0))
(assert (subset seed (N k4)))
(assert (not (subset seed (N (+ k4 1)))))
(check-sat) ; expect unsat
(pop)
; ASSUMED: T8
(assert (forall ((n Int)) (! (=> (>= n 0) (subset seed (N n))) :pattern ((N n)))))

; --- CONCLUSION: at a stationary index the semi-naive `all` IS the least
; solution of R = seed u J(R) above the seed.
(push)
(declare-const n0 Int)
(assert (>= n0 0))
(assert (= (N (+ n0 1)) (N n0)))
(assert (not (and (= (A n0) (N n0))
                  (subset (J (N n0)) (N n0))
                  (subset seed (N n0))
                  (forall ((y NSet)) (=> (and (subset seed y) (subset (J y) y)) (subset (A n0) y))))))
(check-sat) ; expect unsat
(pop)
