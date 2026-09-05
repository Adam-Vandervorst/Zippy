; =============================================================================
; O1 — WHAT `Space.Fixpoint` ACTUALLY COMPUTES.  The foundation the whole
; recursion-lowering surface stands on; before this file the corpus proved only
; that particular recurrences TERMINATE, never what their limit IS.
;
; The operational rule (MORKL.scala:333-341 `eval`, :652-670 `exec`/`execT`,
; EquivPipeline.scala:75-84 `expand`) is, for `Fixpoint(init, rec, body)` with
; F := \X. [[body]][rec := X]:
;
;     cur := I; acc := I
;     loop: nxt := F(cur) ; if nxt = cur then return acc
;           acc := acc u nxt; cur := nxt
;
; so with  C_0 = I,  C_{k+1} = F(C_k)  (the KLEENE chain) the returned value is
; the ACCUMULATOR  A_n = U_{j<=n} C_j  at the least n with C_{n+1} = C_n - NOT
; C_n, and the two are equal only when the chain ascends.  Everything the
; lowering passes assume (asFixpoint MORKL.scala:1214, asFixpointGeneral :1279,
; lowerMutualPassthrough :1235, SpatialRecursion's Kleene tier) is a statement
; about the LEAST FIXPOINT, so the gap between "the accumulator" and "the least
; fixpoint" has to be closed exactly once, here.
;
; THEOREM (four parts, each an explicit induction in the style of
; no_infinite_descent.smt2 - base, step, then the bridging induction principle
; asserted, exactly as a hand proof invokes it):
;   (i)   MONOTONE F and I subset= F(I)  =>  the Kleene chain ASCENDS;
;   (ii)  under (i)                      =>  A_k = C_k for every k (the
;         accumulator is redundant - this is what licenses reading the loop's
;         result as "the k-th Kleene iterate");
;   (iii) if C_{n+1} = C_n then A_n is a fixpoint of F, contains I, and is
;         BELOW EVERY pre-fixpoint Y >= I (subset(F Y, Y)) - i.e. A_n = lfp_{>=I} F;
;   (iv)  over a FINITE universe `top` the stopping n EXISTS: every non-
;         stationary step strictly shrinks card(top \ C_k), which combined with
;         no_infinite_descent.smt2 (no everywhere-decreasing N->N function)
;         forbids an infinite run.  (iv) is the same measure argument as T1
;         bounded_growth_decrease / T2 datalog_a_terminates, restated on the
;         GENERAL Kleene chain rather than on the inflationary shape
;         R |-> R u f(R): T2's operator is inflationary BY CONSTRUCTION, which
;         is precisely what asFixpointGeneral's and lowerMutualPassthrough's
;         operators do NOT satisfy syntactically (their `#arg#` component is
;         REPLACED, not unioned, each round).
;
; WHY BOTH HYPOTHESES ARE NEEDED, and what is NOT claimed:
;   * MONOTONICITY is not decorative.  It is discharged in the compiler by the
;     syntactic gates `monoIn` (MORKL.scala:1284-1307) and `mono` (:1249-1263);
;     their soundness is a SEPARATE obligation (mono_soundness.smt2, O3d/O4b) -
;     this file assumes semantic monotonicity as an axiom and says so.
;   * I subset= F(I) is equally load-bearing for (i)/(ii): the monotone-but-not-
;     inflationary operator F(X) = {b if a in X} u {c if a in X and b in X},
;     I = {a} has A_2 = {a,b,c} while U_{j<=2} C_j = {a,b}.  That counterexample
;     is MACHINE-CHECKED in unroll_vs_kleene.smt2 (O10), which is where the
;     accumulator-vs-chain distinction becomes a live compiler question rather
;     than a bookkeeping point.
;   * NOT CLAIMED: that the *implementation's* `nxt == cur` test finds the least
;     such n (it does, the chain being deterministic, but the loop is not
;     modelled here as a program), and nothing about WHAT F is - F is completely
;     uninterpreted, exactly as `frontier` is in reachable_decrease.p.
;
; PROVER LOG (z3 5.1.0, vampire 5.1.0 - both are run by terminating/run.sh).
; Three things had to be got right before z3 would close this file at all; all
; three are recorded because a future edit that undoes any of them will look
; harmless and will silently re-break the file:
;   1. FILE ORDER.  The four set-algebra stepping stones are proved and asserted
;      BEFORE `C`/`A`/`Int` enter the signature.  In the presence of the
;      Int-indexed chain z3 needs MBQI to guess the extensionality instances,
;      cannot build a model over the infinite index domain, and spins:
;      measured, the absorption goal alone goes from 0.01 s to a >60 s timeout
;      purely by moving `(assert (= (C 0) init))` above it.  (`smt.mbqi=false`
;      turns that timeout into an immediate `unknown` - i.e. E-matching alone
;      cannot find the instance; the stepping stones are what make E-matching
;      sufficient.)
;   2. `top` IS AXIOMATISED AS A SUPERSET (`forall a. subset(a, top)`), not
;      pointwise as `forall x. mem(x, top)`.  The pointwise form makes every
;      extensionality skolem interact with the universe axiom; measured, it
;      alone reintroduced the >60 s timeout.  The two forms are equivalent given
;      subset_def, and only the superset form is ever used below.
;   3. EXPLICIT TRIGGERS on every axiom that can MANUFACTURE a term.  The
;      C-recurrence with its default trigger `(C n)` produces `(C (+ n 1))`,
;      which matches again, forever.  Each pattern below is DEMAND-DRIVEN - it
;      fires only on a term the goal already mentions - so no goal is weakened.
;
;   4. THE MEASURE LEMMA IS PROVED BEFORE `cup` EXISTS.  Its proof needs the
;      extensionality WITNESS (`subset(r,s) and s != r  =>  some w in s \ r`),
;      and the mem-axiom for `cup` derails that search: measured, the identical
;      goal is 0.04 s with `cup` absent from the signature and >20 s (timeout)
;      with `mem(x, cup(a,b))` asserted.  Once proved and asserted with a
;      trigger it is immune, so `cup` is only introduced afterwards.
;
; NON-VACUITY, AND EXACTLY HOW FAR IT WAS CHECKED.  A staged file whose axioms
; are contradictory proves everything, so this matters.  What is true:
;   * the four stepping stones are each PROVED from the axioms above them before
;     being asserted, so nothing is assumed here that is not also checked;
;   * the C/A axioms are a PRIMITIVE-RECURSIVE definition over the naturals from
;     data already in the signature - a definitional extension, which cannot
;     introduce an inconsistency the set axioms did not already have;
;   * a canary query (`z3 -T:20` on this file's depth-0 axioms plus
;     `(assert (not (= (C 1) (C 0))))`, a NON-consequence) answers `timeout`,
;     NOT `unsat` - if the axiom set were contradictory it would answer `unsat`
;     with the same ease it refutes the goals below (all under 0.1 s each).
; What is NOT true, and is recorded rather than papered over: z3 cannot build a
; MODEL of an extensional set signature, so `(check-sat)` on the axioms alone
; answers `timeout`, not `sat`.  The decisive non-vacuity witness for this
; vocabulary lives in unroll_vs_kleene.smt2's fourth section, which re-runs its
; claims in a decidable, axiom-free (_ BitVec 3) encoding.
; =============================================================================
(declare-sort Node 0)
(declare-sort NSet 0)
(declare-fun mem (Node NSet) Bool)
(declare-fun subset (NSet NSet) Bool)
(declare-fun setminus (NSet NSet) NSet)
(declare-fun card (NSet) Int)

; --- membership semantics, subset, extensionality: the corpus vocabulary of
; reachable_decrease.p / scc_decrease.p, unchanged.  `cup` and `top` are
; DELIBERATELY NOT DECLARED YET - see log item 4.
(assert (forall ((x Node) (a NSet) (b NSet)) (= (mem x (setminus a b)) (and (mem x a) (not (mem x b))))))
(assert (forall ((a NSet) (b NSet)) (= (subset a b) (forall ((x Node)) (=> (mem x a) (mem x b))))))
(assert (forall ((a NSet) (b NSet)) (=> (forall ((x Node)) (= (mem x a) (mem x b))) (= a b))))
; ASSUMED: T7
(assert (forall ((a NSet)) (>= (card a) 0)))
; NOTE: card_strict_decrease deliberately carries NO explicit trigger.  Pinning
; it to `((subset a b) (mem w b))` blocks the witness instantiation S1 needs and
; makes S1 time out at 60 s (measured); z3's own trigger for it is correct.
; ASSUMED: T7
(assert (forall ((a NSet) (b NSet) (w Node))
  (=> (and (subset a b) (mem w b) (not (mem w a))) (< (card a) (card b)))))

; =============================================================================
; S1 = T1 bounded_growth_decrease, PROVED FIRST, while `cup` is still absent
; from the signature (log item 4), then asserted with a demand-driven trigger:
; strict growth inside a finite universe strictly shrinks the complement.
; =============================================================================
(push)
(assert (not (forall ((r NSet) (s NSet) (u NSet))
  (=> (and (subset r s) (subset s u) (distinct s r))
      (< (card (setminus u s)) (card (setminus u r)))))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((r NSet) (s NSet) (u NSet)) (!
  (=> (and (subset r s) (subset s u) (distinct s r))
      (< (card (setminus u s)) (card (setminus u r))))
  :pattern ((setminus u s) (setminus u r)))))

; --- only now the union and the universe.
(declare-fun cup (NSet NSet) NSet)
(declare-const top NSet)
(assert (forall ((x Node) (a NSet) (b NSet)) (= (mem x (cup a b)) (or (mem x a) (mem x b)))))
(assert (forall ((a NSet)) (subset a top)))                        ; the universe (log item 2)

; =============================================================================
; MORE SET-ALGEBRA STEPPING STONES.  Each is PROVED here from the axioms above
; and only then asserted with an explicit trigger.  They exist so that every
; goal after the chain is introduced is closable by E-MATCHING ALONE (log 1).
; =============================================================================
; --- S2 absorption: a subset= b  =>  a u b = b.  (The extensionality instance
; the `A_{k+1} = C_{k+1}` step needs and cannot find for itself.)
(push)
(assert (not (forall ((a NSet) (b NSet)) (=> (subset a b) (= (cup a b) b)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet)) (! (=> (subset a b) (= (cup a b) b)) :pattern ((cup a b)))))

; --- S3 reflexivity, S4 transitivity of subset (used by the "every iterate is
; above I" and "every iterate is below every pre-fixpoint" inductions).
(push)
(assert (not (forall ((a NSet)) (subset a a))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet)) (! (subset a a) :pattern ((subset a a)))))
(push)
(assert (not (forall ((a NSet) (b NSet) (c NSet)) (=> (and (subset a b) (subset b c)) (subset a c)))))
(check-sat) ; expect unsat
(pop)
(assert (forall ((a NSet) (b NSet) (c NSet)) (!
  (=> (and (subset a b) (subset b c)) (subset a c)) :pattern ((subset a b) (subset b c)))))

; =============================================================================
; THE OPERATOR AND THE TWO CHAINS.  F is UNINTERPRETED: nothing below may use,
; and nothing below does use, what a body actually computes.
; =============================================================================
(declare-fun F (NSet) NSet)
(declare-const init NSet)
; PREMISE: F is monotone — discharged by the syntactic gate MORKL.mono/monoIn/monotoneInMention, whose soundness is terminating/mono_soundness.smt2 (O3d), and mechanized as Zippy.Space.denT_mono (Positive.lean)
(assert (forall ((x NSet) (y NSet)) (!
  (=> (subset x y) (subset (F x) (F y))) :pattern ((F x) (F y)))))            ; MONOTONE
; PREMISE: init ⊆ F(init) — holds BY CONSTRUCTION for Space.Fixpoint (the iterated operator is X ↦ init ∪ body[rec := X])
(assert (subset init (F init)))                                               ; INFLATIONARY AT I

(declare-fun C (Int) NSet)                                    ; C_k = `cur` after k rounds
(declare-fun A (Int) NSet)                                    ; A_k = `acc` after k rounds
(assert (= (C 0) init))
(assert (forall ((n Int)) (! (=> (>= n 0) (= (C (+ n 1)) (F (C n)))) :pattern ((C (+ n 1))))))
(assert (= (A 0) init))
(assert (forall ((n Int)) (!
  (=> (>= n 0) (= (A (+ n 1)) (cup (A n) (C (+ n 1))))) :pattern ((A (+ n 1))))))

; -----------------------------------------------------------------------------
; DISCHARGED.  The FOUR bridging induction principles this file
; asserts -- the four `(assert (forall ((n Int)) ...))` lines below -- are
; THEOREMS in Lean, where induction over the chain index is `Nat.rec`:
;
;   (i)     chain_ascends            forall n. C n subset C (n+1)
;   (ii)    acc_eq_chain             forall n. A n = C n
;   (iii-a) init_subset_chain        forall n. init subset C n
;   (iii-b) chain_below_prefixpoint  forall n y. init<=y and F y<=y => C n <= y
;
; and so is the CONCLUSION they exist for, `stationary_is_lfp`: at a stationary
; index the returned accumulator IS lfp_{>=init} F.  Both side conditions
; (monotone F, init subset F init) are explicit parameters of every one of them,
; so none can be read as unconditional -- which is what this file's
; monotone-but-non-inflationary counterexample at :47-50 is about.
;
; NOT DISCHARGED, and the Lean file says so in the same words: part (iv), that
; over a finite universe the stationary index EXISTS.  It is not one of the four
; -- it is a single `card` check whose bridging principle lives in
; no_infinite_descent.smt2 -- and it is a well-foundedness claim needing a
; finiteness hypothesis that none of the four needs.  `stationary_is_lfp` takes
; the stationary index as a HYPOTHESIS for exactly that reason.
;
; MECHANIZED-IN: proofs/lean/Zippy/Fixpoint.lean#Zippy.Kleene.stationary_is_lfp
; -----------------------------------------------------------------------------

; =============================================================================
; (i) the Kleene chain ASCENDS - induction on k.
; =============================================================================
; --- base: C_0 subset= C_1, i.e. init subset= F(init) - the hypothesis itself.
(push)
(assert (not (subset (C 0) (C 1))))
(check-sat) ; expect unsat
(pop)
; --- step: C_k subset= C_{k+1}  =>  C_{k+1} subset= C_{k+2}, by monotonicity.
(push)
(declare-const k0 Int)
(assert (>= k0 0))
(assert (subset (C k0) (C (+ k0 1))))
(assert (not (subset (C (+ k0 1)) (C (+ k0 2)))))
(check-sat) ; expect unsat
(pop)
; --- BRIDGE (the induction principle, asserted exactly as a hand proof invokes
; it; the base and step above are its two machine-checked premises).
; ASSUMED: T2
(assert (forall ((n Int)) (! (=> (>= n 0) (subset (C n) (C (+ n 1)))) :pattern ((C (+ n 1))))))

; =============================================================================
; (ii) the accumulator is REDUNDANT on an ascending chain: A_k = C_k.
; =============================================================================
(push)
(assert (not (= (A 0) (C 0))))
(check-sat) ; expect unsat
(pop)
; --- step: A_k = C_k  =>  A_{k+1} = A_k u C_{k+1} = C_k u C_{k+1} = C_{k+1}.
; This is where ASCENDING earns its keep: without C_k subset= C_{k+1} the union
; does not collapse and A_k = C_k is FALSE (header, and O10).
(push)
(declare-const k1 Int)
(assert (>= k1 0))
(assert (= (A k1) (C k1)))
(assert (not (= (A (+ k1 1)) (C (+ k1 1)))))
(check-sat) ; expect unsat
(pop)
; ASSUMED: T2
(assert (forall ((n Int)) (! (=> (>= n 0) (= (A n) (C n))) :pattern ((A n)))))

; =============================================================================
; (iii) the stationary point IS the least fixpoint above I.
; =============================================================================
; --- every iterate is above I - induction (base, then a transitivity step).
(push)
(assert (not (subset init (C 0))))
(check-sat) ; expect unsat
(pop)
(push)
(declare-const k2 Int)
(assert (>= k2 0))
(assert (subset init (C k2)))
(assert (not (subset init (C (+ k2 1)))))
(check-sat) ; expect unsat
(pop)
; ASSUMED: T2
(assert (forall ((n Int)) (! (=> (>= n 0) (subset init (C n))) :pattern ((C n)))))

; --- every iterate is below every pre-fixpoint Y >= I - induction on k with Y
; UNIVERSALLY QUANTIFIED, so the conclusion is genuinely "least" and not "least
; among some enumerated candidates".
(push)
(assert (not (forall ((y NSet)) (=> (and (subset init y) (subset (F y) y)) (subset (C 0) y)))))
(check-sat) ; expect unsat
(pop)
(push)
(declare-const k3 Int)
(assert (>= k3 0))
(assert (forall ((y NSet)) (=> (and (subset init y) (subset (F y) y)) (subset (C k3) y))))
(assert (not (forall ((y NSet)) (=> (and (subset init y) (subset (F y) y)) (subset (C (+ k3 1)) y)))))
(check-sat) ; expect unsat
(pop)
; ASSUMED: T2
(assert (forall ((n Int) (y NSet)) (!
  (=> (and (>= n 0) (subset init y) (subset (F y) y)) (subset (C n) y))
  :pattern ((C n) (F y)))))

; --- CONCLUSION of (iii): at a stationary index n the RETURNED value A_n is a
; fixpoint of F, contains I, and is contained in every pre-fixpoint above I -
; i.e. A_n = lfp_{>=I} F.  This is the statement every lowering pass cites.
(push)
(declare-const n0 Int)
(assert (>= n0 0))
(assert (= (C (+ n0 1)) (C n0)))
(assert (not (and (= (F (A n0)) (A n0))
                  (subset init (A n0))
                  (forall ((y NSet)) (=> (and (subset init y) (subset (F y) y)) (subset (A n0) y))))))
(check-sat) ; expect unsat
(pop)

; =============================================================================
; (iv) over a FINITE universe the stationary index EXISTS: every non-stationary
; step strictly shrinks card(top \ C_k).  Combined with no_infinite_descent.smt2
; this forbids an infinite run - the same dependent-choice glue spelled out in
; reachable_decrease.p / scc_decrease.p.  Finiteness enters ONLY through
; card_strict_decrease + card_nonneg; no cardinality of `top` is assumed.
; =============================================================================
(push)
(declare-const k4 Int)
(assert (>= k4 0))
(assert (distinct (C (+ k4 1)) (C k4)))
(assert (not (< (card (setminus top (C (+ k4 1)))) (card (setminus top (C k4))))))
(check-sat) ; expect unsat
(pop)
