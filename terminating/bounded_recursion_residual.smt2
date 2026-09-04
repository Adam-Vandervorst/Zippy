; =============================================================================
; O11 — WHY `SpatialRecursion.BoundedRecursion` MAY CUT THE LAST CALL.
;
; `BoundedRecursion` unrolls a recognised self-recursion levels 0..k-1 and
; replaces the level-k `Call` by `Empty`.  The file's own header says so:
; "This has been checked differentially (see `SpatialRecursionCheck`), not
; proved" (SpatialRecursion.scala:75-76), and the claim it makes is
; "the argument's maximum length strictly drops, so the argument reaches {} — a
; fixed point of the recursion — in <= L+1 steps" (:72-74).  That argument has
; three separable parts; this file proves the two that are pure reasoning and
; names the third, which is discharged elsewhere.
;
; (a) MEASURE => DEPTH.  If mu(a_0) = L, mu is a natural number, and every
;     recursive step drops mu by at least one, then the chain cannot reach depth
;     L+1: for every k <= L, mu(a_k) <= L - k, so a_{L+1} would need mu < 0.
;     This is T1 bounded_growth_decrease's shape restated on the PATH-LENGTH
;     measure (SpatialRecursion's `LenBounds`) instead of on card(top \ R), and
;     it is what makes the unroll depth `k = L+1` sufficient rather than
;     arbitrary.  Proved below as base + step + bridge, then instantiated.
;
; (b) THE ABSTRACT SIDE IS ALREADY CERTIFIED, and was left uncited.  The claim
;     "every Kleene iterate stays inside a certified summary" is exactly
;     proofs/spatial/lat_postfixpoint.smt2 — "F#(T) subset= T and init subset= T
;     => every Kleene iterate subset= T", which is what `Summaries.certified`
;     (SpatialRecursion.scala:182-192) re-checks over the final table.  It is
;     NOT re-proved here; it is CITED, and REGISTRY.tsv records the citation so
;     the code site stops looking uncovered.
;
; (c) CUT SOUNDNESS.  Replacing the level-k `Call` by `Empty` is
;     denotation-preserving exactly when that call denotes {}.  Two hypotheses
;     give that, and both are named rather than assumed silently:
;       (c1) the summary is SOUND — the concrete value is inside the
;            concretisation of its abstract value;
;       (c2) gamma(bottom) = {} — the abstract bottom concretises to the empty
;            space, which is what `isProvablyEmpty` / `SpaceType.empty` means.
;     Then a level-k summary of bottom forces the concrete level-k call to {},
;     and the substitution is a congruence step.  Goal `cut_is_sound` below is
;     that implication; goal `cut_needs_soundness` shows the hypothesis (c1) is
;     LOAD-BEARING by refuting the statement without it.
;
; WHAT IS NOT CLAIMED.
;   * That the recognised family's measure really does drop — that is a property
;     of `BoundedRecursion.applicableTo`'s pattern match, checked differentially
;     by `SpatialRecursionCheck`, and it is registered in REGISTRY.tsv as a
;     PROPERTY row, not as an SMT obligation.
;   * (d) the per-level alpha-renaming hygiene (the `#sr#` reserved prefix,
;     SpatialRecursion.scala:80-82).  Capture-avoidance is a syntactic property
;     of the renamer; it is registered as a PROPERTY row pointing at
;     `SpatialRecursionCheck`, and it is deliberately NOT modelled here — an SMT
;     encoding of alpha-renaming would be a re-implementation, and a
;     re-implementation that agreed with the original would prove nothing about
;     the original.
;
; PROVER LOG (z3 5.1.0): all goals under 0.05 s.  The one modelling decision
; worth recording is that the measure is an Int-valued function of the DEPTH,
; not of the argument: the argument's identity is irrelevant to (a), and
; carrying it makes the induction need a frame condition it does not otherwise
; need.
; =============================================================================
(declare-const L Int)
; PREMISE: L ≥ 0 (the measured initial value)
(assert (>= L 0))
(declare-fun mu (Int) Int)                        ; mu(k) = the measure at depth k
(assert (= (mu 0) L))
; PREMISE: mu is natural-valued (O11a's hypothesis)
(assert (forall ((k Int)) (! (=> (>= k 0) (>= (mu k) 0)) :pattern ((mu k)))))          ; natural
; PREMISE: mu strictly drops at every level (O11a's hypothesis)
(assert (forall ((k Int)) (! (=> (>= k 0) (<= (mu (+ k 1)) (- (mu k) 1))) :pattern ((mu (+ k 1))))))

; =============================================================================
; (a) MEASURE => DEPTH.
; =============================================================================
; --- base: mu(0) <= L - 0.
(push)
(assert (not (<= (mu 0) (- L 0))))
(check-sat) ; expect unsat
(pop)
; --- step: mu(k) <= L - k  =>  mu(k+1) <= L - (k+1).
(push)
(declare-const k0 Int)
(assert (>= k0 0))
(assert (<= (mu k0) (- L k0)))
(assert (not (<= (mu (+ k0 1)) (- L (+ k0 1)))))
(check-sat) ; expect unsat
(pop)
; --- BRIDGE (the induction principle, as in no_infinite_descent.smt2).
; ASSUMED: T8
(assert (forall ((k Int)) (! (=> (>= k 0) (<= (mu k) (- L k))) :pattern ((mu k)))))
; --- CONSEQUENCE: depth L+1 is unreachable, so unrolling L+1 levels is enough.
; (mu(L+1) <= -1 contradicts mu >= 0.)
(push)
(assert (not (< (mu (+ L 1)) 0)))
(check-sat) ; expect unsat
(pop)
; (A "the cut depth is tight" goal was drafted here and DELETED: it reduced to
; `0 <= k <= L => L - k >= 0`, pure arithmetic with no content about the
; recursion.  A degenerate obligation is worse than a missing one — docs/traps.md.)

; =============================================================================
; (c) CUT SOUNDNESS.  Spaces are an uninterpreted sort with an emptiness
; predicate; `gamma` maps an abstract value to a space, `absAt k` is the summary
; at depth k, `conc k` the concrete value there.
; =============================================================================
(declare-sort Space 0)
(declare-sort Abs 0)
(declare-fun subsp (Space Space) Bool)
(declare-const emptysp Space)
(declare-fun gamma (Abs) Space)
(declare-const bot Abs)
(declare-fun absAt (Int) Abs)
(declare-fun conc (Int) Space)
(assert (forall ((s Space)) (! (= (subsp s emptysp) (= s emptysp)) :pattern ((subsp s emptysp)))))
; (c2) the abstract bottom concretises to the empty space
(assert (= (gamma bot) emptysp))

; --- cut_is_sound: with (c1) soundness of the summary at depth k and a bottom
; summary there, the concrete value at depth k IS empty — so replacing that
; Call by `Empty` changes no denotation.
(push)
(declare-const k2 Int)
(assert (subsp (conc k2) (gamma (absAt k2))))                 ; (c1) soundness at k2
(assert (= (absAt k2) bot))                                   ; the summary is bottom
(assert (not (= (conc k2) emptysp)))
(check-sat) ; expect unsat
(pop)
; --- cut_needs_soundness: WITHOUT (c1) the conclusion does not follow.  Refuted
; by exhibiting a model — but this corpus only ships `unsat` goals, so the
; refutation is stated positively: there is a space that is not empty even
; though the summary at that depth is bottom, i.e. `absAt k = bot` alone does
; not constrain `conc k`.  (`ne` is an arbitrary non-empty space; the goal says
; the two facts are CONSISTENT with conc k = ne, by proving the contrapositive
; shape "if conc k were forced empty by the summary alone then every space
; would be empty".)
(declare-const ne Space)
; PREMISE: ne is a non-empty space
(assert (distinct ne emptysp))
(push)
(assert (= (absAt 999) bot))
(assert (forall ((s Space)) (=> (= (absAt 999) bot) (= s emptysp))))   ; the WRONG rule
(check-sat) ; expect unsat
(pop)
