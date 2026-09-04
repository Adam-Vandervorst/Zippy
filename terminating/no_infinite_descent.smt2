; =============================================================================
; Well-foundedness of < on the naturals: no total function g from naturals to
; naturals can be everywhere strictly decreasing on successors. This is the
; abstract fact that turns "every recursive call strictly decreases a
; natural-number measure" into "the recursion terminates", and it is the
; shared well-foundedness half for BOTH recursions:
;
;   - R"seedless_scc", measure card(nodes): see scc_decrease.p for why each
;     recursive call's card(nodes) is strictly smaller than its caller's;
;   - R"reachable", measure card(nodemask \ reach): see reachable_decrease.p
;     for why each unfolding not yet at the fixpoint strictly shrinks it;
;   - the MORKL Datalog programs of datalog_a.txt / datalog_b.txt, measures
;     card(top \ state) resp. 2*card(top \ all) + [delta nonempty]: see
;     datalog_a_terminates.p, datalog_b_naive_terminates.p,
;     datalog_b_seminaive_terminates.p (all built on the shared lemma in
;     bounded_growth_decrease.p).
;
; The bridging step from "this recursion never terminates" to "such a g
; exists", made explicit: a non-terminating run contains an infinite chain
; of nested recursive calls c_0, c_1, c_2, ... (picking, for each n, the
; (n+1)-st call in the chain - this is dependent choice, the same principle
; any hand proof of "no infinite descent" uses); setting g(n) := the measure
; at c_n gives a total function from naturals to naturals that the
; domain-specific file shows is strictly decreasing at every step - which
; this file shows is impossible.
;
; This is genuinely an induction fact (equivalent to Peano induction /
; well-ordering of the naturals), and asking Vampire/Z3 to find the
; induction fully automatically did not go through in reasonable time (a
; background Vampire run with --induction int ran 3 minutes and 3+ GB
; without a proof; Z3 has no native induction at all for unbounded
; universal arithmetic statements like this). Rather than accept that as a
; dead end, the induction is spelled out explicitly below - base case,
; inductive step, and the final instantiation - exactly as a mathematician
; would write it on paper, with each individual (non-inductive) step
; independently checked by Z3. Only the "therefore, by induction, for all
; n" bridging step is asserted rather than search-discovered, which is the
; same thing that happens implicitly every time a hand proof invokes the
; induction principle.
; =============================================================================

(declare-fun g (Int) Int)
; PREMISE: g is natural-valued
(assert (forall ((n Int)) (=> (>= n 0) (>= (g n) 0))))         ; g maps naturals to naturals
; PREMISE: g strictly decreases
(assert (forall ((n Int)) (=> (>= n 0) (< (g (+ n 1)) (g n)))))  ; g strictly decreases at every step

; --- Step 1 (base case): g(0) <= g(0) - 0.
(push)
(assert (not (<= (g 0) (- (g 0) 0))))
(check-sat) ; expect unsat
(pop)

; --- Step 2 (inductive step): for arbitrary n>=0, assuming the induction
; hypothesis g(n) <= g(0)-n, conclude g(n+1) <= g(0)-(n+1). (g(n+1) < g(n) <=
; g(0)-n by the hypothesis and the decrease axiom; since g(n+1) and g(0)-n
; are integers, g(n+1) < g(0)-n implies g(n+1) <= g(0)-n-1.)
(push)
(declare-const n0 Int)
(assert (>= n0 0))
(assert (<= (g n0) (- (g 0) n0)))
(assert (not (<= (g (+ n0 1)) (- (g 0) (+ n0 1)))))
(check-sat) ; expect unsat
(pop)

; --- By steps 1+2, mathematical induction gives: forall n>=0. g(n) <= g(0)-n.
; --- Step 3 (final contradiction): instantiate that conclusion at
; n := g(0)+1 (valid since g(0)>=0) and combine with g mapping into the
; naturals at that same point.
(push)
(assert (>= (+ (g 0) 1) 0))
(assert (>= (g (+ (g 0) 1)) 0))                          ; g maps into naturals, at n := g(0)+1
(assert (<= (g (+ (g 0) 1)) (- (g 0) (+ (g 0) 1))))       ; the induction conclusion, at n := g(0)+1
(check-sat) ; expect unsat - g(g(0)+1) would have to be both >= 0 and <= -1
(pop)
