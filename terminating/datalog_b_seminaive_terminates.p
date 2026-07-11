% =============================================================================
% Termination of the THREE SEMI-NAIVE MORKL Datalog programs in datalog_b.txt:
%
%   tc_sn  - transitive closure:  state (e; all, delta)
%   rsg_sn - reverse same-gen:    state (up, flat, down; all, delta)
%   pt_sn  - Andersen points-to:  state (addressOf, assign; all, delta)
%
% All three share one transition, transcribed from the printed ASTs:
%
%   all'   = all \/ (D(delta) \ all)
%   delta' =        D(delta) \ all
%
% where D is the per-program delta-consequence operator:
%
%   D_tc(delta)  = comp(delta, e)
%   D_pt(delta)  = comp(assign, delta)
%   D_rsg(delta) = comp(comp(up, inv(delta)), down)
%
% (comp/inv as read off in datalog_b_naive_terminates.p). D is left FULLY
% UNINTERPRETED below: unlike the naive programs, the semi-naive step is NOT
% monotone in the state - delta' shrinks when all grows, via the Subtraction
% - and no monotonicity is needed. What terminates semi-naive evaluation is
% the LEXICOGRAPHIC measure
%
%   mu(all, delta) = 2 * card(top \ all) + [delta != empty]
%
% which strictly decreases on EVERY step that changes the state at all:
%   - if all' != all: all grew strictly inside the finite universe `top`
%     (allp_grows + allp_in_top + bounded_growth_decrease), so card(top\all)
%     drops by at least 1 and the flag term (bounded by flag_bounds) cannot
%     make up the 2;
%   - if all' = all but delta' != delta: a stalled `all` forces delta' =
%     empty (stalled_delta_empty - pure set algebra: delta' = D(delta)\all
%     is disjoint from all yet, when all absorbs it, contained in all), so
%     delta was nonempty and the flag term drops 1 with the card term fixed.
% So mu is a natural number ($greatereq conjunct + card_nonneg) that
% strictly decreases until the state repeats; by no_infinite_descent.smt2
% the state repeats after finitely many steps. The carried arguments (e /
% addressOf,assign / up,flat,down) pass through every recursive call
% unchanged, so the full argument tuple repeats exactly when (all, delta)
% does - and that repeat is the recursion's cut ("no new facts": once all
% stalls, the next delta is empty, and the step after that changes nothing).
%
% Since D is uninterpreted, this one theorem covers all three programs at
% once - and any other semi-naive Datalog program with this transition
% shape. Finiteness of `top` (all facts of the fixed arity over the seed
% literals' items) is the usual "no fresh constants" boundary; see
% datalog_a_terminates.p / reachable_decrease.p.
%
% Stepping stones each independently machine-checked standalone;
% bounded_growth_decrease proved in bounded_growth_decrease.p.
% =============================================================================

tff(node_type, type, node: $tType ).
tff(nset_type, type, nset: $tType ).

tff(mem_type, type, mem: (node * nset) > $o ).
tff(subset_type, type, subset: (nset * nset) > $o ).
tff(card_type, type, card: nset > $int ).
tff(setminus_type, type, setminus: (nset * nset) > nset ).
tff(cup_type, type, cup: (nset * nset) > nset ).
tff(empty_type, type, empty: nset ).
tff(top_type, type, top: nset ).
tff(flag_type, type, flag: nset > $int ).
tff(d_type, type, d: nset > nset ).
tff(allp_type, type, allp: (nset * nset) > nset ).
tff(deltap_type, type, deltap: (nset * nset) > nset ).
tff(mu_type, type, mu: (nset * nset) > $int ).

tff(mem_cup, axiom,
    ! [X: node, A: nset, B: nset] : ( mem(X,cup(A,B)) <=> ( mem(X,A) | mem(X,B) ) ) ).

tff(mem_setminus, axiom,
    ! [X: node, A: nset, B: nset] : ( mem(X,setminus(A,B)) <=> ( mem(X,A) & ~mem(X,B) ) ) ).

tff(subset_def, axiom,
    ! [A: nset, B: nset] : ( subset(A,B) <=> ( ! [X: node] : (mem(X,A) => mem(X,B)) ) ) ).

tff(extensionality, axiom,
    ! [A: nset, B: nset] : ( ( ! [X: node] : (mem(X,A) <=> mem(X,B)) ) => A = B ) ).

tff(mem_empty, axiom, ! [X: node] : ~mem(X, empty) ).

tff(mem_top, axiom, ! [X: node] : mem(X, top) ).

tff(card_nonneg, axiom, ! [A: nset] : $greatereq(card(A), 0) ).

% [delta != empty] as an integer, for the lexicographic measure.
tff(flag_empty, axiom, flag(empty) = 0 ).

tff(flag_nonempty, axiom, ! [A: nset] : ( A != empty => flag(A) = 1 ) ).

% --- the shared semi-naive transition and its measure.
tff(allp_def, axiom,
    ! [A: nset, D: nset] : allp(A,D) = cup(A, setminus(d(D), A)) ).

tff(deltap_def, axiom,
    ! [A: nset, D: nset] : deltap(A,D) = setminus(d(D), A) ).

tff(mu_def, axiom,
    ! [A: nset, D: nset] :
      mu(A,D) = $sum($product(2, card(setminus(top, A))), flag(D)) ).

% --- stepping stones, each independently machine-checked standalone from
% the axioms above (staging discipline of scc_decrease.p).
tff(allp_grows, lemma,
    ! [A: nset, D: nset] : subset(A, allp(A,D)) ).

tff(allp_in_top, lemma,
    ! [A: nset, D: nset] : subset(allp(A,D), top) ).

tff(stalled_delta_empty, lemma,
    ! [A: nset, D: nset] : ( allp(A,D) = A => deltap(A,D) = empty ) ).

tff(flag_bounds, lemma,
    ! [A: nset] : ( $greatereq(flag(A), 0) & $lesseq(flag(A), 1) ) ).

% --- proved in bounded_growth_decrease.p, imported as a premise.
tff(bounded_growth_decrease, lemma,
    ! [R: nset, S: nset, U: nset] :
      ( ( subset(R,S) & subset(S,U) & S != R )
        => $less(card(setminus(U,S)), card(setminus(U,R))) ) ).

% --- the theorem: mu maps states into the naturals and strictly decreases
% on every state-changing step, for EVERY delta-consequence operator D.
tff(datalog_b_seminaive_all_three_terminate, conjecture,
    ! [A: nset, D: nset] :
      ( $greatereq(mu(A,D), 0)
      & ( ( allp(A,D) != A | deltap(A,D) != D )
          => $less(mu(allp(A,D), deltap(A,D)), mu(A,D)) ) ) ).
