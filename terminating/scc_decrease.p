% =============================================================================
% Domain-specific half of the termination proof for:
%
%   R"seedless_scc"(fwd, bwd, nodes) :=
%     First(1, nodes).iter(v, _, {
%       pred := R"reachable"(fwd, nodes, {v})
%       desc := R"reachable"(bwd, nodes, {v})
%       (v x ((pred /\ desc) \ {v})) \/
%         R"scc"(fwd, bwd, pred \ desc) \/
%         R"scc"(fwd, bwd, desc \ pred) \/
%         R"scc"(fwd, bwd, (nodes \ pred) \ desc)
%     })
%
% (R"scc" in the body is a typo for R"seedless_scc" - the definition is
% directly self-recursive; confirmed by the author. Every recursive call
% the body makes is therefore one of the three calls covered below.)
%
% Shows: whenever the pivot v triggers the recursive step, all three
% recursive calls receive a node-set with STRICTLY SMALLER cardinality than
% `nodes`. Combined with no_infinite_descent.smt2 (no infinite strictly-
% decreasing sequence of naturals exists), this rules out an infinite chain
% of recursive calls, i.e. the recursion terminates for every finite
% starting node-set.
%
% Interface assumptions about First/iterh, used but not provable here (they
% are facts about those combinators' semantics, not about sets): (i) when
% nodes is nonempty, First(1,nodes) yields a member v of nodes - this is
% the mem(U2,U1) hypothesis threaded through everything below; (ii) when
% nodes is empty, First(1,nodes) yields nothing, the .iterh body never
% runs, there are zero recursive calls, and termination is immediate.
%
% The recursion depth is only half of the body's termination: each
% iteration also computes pred/desc via two R"reachable" calls, and THAT
% recursion's termination (for every finite mask, hence at every level of
% this recursion) is proved in reachable_decrease.p, paired with the same
% no_infinite_descent.smt2. So every individual body evaluation is finite,
% and this file bounds how many body evaluations there can be.
%
% The proof is staged as six `lemma`-role intermediate facts before the
% final conjecture: each is independently machine-checked on its own (as a
% standalone conjecture from just the more basic axioms - see the session
% notes) before being included here as a given premise. Handing Vampire the
% whole axiom set plus the single combined conjecture directly makes it time
% out; broken into these named stepping stones the final combination is
% immediate.
% =============================================================================

tff(node_type, type, node: $tType ).
tff(nset_type, type, nset: $tType ).

tff(mem_type, type, mem: (node * nset) > $o ).
tff(subset_type, type, subset: (nset * nset) > $o ).
tff(card_type, type, card: nset > $int ).

tff(setminus_type, type, setminus: (nset * nset) > nset ).
tff(pred_type, type, pred: (nset * node) > nset ).
tff(desc_type, type, desc: (nset * node) > nset ).

tff(mem_setminus, axiom,
    ! [Y1: node, Y2: nset, Y3: nset] : ( mem(Y1,setminus(Y2,Y3)) <=> ( mem(Y1,Y2) & ~mem(Y1,Y3) ) ) ).

tff(subset_def, axiom,
    ! [X1: nset, X2: nset] : ( subset(X1,X2) <=> ( ! [X3: node] : (mem(X3,X1) => mem(X3,X2)) ) ) ).

% --- cardinality is a natural number, and dropping a witnessed element from
% a subset strictly decreases it relative to the superset (basic fact about
% finite sets; nodes/pred/desc are finite vertex sets of the input graph).
tff(card_nonneg, axiom,
    ! [Z1: nset] : $greatereq(card(Z1), 0) ).

tff(card_strict_decrease, axiom,
    ! [P1: nset, P2: nset, P3: node] :
      ( ( subset(P1,P2) & mem(P3,P2) & ~mem(P3,P1) )
        => $less(card(P1), card(P2)) ) ).

% R"reachable"(e,m,r) = r \/ R"reachable"(e,m, step(r)) always contains its
% seed r, unconditionally: every level of the recursion contributes its own
% leading "r \/ ..." layer. PROVED (not assumed) in reachable_value.p,
% conjunct (a), by induction on the recursion depth from the recursion's
% shape alone; imported here as a premise, in the same staging discipline
% as the lemma roles below.
tff(pred_contains_pivot, axiom,
    ! [Q1: nset, Q2: node] : mem(Q2, pred(Q1,Q2)) ).

tff(desc_contains_pivot, axiom,
    ! [R1: nset, R2: node] : mem(R2, desc(R1,R2)) ).

% R"reachable"(e,m,r) never leaves the mask m once r subset= m - CONDITIONALLY
% on the seed v itself being in nodes. PROVED in reachable_value.p,
% conjunct (b), with exactly this mem-guard; imported here as a premise.
% (The guard is necessary: Reachable(e,m,r) contains its seed r
% unconditionally per pred/desc_contains_pivot above, so "stays inside the
% mask" only holds while r={v} subset= m=nodes, i.e. while mem(V,Nodes); it
% is not true unconditionally, and asserting it without that guard makes the
% axiom set inconsistent - v would be forced into every nset via
% pred_contains_pivot + subset, for every choice of Nodes, including ones v
% has nothing to do with.)
tff(pred_subset_nodes, axiom,
    ! [S1: nset, S2: node] : ( mem(S2,S1) => subset(pred(S1,S2), S1) ) ).

tff(desc_subset_nodes, axiom,
    ! [T1: nset, T2: node] : ( mem(T2,T1) => subset(desc(T1,T2), T1) ) ).

% --- intermediate: pred\desc, desc\pred, and nodes\pred\desc are all
% subsets of nodes, given the pivot is in nodes.
tff(subset_pred_minus_desc, lemma,
    ! [U1: nset, U2: node] :
      ( mem(U2,U1) => subset(setminus(pred(U1,U2),desc(U1,U2)), U1) ) ).

tff(subset_desc_minus_pred, lemma,
    ! [U1: nset, U2: node] :
      ( mem(U2,U1) => subset(setminus(desc(U1,U2),pred(U1,U2)), U1) ) ).

tff(subset_remainder, lemma,
    ! [U1: nset, U2: node] :
      ( mem(U2,U1) => subset(setminus(setminus(U1,pred(U1,U2)),desc(U1,U2)), U1) ) ).

% --- intermediate: the pivot itself is excluded from all three branches
% (unconditionally - pred/desc_contains_pivot alone already rules it out).
tff(pivot_excluded_pred_minus_desc, lemma,
    ! [U1: nset, U2: node] : ~mem(U2, setminus(pred(U1,U2),desc(U1,U2))) ).

tff(pivot_excluded_desc_minus_pred, lemma,
    ! [U1: nset, U2: node] : ~mem(U2, setminus(desc(U1,U2),pred(U1,U2))) ).

tff(pivot_excluded_remainder, lemma,
    ! [U1: nset, U2: node] : ~mem(U2, setminus(setminus(U1,pred(U1,U2)),desc(U1,U2))) ).

% --- the theorem: given the pivot is drawn from nodes, all three recursive
% arguments have strictly smaller cardinality than nodes.
tff(decrease_all_three_branches, conjecture,
    ! [U1: nset, U2: node] :
      ( mem(U2,U1) =>
        ( $less(card(setminus(pred(U1,U2), desc(U1,U2))), card(U1))
          & $less(card(setminus(desc(U1,U2), pred(U1,U2))), card(U1))
          & $less(card(setminus(setminus(U1, pred(U1,U2)), desc(U1,U2))), card(U1)) ) ) ).
