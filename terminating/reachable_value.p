% =============================================================================
% Derivation of the two R"reachable" facts that scc_decrease.p consumes as
% axioms - previously taken on faith there with a comment pointing at an
% earlier session - from the shape of the recursion itself:
%
%   R"reachable"(e, m, r) = r \/ R"reachable"(e, m, step(r)),
%   step(r) = (r \/ frontier(r)) /\ m       (see reachable_decrease.p)
%
% Model: iter(n) is the third argument after n unfoldings; acc(n) is the
% value assembled by the first n levels of the recursion (each level
% contributes its own leading "r \/ ..." layer):
%
%   acc(n) = r \/ step(r) \/ step(step(r)) \/ ... \/ iter(n).
%
% A terminating run - guaranteed for every finite mask by
% reachable_decrease.p + no_infinite_descent.smt2 - hits step(iter(N)) =
% iter(N) at some depth N, the idempotence cut returns iter(N) there, and
% the unrolled value is exactly acc(N). The conjecture below is proved for
% EVERY n >= 0, so in particular at that N: termination is needed only for
% such a finite N to exist, not for knowing which one it is. (cup is real
% set union, where this left-nested accumulation and the recursion's
% right-nested layering are the same set; the proof never needs
% associativity/commutativity of cup - the subset facts hold for the
% accumulated union however it is nested.)
%
% With seed sing(v0) = {v}, mask = nodes, and frontier the fwd (resp. bwd)
% edge-frontier operator, acc(N) is scc_decrease.p's pred(nodes,v) (resp.
% desc(nodes,v)), and the two conjuncts proved here are exactly its axioms:
%
%   (a) mem(v0, acc(n))  - the seed survives into the value UNCONDITIONALLY
%       (= pred_contains_pivot / desc_contains_pivot: the leading "r \/ ..."
%       layer keeps the seed even when it lies outside the mask);
%   (b) mem(v0, mask) => acc(n) subset= mask  - the value stays inside the
%       mask PROVIDED the seed starts inside it (= pred_subset_nodes /
%       desc_subset_nodes, reproducing exactly the mem-guard whose necessity
%       scc_decrease.p's comments already document).
%
% The only fact about step used is subset(step(R), mask) - the step_in_mask
% conjunct proved in reachable_decrease.p, imported here as a premise (same
% staging discipline as scc_decrease.p's lemma roles); frontier, edges, and
% everything else about what step computes stay uninterpreted. The remaining
% axioms are plain Horn facts of set algebra (reflexivity/transitivity of
% subset, cup as least upper bound, singletons).
%
% The proof is by induction on the recursion depth n - and unlike
% no_infinite_descent.smt2, where the induction had to be staged by hand,
% here the ATP finds the induction itself: run with
%
%   vampire --induction int reachable_value.p     (~2s, default otherwise)
%
% The --induction int flag is required; without it default-mode saturation
% has no induction rule and times out.
% =============================================================================

tff(node_type, type, node: $tType ).
tff(nset_type, type, nset: $tType ).

tff(mem_type, type, mem: (node * nset) > $o ).
tff(subset_type, type, subset: (nset * nset) > $o ).
tff(cup_type, type, cup: (nset * nset) > nset ).
tff(sing_type, type, sing: node > nset ).
tff(step_type, type, step: nset > nset ).
tff(mask_type, type, mask: nset ).
tff(v0_type, type, v0: node ).
tff(iter_type, type, iter: $int > nset ).
tff(acc_type, type, acc: $int > nset ).

% --- Horn fragment of set algebra: subset is a preorder, cup is an upper
% bound and least such, subset transports membership, singletons.
tff(subset_refl, axiom, ! [A: nset] : subset(A,A) ).

tff(subset_trans, axiom,
    ! [A: nset, B: nset, C: nset] : ( ( subset(A,B) & subset(B,C) ) => subset(A,C) ) ).

tff(cup_ub1, axiom, ! [A: nset, B: nset] : subset(A, cup(A,B)) ).

tff(cup_ub2, axiom, ! [A: nset, B: nset] : subset(B, cup(A,B)) ).

tff(cup_lub, axiom,
    ! [A: nset, B: nset, C: nset] : ( ( subset(A,C) & subset(B,C) ) => subset(cup(A,B), C) ) ).

tff(subset_mem, axiom,
    ! [A: nset, B: nset, X: node] : ( ( subset(A,B) & mem(X,A) ) => mem(X,B) ) ).

tff(mem_sing, axiom, ! [X: node] : mem(X, sing(X)) ).

tff(sing_least, axiom,
    ! [X: node, B: nset] : ( mem(X,B) => subset(sing(X), B) ) ).

% --- the single fact about one unfolding of R"reachable"'s argument:
% whatever the frontier adds, the step lands inside the mask. Proved as the
% step_in_mask lemma of reachable_decrease.p; imported as a premise here.
tff(step_in_mask, axiom, ! [R: nset] : subset(step(R), mask) ).

% --- the argument chain and the level-by-level accumulated value.
tff(iter_base, axiom, iter(0) = sing(v0) ).

tff(iter_step, axiom,
    ! [N: $int] : ( $greatereq(N,0) => iter($sum(N,1)) = step(iter(N)) ) ).

tff(acc_base, axiom, acc(0) = sing(v0) ).

tff(acc_step, axiom,
    ! [N: $int] : ( $greatereq(N,0) => acc($sum(N,1)) = cup(acc(N), iter($sum(N,1))) ) ).

% --- the theorem: at every recursion depth (hence at the terminating depth
% N), (a) the seed is in the value, unconditionally, and (b) if the seed
% starts inside the mask, the value stays inside the mask.
tff(value_facts, conjecture,
    ! [N: $int] :
      ( $greatereq(N,0) =>
        ( mem(v0, acc(N))
        & ( mem(v0, mask) => subset(acc(N), mask) ) ) ) ).
