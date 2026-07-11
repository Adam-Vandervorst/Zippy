% =============================================================================
% The core reusable measure lemma behind every termination proof in this
% directory: STRICT GROWTH INSIDE A FINITE UNIVERSE STRICTLY SHRINKS THE
% COMPLEMENT. For any sets R (current state), S (next state), U (universe):
%
%     R subset= S subset= U  &  S != R
%       =>  card(U \ S) < card(U \ R)
%
% This is reachable_decrease.p's conjunct (3) pulled out of its mask-specific
% setting and quantified over the universe, so downstream files can import it
% as a single premise instead of re-fighting the witness extraction each
% time. Combined with no_infinite_descent.smt2 exactly as before: any run
% whose states keep strictly growing inside a finite universe U can only
% take card(U) growth steps before the next state repeats - at which point
% the recursion schemes in this directory (state \/ Call(..., step(state)),
% cut when the argument repeats; for the Datalog programs the cut is
% literally the "no new facts" test) stop.
%
% Used as an imported lemma-role premise by: datalog_a_terminates.p,
% datalog_b_naive_terminates.p, datalog_b_seminaive_terminates.p (and it
% subsumes the measure part of reachable_decrease.p, kept in its original
% staged form there).
%
% "node" is any element sort - graph vertices for reachable/scc, whole
% Datalog facts (tagged tuples) for the datalog_* files; nothing here
% depends on what the elements are.
% =============================================================================

tff(node_type, type, node: $tType ).
tff(nset_type, type, nset: $tType ).

tff(mem_type, type, mem: (node * nset) > $o ).
tff(subset_type, type, subset: (nset * nset) > $o ).
tff(card_type, type, card: nset > $int ).
tff(setminus_type, type, setminus: (nset * nset) > nset ).

tff(mem_setminus, axiom,
    ! [X: node, A: nset, B: nset] : ( mem(X,setminus(A,B)) <=> ( mem(X,A) & ~mem(X,B) ) ) ).

tff(subset_def, axiom,
    ! [A: nset, B: nset] : ( subset(A,B) <=> ( ! [X: node] : (mem(X,A) => mem(X,B)) ) ) ).

tff(extensionality, axiom,
    ! [A: nset, B: nset] : ( ( ! [X: node] : (mem(X,A) <=> mem(X,B)) ) => A = B ) ).

% --- cardinality of a finite set: a natural number that strictly drops when
% a witnessed element is removed from a superset (same finite-set facts as
% scc_decrease.p / reachable_decrease.p).
tff(card_nonneg, axiom,
    ! [A: nset] : $greatereq(card(A), 0) ).

tff(card_strict_decrease, axiom,
    ! [A: nset, B: nset, W: node] :
      ( ( subset(A,B) & mem(W,B) & ~mem(W,A) )
        => $less(card(A), card(B)) ) ).

% --- the lemma. Proof shape: S != R with R subset= S yields (extensionality)
% a witness w in S \ R; U\S subset= U\R since R subset= S; w lands in U\R but
% not in U\S; card_strict_decrease closes it.
tff(bounded_growth_decrease, conjecture,
    ! [R: nset, S: nset, U: nset] :
      ( ( subset(R,S) & subset(S,U) & S != R )
        => $less(card(setminus(U,S)), card(setminus(U,R))) ) ).
