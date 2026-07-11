% =============================================================================
% Termination of ALL SIX MORKL Datalog programs in datalog_a.txt:
%
%   1/6 singleCycle_naive_transitive        4/6 multiIsolatedCycle_semiNaive_transitive
%   2/6 singleCycle_semiNaive_transitive    5/6 topSort_naive_transitive
%   3/6 multiIsolatedCycle_naive_transitive 6/6 topSort_semiNaive_transitive
%
% Every one of these routines has the recursion shape
%
%   routine(last) = last \/ Call(routine, [ last \/ F(last) ])       (*)
%
% - the recursive call's argument is Union(Mention("last"), ...) LITERALLY in
% the printed AST, so the argument chain is inflationary BY CONSTRUCTION,
% whatever F computes. Program-by-program, F is:
%
%   naive (1,3,5 - identical routine bodies, only the RoutinePtr name and the
%   seed edge Literal differ, and this proof quantifies over both):
%     F(last) = Iteration(Unwrap(last,"edge"), x, y_, Wrap3(y_, y, x, "path"))
%            \/ Iteration(Unwrap(last,"path"), x, ..., z, Wrap3(z_, z, x, "path"))
%     i.e. copy edge facts to path facts, and join path o path into path.
%
%   semi-naive (2,4,6 - likewise identical up to the seed):
%     F(last) = Wrap(Unwrap(last,"complete") \/ Unwrap(last,"delta"), "complete")
%            \/ Wrap(cons(last) \ (Unwrap(last,"complete.path") \/
%                                   Unwrap(last,"delta.path")), "delta.path")
%     (cons = the three edge/path joins over the complete/delta parts).
%
% F is left COMPLETELY UNINTERPRETED below - the naive F is monotone, the
% semi-naive F is not (it contains a Subtraction), and neither fact is
% needed. The single domain assumption is that F maps subsets of the finite
% fact universe `top` to subsets of `top`, which in this typed encoding is
% structural: every fact any of these programs can construct is a path of
% bounded arity (tag.x.y, or tag.tag'.x.y for the semi-naive complete/delta
% tagging) whose items are drawn from the fixed tag set
% {edge, path, complete, delta} and the constants of the seed literal - the
% Space operators used (Union/Subtraction/Wrap/Unwrap/Iteration/Singleton)
% only rearrange existing items, they never mint new ones. `top` = all such
% facts is therefore finite, and finiteness of `top` is what card's axioms
% model. (This is the same boundary discussed in reachable_decrease.p: a
% hash-like F that conjured fresh constants each round would have NO finite
% top, and the sort discipline here is the formal counterpart of "no fresh
% constants".)
%
% The theorem: at every state R of the argument chain, R subset= step(R),
% and a non-fixpoint step strictly shrinks card(top \ R). Paired with
% no_infinite_descent.smt2 (measure into the naturals via card_nonneg), the
% argument chain of (*) stabilizes within card(top) steps, the recursion's
% argument repeats, and the run terminates - the repeat test is exactly
% Datalog's "no new facts derived this round".
%
% bounded_growth_decrease is proved standalone in bounded_growth_decrease.p
% and imported here as a lemma-role premise (usual staging discipline).
% =============================================================================

tff(node_type, type, node: $tType ).
tff(nset_type, type, nset: $tType ).

tff(mem_type, type, mem: (node * nset) > $o ).
tff(subset_type, type, subset: (nset * nset) > $o ).
tff(card_type, type, card: nset > $int ).
tff(setminus_type, type, setminus: (nset * nset) > nset ).
tff(cup_type, type, cup: (nset * nset) > nset ).
tff(top_type, type, top: nset ).
tff(f_type, type, f: nset > nset ).

tff(mem_cup, axiom,
    ! [X: node, A: nset, B: nset] : ( mem(X,cup(A,B)) <=> ( mem(X,A) | mem(X,B) ) ) ).

tff(subset_def, axiom,
    ! [A: nset, B: nset] : ( subset(A,B) <=> ( ! [X: node] : (mem(X,A) => mem(X,B)) ) ) ).

% top is the (finite) universe of constructible facts; everything lives in it.
tff(mem_top, axiom,
    ! [X: node] : mem(X, top) ).

tff(card_nonneg, axiom,
    ! [A: nset] : $greatereq(card(A), 0) ).

% --- proved in bounded_growth_decrease.p, imported as a premise.
tff(bounded_growth_decrease, lemma,
    ! [R: nset, S: nset, U: nset] :
      ( ( subset(R,S) & subset(S,U) & S != R )
        => $less(card(setminus(U,S)), card(setminus(U,R))) ) ).

% --- the theorem, for step(R) = R \/ F(R) with F arbitrary: the chain only
% grows, and growth strictly pays down the finite budget card(top \ R).
tff(datalog_a_all_six_terminate, conjecture,
    ! [R: nset] :
      ( subset(R, cup(R, f(R)))
      & ( cup(R, f(R)) != R
          => $less(card(setminus(top, cup(R, f(R)))), card(setminus(top, R))) ) ) ).
