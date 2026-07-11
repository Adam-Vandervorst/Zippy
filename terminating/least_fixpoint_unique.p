% =============================================================================
% General theorem, independent of graphs/paths: in any join-semilattice
% (cup idempotent, commutative, associative - exactly Union's laws in
% intro.egg), a self-referential equation X = cup(A, f(X)) has AT MOST ONE
% *least* solution.
%
% This is the abstract fact underwriting why R"transitive" and R"reachable"
% are well-defined "total functions" despite having no visible base case:
% whichever least solution you happen to construct (by unrolling the
% recursion, by Kleene iteration, by any other means), it is forced to
% coincide with every other least solution - the recursive *equation* by
% itself doesn't pin down a unique value (many non-least relations satisfy
% X = cup(A, f(X)) too, e.g. anything f-closed and large enough), but
% *insisting on the least one* - which is what "the algorithm converges to
% the smallest thing that stops changing" means - does pin it down uniquely.
% Combined with transitive_equiv.p (two structurally different recursions
% for R"transitive" denote the same relation) and the egglog checks in
% total_functions.egg (concrete instances actually reach that least fixed
% point via Union's idempotence, without any syntactic termination check),
% this closes the loop: the prompt's recursive definitions denote a single,
% well-defined value, and reaching it needs no explicit "did anything
% change" guard because Union already enforces it.
%
% This file is the WELL-DEFINEDNESS piece only. That R"reachable"'s
% unfolding actually reaches its fixpoint in finitely many steps on every
% finite mask (termination proper) is proved separately in
% reachable_decrease.p + no_infinite_descent.smt2, and what the reached
% value contains in reachable_value.p.
% =============================================================================

fof(cup_idempotent, axiom,
    ! [X] : cup(X,X) = X ).

fof(cup_commutative, axiom,
    ! [X,Y] : cup(X,Y) = cup(Y,X) ).

fof(cup_associative, axiom,
    ! [X,Y,Z] : cup(cup(X,Y),Z) = cup(X,cup(Y,Z)) ).

% the induced order: X <= Y  iff  cup(X,Y) = Y
fof(leq_def, axiom,
    ! [X,Y] : ( leq(X,Y) <=> cup(X,Y) = Y ) ).

% l1 and l2 both satisfy the defining equation X = cup(a, f(X))
fof(l1_satisfies, axiom,
    l1 = cup(a, f(l1)) ).

fof(l2_satisfies, axiom,
    l2 = cup(a, f(l2)) ).

% l1 and l2 are each the LEAST relation satisfying that equation
fof(l1_least, axiom,
    ! [Z] : ( Z = cup(a, f(Z)) => leq(l1,Z) ) ).

fof(l2_least, axiom,
    ! [Z] : ( Z = cup(a, f(Z)) => leq(l2,Z) ) ).

fof(least_fixpoint_unique, conjecture,
    l1 = l2 ).
