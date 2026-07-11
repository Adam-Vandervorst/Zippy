% =============================================================================
% Domain-specific half of the termination proof for:
%
%   R"reachable"(edges, nodemask, reach) :=
%     reach \/ R"reachable"(edges, nodemask,
%                (reach \/ \/(edges <| (reach /\ nodemask))) /\ nodemask)
%
% (parenthesized per Scala's actual first-character operator precedence: `\`
% - the first character of `\/` - outranks `/` - the first character of `/\`
% - so the unparenthesized source parses as (reach \/ ...) /\ nodemask, NOT
% reach \/ (... /\ nodemask); total_functions.egg's executable encoding is
% aligned with this parse. For arguments already inside the mask the two
% parses coincide, which is why the concrete egglog tests could not tell
% them apart.)
%
% One unfolding rewrites the third argument by
%
%     step(R) = (R \/ frontier(R)) /\ mask
%
% where frontier(R) = \/(edges <| (R /\ mask)) - but NOTHING below depends on
% what frontier computes: it is a completely uninterpreted function symbol.
% That is the crux of why this recursion terminates when the superficially
% similar shape f(x) = x \/ f(x \/ g(x)) does not: for arbitrary g (say, a
% hash function conjuring one fresh element per round) the argument grows
% forever. R"reachable" is more specific - whatever frontier produces is
% immediately intersected back into the FINITE mask, and that alone (plus
% finiteness of card) forces stabilization. The conjecture has three parts:
%
%   (1) step(R) subset= mask, for EVERY R, masked or not: one unfolding lands
%       the argument inside the mask, so the invariant needed by (2) and (3)
%       holds from depth 1 onward regardless of the initial seed;
%   (2) R subset= mask => R subset= step(R): on masked arguments the
%       unfolding is inflationary - the argument chain only grows;
%   (3) R subset= mask & step(R) != R =>
%           card(mask \ step(R)) < card(mask \ R):
%       every unfolding not yet at the fixpoint strictly shrinks the
%       natural-number measure card(mask \ R).
%
% Combined with no_infinite_descent.smt2 (no total function from the naturals
% to the naturals is everywhere strictly decreasing): suppose the recursion
% never reached step(R) = R - which is exactly the condition under which the
% implementation's idempotence cut Reachable(e,m,r) -> r fires and stops
% recursing (see total_functions.egg). Then the argument chain r1 = step(r0),
% r2 = step(r1), ... is infinite, lies inside the mask from r1 on by (1), and
% by (3) the assignment g(n) := card(mask \ r_{n+1}) would be a total,
% everywhere-strictly-decreasing function from naturals to naturals
% (card_nonneg supplies "into the naturals") - impossible. Hence for every
% finite mask and ARBITRARY seed the chain stabilizes after at most
% card(mask) growing steps and R"reachable" terminates. (Reading an infinite
% run off as the function g is the same dependent-choice glue used for
% R"seedless_scc" - see the headers of no_infinite_descent.smt2 and
% scc_decrease.p.)
%
% What the value of the terminated recursion looks like - in particular the
% two facts scc_decrease.p consumes as pred/desc axioms - is derived
% separately in reachable_value.p, which imports conjunct (1) of this file
% as its only fact about step.
%
% Staging discipline (same as scc_decrease.p): the five `lemma`-role facts
% before the final conjecture were each independently machine-checked as a
% standalone conjecture from just the axioms above them, then included here
% as premises; default-mode Vampire times out on the combined conjecture
% directly but dispatches it immediately from these stepping stones
% (portfolio `--mode casc` also proves the combined conjecture from the bare
% axioms with no staging, as a cross-check).
% =============================================================================

tff(node_type, type, node: $tType ).
tff(nset_type, type, nset: $tType ).

tff(mem_type, type, mem: (node * nset) > $o ).
tff(subset_type, type, subset: (nset * nset) > $o ).
tff(card_type, type, card: nset > $int ).

tff(cup_type, type, cup: (nset * nset) > nset ).
tff(cap_type, type, cap: (nset * nset) > nset ).
tff(setminus_type, type, setminus: (nset * nset) > nset ).
tff(frontier_type, type, frontier: nset > nset ).
tff(mask_type, type, mask: nset ).
tff(step_type, type, step: nset > nset ).

% --- membership semantics of the boolean operations, subset, extensionality.
tff(mem_cup, axiom,
    ! [X: node, A: nset, B: nset] : ( mem(X,cup(A,B)) <=> ( mem(X,A) | mem(X,B) ) ) ).

tff(mem_cap, axiom,
    ! [X: node, A: nset, B: nset] : ( mem(X,cap(A,B)) <=> ( mem(X,A) & mem(X,B) ) ) ).

tff(mem_setminus, axiom,
    ! [X: node, A: nset, B: nset] : ( mem(X,setminus(A,B)) <=> ( mem(X,A) & ~mem(X,B) ) ) ).

tff(subset_def, axiom,
    ! [A: nset, B: nset] : ( subset(A,B) <=> ( ! [X: node] : (mem(X,A) => mem(X,B)) ) ) ).

tff(extensionality, axiom,
    ! [A: nset, B: nset] : ( ( ! [X: node] : (mem(X,A) <=> mem(X,B)) ) => A = B ) ).

% --- cardinality is a natural number, and dropping a witnessed element from
% a subset strictly decreases it relative to the superset (same finite-set
% facts as scc_decrease.p; mask is a finite vertex set of the input graph).
tff(card_nonneg, axiom,
    ! [A: nset] : $greatereq(card(A), 0) ).

tff(card_strict_decrease, axiom,
    ! [A: nset, B: nset, W: node] :
      ( ( subset(A,B) & mem(W,B) & ~mem(W,A) )
        => $less(card(A), card(B)) ) ).

% --- one unfolding of R"reachable"'s third argument. frontier is
% deliberately uninterpreted: the proof may not, and does not, use anything
% about what TailsUnion/Restriction actually compute.
tff(step_def, axiom,
    ! [R: nset] : step(R) = cap(cup(R, frontier(R)), mask) ).

% --- intermediate: one step always lands inside the mask (this is also the
% single fact about step that reachable_value.p imports), and on masked
% arguments the step is inflationary.
tff(step_in_mask, lemma,
    ! [R: nset] : subset(step(R), mask) ).

tff(step_inflationary, lemma,
    ! [R: nset] : ( subset(R, mask) => subset(R, step(R)) ) ).

% --- intermediate: growing the subtracted set shrinks the complement.
tff(complement_antitone, lemma,
    ! [R: nset] :
      ( subset(R, step(R))
        => subset(setminus(mask, step(R)), setminus(mask, R)) ) ).

% --- intermediate: a strict growth step has a witness element (this is
% where extensionality earns its keep: step(R) != R plus R subset= step(R)
% forces some element of step(R) outside R)...
tff(growth_has_witness, lemma,
    ! [R: nset] :
      ( ( subset(R, step(R)) & step(R) != R )
        => ? [W: node] : ( mem(W, step(R)) & ~mem(W, R) ) ) ).

% --- ...and that witness lies in mask \ R but not in mask \ step(R), which
% is exactly what card_strict_decrease needs.
tff(witness_separates_complements, lemma,
    ! [R: nset, W: node] :
      ( ( subset(step(R), mask) & mem(W, step(R)) & ~mem(W, R) )
        => ( mem(W, setminus(mask, R)) & ~mem(W, setminus(mask, step(R))) ) ) ).

% --- the theorem: (1) one step lands inside the mask; on masked arguments,
% (2) the step is inflationary and (3) strictly shrinks card(mask \ R)
% unless it is already at the fixpoint (at which point the idempotence cut
% terminates the recursion).
tff(reachable_step_decreases, conjecture,
    ! [R: nset] :
      ( subset(step(R), mask)
      & ( subset(R, mask)
          => ( subset(R, step(R))
             & ( step(R) != R
                 => $less(card(setminus(mask, step(R))), card(setminus(mask, R))) ) ) ) ) ).
