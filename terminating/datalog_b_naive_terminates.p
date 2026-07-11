% =============================================================================
% Termination of the THREE NAIVE MORKL Datalog programs in datalog_b.txt:
%
%   tc  - transitive closure:   tc(e, acc)            = acc \/ tc(e, g_tc(acc))
%   rsg - reverse same-gen:     rsg(up,flat,down, s)  = s   \/ rsg(..., g_rsg(s))
%   pt  - Andersen points-to:   pt(addr,assign, p)    = p   \/ pt(..., g_pt(p))
%
% Unlike datalog_a.txt's programs, the recursive call does NOT union the old
% state into the new argument - the printed argument updates are
%
%   g_tc(R)  = e        \/ Iteration(R, n, nbs, Wrap(TailsUnion(e <| nbs), n))
%   g_pt(R)  = addressOf \/ Iteration(assign, n, nbs, Wrap(TailsUnion(R <| nbs), n))
%   g_rsg(R) = flat     \/ Iteration(Iteration(up, n, nbs,
%                            Wrap(TailsUnion(swap(R) <| nbs), n)),
%                            n, nbs, Wrap(TailsUnion(down <| nbs), n))
%
% where the Iteration/Wrap/TailsUnion/Restriction pattern over 2-item paths
% is exactly RELATIONAL COMPOSITION,
%     comp(A,B) = { x.z : x.y in A, y.z in B },
% and rsg's inner Iteration/Singleton pattern is the CONVERSE,
%     inv(A) = { x.y : y.x in A }.
% Under that reading (mem2 axioms below give both their defining semantics):
%
%   g_tc(R)  = e         \/ comp(R, e)
%   g_pt(R)  = addressOf \/ comp(assign, R)
%   g_rsg(R) = flat      \/ comp(comp(up, inv(R)), down)
%
% So the step is NOT inflationary at arbitrary states; instead the run
% satisfies the invariant  R subset= g(R)  ("expanded state"):
%   - at the seed: each invocation passes the base relation itself as the
%     initial accumulator (acc0 = e, p0 = addressOf... rsg0 = flat - see the
%     invoke: blocks), and base subset= g(R) holds for EVERY R (first
%     conjunct below), so the seed is expanded;
%   - preserved by the step: g is MONOTONE (comp/inv/cup monotonicity - the
%     lemma-role stones below, each independently machine-checked from the
%     mem2 semantics alone), so R subset= g(R) gives g(R) subset= g(g(R)).
% On expanded states a non-fixpoint step strictly shrinks card(top \ R)
% (bounded_growth_decrease.p), where `top` - all 2-item paths over the
% items of the seed literals - is finite because comp/inv/cup only permute
% existing items, never mint new ones (fixed arity 2, fixed item universe;
% same "no fresh constants" boundary as datalog_a_terminates.p /
% reachable_decrease.p). Paired with no_infinite_descent.smt2: the argument
% chain stabilizes within card(top) steps; the carried arguments (e /
% addressOf,assign / up,flat,down) pass through every call UNCHANGED, so the
% full argument tuple repeats exactly when the accumulator does, the
% recursion's argument-repeat cut ("no new facts") fires, and each program
% terminates. The concrete Literal seeds in datalog_b.txt are instances of
% the universally quantified statement - nothing below depends on the
% particular graphs.
% =============================================================================

tff(node_type, type, node: $tType ).
tff(nset_type, type, nset: $tType ).

tff(mem2_type, type, mem2: (node * node * nset) > $o ).
tff(subset_type, type, subset: (nset * nset) > $o ).
tff(card_type, type, card: nset > $int ).
tff(setminus_type, type, setminus: (nset * nset) > nset ).
tff(cup_type, type, cup: (nset * nset) > nset ).
tff(comp_type, type, comp: (nset * nset) > nset ).
tff(inv_type, type, inv: nset > nset ).
tff(top_type, type, top: nset ).

tff(e_type, type, e: nset ).
tff(addressof_type, type, addressof: nset ).
tff(assign_type, type, assign: nset ).
tff(up_type, type, up: nset ).
tff(flat_type, type, flat: nset ).
tff(down_type, type, down: nset ).

tff(gtc_type, type, gtc: nset > nset ).
tff(gpt_type, type, gpt: nset > nset ).
tff(grsg_type, type, grsg: nset > nset ).

% --- membership semantics of the operators actually used by the programs.
tff(mem2_cup, axiom,
    ! [X: node, Y: node, A: nset, B: nset] :
      ( mem2(X,Y,cup(A,B)) <=> ( mem2(X,Y,A) | mem2(X,Y,B) ) ) ).

tff(subset_def, axiom,
    ! [A: nset, B: nset] :
      ( subset(A,B) <=> ( ! [X: node, Y: node] : (mem2(X,Y,A) => mem2(X,Y,B)) ) ) ).

tff(mem2_comp, axiom,
    ! [X: node, Z: node, A: nset, B: nset] :
      ( mem2(X,Z,comp(A,B)) <=> ( ? [Y: node] : ( mem2(X,Y,A) & mem2(Y,Z,B) ) ) ) ).

tff(mem2_inv, axiom,
    ! [X: node, Y: node, A: nset] : ( mem2(X,Y,inv(A)) <=> mem2(Y,X,A) ) ).

tff(mem2_top, axiom,
    ! [X: node, Y: node] : mem2(X,Y,top) ).

tff(card_nonneg, axiom,
    ! [A: nset] : $greatereq(card(A), 0) ).

% --- the three programs' argument updates, transcribed from datalog_b.txt.
tff(gtc_def, axiom,
    ! [R: nset] : gtc(R) = cup(e, comp(R, e)) ).

tff(gpt_def, axiom,
    ! [R: nset] : gpt(R) = cup(addressof, comp(assign, R)) ).

tff(grsg_def, axiom,
    ! [R: nset] : grsg(R) = cup(flat, comp(comp(up, inv(R)), down)) ).

% --- stepping stones, each independently machine-checked standalone from
% the mem2 axioms above (staging discipline of scc_decrease.p).
tff(comp_mono1, lemma,
    ! [A: nset, B: nset, C: nset] : ( subset(A,B) => subset(comp(A,C), comp(B,C)) ) ).

tff(comp_mono2, lemma,
    ! [A: nset, B: nset, C: nset] : ( subset(A,B) => subset(comp(C,A), comp(C,B)) ) ).

tff(inv_mono, lemma,
    ! [A: nset, B: nset] : ( subset(A,B) => subset(inv(A), inv(B)) ) ).

tff(cup_mono2, lemma,
    ! [A: nset, B: nset, C: nset] : ( subset(A,B) => subset(cup(C,A), cup(C,B)) ) ).

% --- proved in bounded_growth_decrease.p, imported as a premise.
tff(bounded_growth_decrease, lemma,
    ! [R: nset, S: nset, U: nset] :
      ( ( subset(R,S) & subset(S,U) & S != R )
        => $less(card(setminus(U,S)), card(setminus(U,R))) ) ).

% --- the theorem, three conjuncts per program: the seed is expanded (base
% subset= g(R) for every R, in particular at the seed base itself), the
% expanded-state invariant is preserved, and a non-fixpoint step on an
% expanded state strictly shrinks card(top \ R).
tff(datalog_b_naive_all_three_terminate, conjecture,
    ! [R: nset] :
      ( subset(e, gtc(R))
      & ( subset(R, gtc(R)) => subset(gtc(R), gtc(gtc(R))) )
      & ( ( subset(R, gtc(R)) & gtc(R) != R )
          => $less(card(setminus(top, gtc(R))), card(setminus(top, R))) )
      & subset(addressof, gpt(R))
      & ( subset(R, gpt(R)) => subset(gpt(R), gpt(gpt(R))) )
      & ( ( subset(R, gpt(R)) & gpt(R) != R )
          => $less(card(setminus(top, gpt(R))), card(setminus(top, R))) )
      & subset(flat, grsg(R))
      & ( subset(R, grsg(R)) => subset(grsg(R), grsg(grsg(R))) )
      & ( ( subset(R, grsg(R)) & grsg(R) != R )
          => $less(card(setminus(top, grsg(R))), card(setminus(top, R))) ) ) ).
