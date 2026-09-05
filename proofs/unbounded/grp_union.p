% ===========================================================================
% TIER 3 / iteration.
%
% HEAD GROUPS OF A UNION.  `grp(h, A u B) = grp(h,A) u grp(h,B)`, and a head
% that does not occur in B contributes an EMPTY group there.  Together these are
% the reason an iteration can be split across a head-disjoint union
% (`iteration_split.p`): with no shared head, one of the two groups is empty at
% every head, so the merged group is just the other one.
%
% The second conjunct is where the `{}` / `{eps}` distinction of docs/traps.md 1
% lives: "h is not a head of B" is NOT "B is empty", and the group is empty for
% either reason.  The last two conjuncts are the COLLAPSED form the iteration
% split actually consumes — MEASURED: with only the first three staged,
% `iteration_split.p` still timed out at 90 s; with the collapsed form staged it
% closes, because the prover no longer has to rediscover `cup(X,empty) = X`
% under the head-group definition on every branch.
%
% GENERALISES: the `groupMap(_._1)(_._2)` grouping in `eval`'s Iteration arm,
% which performs this merge concretely for one source value.
%
% VERDICT: PROVED by vampire in 0.3s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_lattice_lemmas.p').
include('_tails_ops.p').

tff(grp_union, conjecture,
    ! [H: item, A: space, B: space] :
      ( grp(H, cup(A,B)) = cup(grp(H,A), grp(H,B))
      & ( ~ headed(H,B) => grp(H,B) = empty )
      & ( headed(H, cup(A,B)) <=> ( headed(H,A) | headed(H,B) ) )
      & ( ~ headed(H,B) => grp(H, cup(A,B)) = grp(H,A) )
      & ( ~ headed(H,A) => grp(H, cup(A,B)) = grp(H,B) ) ) ).
