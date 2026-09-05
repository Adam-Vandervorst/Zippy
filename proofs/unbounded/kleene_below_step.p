% ===========================================================================
% TIER 3 / fixpoint.  KLEENE BELOW EVERY PRE-FIXPOINT — STEP CASE.
%
% One round of `eval`'s fixpoint loop preserves the invariant
% `sub(cur(N),X) & sub(acc(N),X)` for any pre-fixpoint X of the body:
%
%   cur(N+1) = body[cur(N)] <= body[X] <= X      (monotone body, then X pre-fix)
%   acc(N+1) = acc(N) u cur(N+1) <= X            (both halves below X)
%
% MONOTONICITY OF THE BODY IS REQUIRED and is stated as a hypothesis rather than
% assumed globally — the first inclusion is the only place it is used, and a
% non-monotone body genuinely breaks it.  `SpatialCost.fixRounds` decides body
% monotonicity by a purely SYNTACTIC pattern match on `Union(Mention(rec), _)`;
% this is the semantic property that pattern is standing in for.
%
% With `kleene_below_base.p` this gives, by induction on the recursion depth,
% `ForAll N: sub(acc(N), X)` for every pre-fixpoint X — in particular for
% `fix(i0,g0)`, which is the inclusion `kleene_conv.p` imports.
%
% GENERALISES: terminating/least_fixpoint_unique.p, which assumes a least
% solution exists and shows it is unique; this shows the LOOP stays below every
% solution.
%
% VERDICT: PROVED by vampire in 0.3s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_fix_ops.p').
include('_kleene.p').

tff(kleene_below_step, conjecture,
    ! [N: idx, X: space] :
      ( ( monoG(g0) & sub(i0,X) & sub(ap1(g0,X), X)
        & sub(cur(N), X) & sub(acc(N), X) )
     => ( sub(cur(s(N)), X) & sub(acc(s(N)), X) ) ) ).
