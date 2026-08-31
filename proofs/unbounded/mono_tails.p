% ===========================================================================
% TIER 3 / tails-union / tails-intersection.
%
% TAILS-UNION IS MONOTONE; TAILS-INTERSECTION IS NOT.  Growing a source can
% add a NEW HEAD, and the new head's group then intersects away tails that were in
% the old result — so `sub(A,B)` alone does NOT give `sub(ti(A),ti(B))`.  The
% sound rule is the GUARDED one: monotone provided B introduces no new head.
% Writing the unguarded version would be exactly the "cheaper superset guard"
% docs/traps.md 1 forbids, so it is stated with its guard and nothing weaker.
%
% GENERALISES: the TailsUnion/TailsIntersection arms of SpatialTypes.infer
%
% VERDICT: PROVED by vampire in 0.6s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_tails_ops.p').

tff(mono_tails, conjecture,
    ! [A: space, B: space, C: space] :
      ( ( sub(A,B) => sub(tu(A), tu(B)) )
      & ( ( sub(A,B) & ! [H: item] : ( headed(H,B) => headed(H,A) ) )
          => sub(ti(A), ti(B)) ) ) ).
