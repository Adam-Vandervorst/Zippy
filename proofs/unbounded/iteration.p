% ===========================================================================
% TIER 3 / iteration.
%
% ITERATION IS MONOTONE IN ITS SOURCE, given a monotone body — and it is
% EMPTY on a source with no heads.  Both degenerate sources are covered: `{}` and
% `{eps}` run zero head groups, which is exactly the HEADEDNESS guard
% docs/traps.md 1 insists on ("`{eps}` is non-empty yet runs zero head-groups"):
% the guard is not `nonEmpty`, it is "has a head".
% The body is quantified over — `F : bodyF` ranges over ALL iteration bodies —
% which is the thing neither tier-1 nor tier-2 can do: both re-analyse the one
% concrete body AST they are handed.
%
% GENERALISES: SpatialCost's generic Iteration transfer (`groups = ms.heads;
% ... cb.scale(groupsLo, groups)`) and tier-1's Iteration arm
%
% VERDICT: PROVED by vampire in 0.7s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_tails_ops.p').
include('_iter_ops.p').

tff(iteration, conjecture,
    ! [A: space, B: space, F: bodyF] :
      ( iter(empty, F) = empty
      & iter(sing(nil), F) = empty
      & ( ( monoB(F) & sub(A,B) ) => sub(iter(A,F), iter(B,F)) ) ) ).
