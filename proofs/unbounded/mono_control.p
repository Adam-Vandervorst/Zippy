% ===========================================================================
% TIER 3 / iteration / fixpoint.
%
% MONOTONICITY OF THE TWO CONTROL-FLOW OPERATORS, collected: iteration in its
% source (given a monotone body), the fixpoint in its seed (unconditionally), and
% the fixpoint's Park-induction principle in usable form — if X is any
% pre-fixpoint above the seed, the fixpoint is below it.  The last is the rule an
% abstract interpretation would need in order to certify a widened fixpoint
% result, which is currently done by round-counting instead.
%
% GENERALISES: the Iteration/Fixpoint arms of SpatialTypes.infer and
% SpatialCost.fixRounds
%
% VERDICT: PROVED by vampire in 4.3s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_tails_ops.p').
include('_iter_ops.p').
include('_fix_ops.p').

tff(mono_control, conjecture,
    ! [A: space, B: space, I: space, J: space, X: space, F: bodyF, G: bodyG] :
      ( ( ( monoB(F) & sub(A,B) ) => sub(iter(A,F), iter(B,F)) )
      & ( sub(I,J) => sub(fix(I,G), fix(J,G)) )
      & ( ( sub(I,X) & sub(ap1(G,X),X) ) => sub(fix(I,G), X) ) ) ).
