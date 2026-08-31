% ===========================================================================
% TIER 3 / fixpoint.  ACCUMULATOR = LAST ITERATE — BASE CASE.
%
% `acc(0) = init = cur(0)`, immediately from the two base axioms of `_kleene.p`.
% The step case (`kleene_acc_is_cur_step.p`) is where the work is, and where the
% EXTENSIVITY of the body is needed.  Together they give `ForAll N: acc(N) =
% cur(N)` by induction on the recursion depth — the premise that lets
% `kleene_conv.p` read the Scala loop's stopping test (`nxt == cur`, a test on
% the ITERATE) as a statement about the value the loop RETURNS (the accumulator).
%
% GENERALISES: nothing at tier-1/tier-2; both treat `Fixpoint` as one opaque node.
%
% VERDICT: PROVED by vampire in 0.0s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_fix_ops.p').
include('_kleene.p').

tff(kleene_acc_is_cur_base, conjecture, acc(z) = cur(z) ).
