% ===========================================================================
% TIER 3 / fixpoint.  KLEENE BELOW EVERY PRE-FIXPOINT — BASE CASE.
%
% Depth 0 of the induction whose step is `kleene_below_step.p` and whose
% conclusion `kleene_conv.p` consumes: at depth 0 both the iterate and the
% accumulator are the seed, so both lie below any pre-fixpoint X of the body.
%
% The invariant is the CONJUNCTION `sub(cur(N),X) & sub(acc(N),X)`, not just the
% accumulator: the step case needs the iterate's bound to push through the body,
% and an induction on `acc` alone does not go through.  This is the same
% two-sequence invariant terminating/reachable_value.p carries for R"reachable".
%
% GENERALISES: nothing in tier-1 or tier-2 — tier-2's whole `Fixpoint` arm is
% the single ground edge `n >= n_init` with `hi = inf`
% (docs/design_size_constraints.md), which says nothing about what the loop
% converges TO.
%
% VERDICT: PROVED by vampire in 0.0s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_fix_ops.p').
include('_kleene.p').

tff(kleene_below_base, conjecture,
    ! [X: space] :
      ( ( sub(i0,X) & sub(ap1(g0,X), X) )
     => ( sub(cur(z), X) & sub(acc(z), X) ) ) ).
