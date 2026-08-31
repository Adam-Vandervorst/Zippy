% ===========================================================================
% TIER 3 / fixpoint.  THE ACCUMULATOR CONTAINS THE SEED — BASE CASE.
%
% `acc(0) = init`, so trivially `sub(init, acc(0))`.  Recorded as an explicit
% obligation rather than waved through because it is one of the two halves the
% hand-staged induction in `kleene_conv.p` consumes, and because it is the arm
% that distinguishes `acc` from `cur`: `cur(0) = init` too, but `cur` does NOT
% keep the seed at later depths — only the accumulation does.  That is exactly
% why `eval` carries both variables.
%
% GENERALISES: docs/design_size_constraints.md's tier-2 closure edge
% `init subset= Fixpoint(init, ...)` — one ground edge in one saturated relation
% there, the depth-0 case of a statement about all depths here.
%
% VERDICT: PROVED by vampire in 0.0s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_fix_ops.p').
include('_kleene.p').

tff(kleene_grows_base, conjecture, sub(i0, acc(z)) ).
