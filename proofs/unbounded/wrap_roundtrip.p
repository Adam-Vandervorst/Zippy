% ===========================================================================
% TIER 3 / wrap / unwrap.
%
% THE WRAP/UNWRAP ROUND TRIP: `unwrap(wrap(A,W),W) = A` for EVERY space A and
% EVERY prefix W, plus the two nil units.  This is the only theorem family in the
% corpus that needs LEFT CANCELLATION of append (`_cancel.p`): membership in
% `wrap(A,W)` gives some q in A with `app(W,q) = app(W,p)`, and only cancellation
% turns that into `q = p`.  Without it the round trip is genuinely unprovable, not
% merely hard — which is why `_cancel.p` is a separate, documented import and why
% its own induction proof is attempted in `mon_cancel.p`.
%
% GENERALISES: proofs/impl_wrap.smt2 + proofs/impl_unwrap.smt2 (instance
% tier: one wrap of one literal)
%
% VERDICT: PROVED by vampire in 0.1s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').
include('_cancel.p').

tff(wrap_roundtrip, conjecture,
    ! [A: space, W: path] :
      ( unwrap(wrap(A,W),W) = A
      & wrap(A,nil) = A
      & unwrap(A,nil) = A ) ).
