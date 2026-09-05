% ===========================================================================
% TIER 3 / paths.  LEFT CANCELLATION — BASE CASE.
%
%     app(nil,Q) = app(nil,R)  =>  Q = R
%
% Depth 0 of the induction whose step is `mon_cancel_step.p` and whose ForAll-P
% conclusion is the axiom `_cancel.p` imports into `wrap_roundtrip.p` and
% `card_wrap.p`.  Immediate from `app_nil_l`, and recorded as an explicit
% obligation anyway: the point of the split is that BOTH halves of the induction
% are machine-checked, leaving only the induction principle itself as the
% unmechanised step (see `mon_cancel.p`, which is the direct ForAll-P attempt and
% is OPEN).
%
% GENERALISES: the `(= q nil)` arm of the certified split lemma
% proofs/lemma_append_cons.smt2.
%
% VERDICT: PROVED by vampire in 0.0s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').

tff(mon_cancel_base, conjecture,
    ! [Q: path, R: path] : ( app(nil,Q) = app(nil,R) => Q = R ) ).
