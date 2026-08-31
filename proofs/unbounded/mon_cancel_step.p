% ===========================================================================
% TIER 3 / paths.  LEFT CANCELLATION — STEP CASE.
%
%   (ForAll Q,R. app(T,Q) = app(T,R) => Q = R)
%     =>  (ForAll Q,R. app(H::T,Q) = app(H::T,R) => Q = R)
%
% `app(cons(H,T),Q) = cons(H, app(T,Q))` by `app_cons`, so injectivity of `cons`
% peels the head off both sides and the induction hypothesis finishes.  Note the
% hypothesis has to be quantified over Q and R INSIDE the induction — a version
% carrying fixed Q, R does not go through, which is the usual reason a
% cancellation proof is generalised before it is inducted.
%
% With `mon_cancel_base.p` this gives `ForAll P,Q,R. app(P,Q) = app(P,R) => Q = R`
% by induction on P, which is exactly the axiom `_cancel.p` states.  The
% induction principle itself is the one step in this corpus that is NOT
% machine-checked: `path` is an opaque TFF sort, so vampire has no
% structural-induction rule for it (see `mon_cancel.p`'s attempt log).  The
% staging is the same hand-staged induction terminating/no_infinite_descent.smt2
% uses, and it is recorded here rather than hidden.
%
% GENERALISES: the `?q2. q = cons(k2,q2)` arm of the certified split lemma
% proofs/lemma_append_cons.smt2.
%
% VERDICT: PROVED by vampire in 0.1s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').

tff(mon_cancel_step, conjecture,
    ! [H: item, T: path] :
      ( ( ! [Q: path, R: path] : ( app(T,Q) = app(T,R) => Q = R ) )
     => ( ! [Q: path, R: path] : ( app(cons(H,T),Q) = app(cons(H,T),R) => Q = R ) ) ) ).
