% ===========================================================================
% TIER 3 / paths.  LEFT CANCELLATION OF APPEND, as a THEOREM.
%
%     app(P,Q) = app(P,R)  =>  Q = R
%
% This file deliberately does NOT include `_cancel.p`.  `_cancel.p` is the same
% statement in assertional form, and keeping it out is what makes this file a
% real obligation instead of a tautology.
%
% WHAT IT RESTS ON.  `_path_induction.p`: the STRUCTURAL INDUCTION SCHEMA for
% the free term algebra `path`, instantiated at this one predicate.  That axiom
% says nothing about what `app` computes — the same schema instance is valid for
% any property of paths — and it leaves BOTH of its premises as obligations
% vampire must discharge from `_paths.p` before the implication is usable:
%
%     base   ForAll Q,R. app(nil,Q) = app(nil,R) => Q = R
%     step   ForAll H,T. (base-at-T) => (base-at-cons(H,T))
%
% Those two are ALSO separately certified in this corpus, as `mon_cancel_base.p`
% and `mon_cancel_step.p` (both PROVED), so the derivation can be read off the
% status table without reading a proof object.
%
% HOW IT USED TO STAND, AND WHY THAT WAS NOT GOOD ENOUGH.  It was OPEN: the
% conclusion was admitted as the axiom `_cancel.p` and imported by
% `wrap_roundtrip.p` and `card_wrap.p`, so those two theorems were PROVED
% RELATIVE TO AN ADMITTED DOMAIN FACT about `app` while the status table showed
% them as plainly PROVED.  What is trusted now is one instance of a standard
% induction schema, named in `_path_induction.p`, with both premises checked.
%
% ATTEMPT LOG for the fully automatic route (vampire 5.1.0, 16-core x86_64
% Linux 6.17), kept because a future edit that removes `_path_induction.p`
% expecting the prover to cope will look harmless:
%   vampire --mode casc -t 120s                                      Timeout
%   vampire --mode casc --induction struct -t 120s                   Timeout
%   vampire --mode casc --induction int -t 120s                      Timeout
%   vampire --mode casc -t 180s                                      Timeout
%   2026-09-02, SMT-LIB2 rendering with `declare-datatypes` for Path:
%     vampire --input_syntax smtlib2 --induction struct -t 100s      Timeout
%     vampire --input_syntax smtlib2 --mode casc --induction struct  Timeout
%     the same with `define-fun-rec app`                             Timeout
%     z3 -T:50                                                       timeout
% No countermodel from any of them, as expected — the statement is true.
%
% GENERALISES: the `(cons k2 p) = (append q r)` split lemma certified in
% proofs/lemma_append_cons.smt2, which is the FINITE-DEPTH consequence z3 can
% discharge from `declare-datatypes`; cancellation is its unbounded form.
%
% VERDICT: PROVED by vampire in 0.02s (DEFAULT mode; 0.12s under --mode casc).
% MEASURED 2026-09-02, vampire 5.1.0 (commit 7b2f410), 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_path_induction.p').

tff(mon_cancel, conjecture,
    ! [P: path, Q: path, R: path] :
      ( app(P,Q) = app(P,R) => Q = R ) ).
