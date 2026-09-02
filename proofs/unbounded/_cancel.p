% =============================================================================
% TIER 3 add-on: LEFT CANCELLATION of path append, AS A PROVED LEMMA.
%
%     app(P,Q) = app(P,R)  =>  Q = R
%
% IT IS NO LONGER AN ADMISSION.  This statement is DISCHARGED in this corpus by
% `mon_cancel.p` (PROVED — see STATUS.tsv), from `_paths.p` plus the one
% induction-schema instance in `_path_induction.p`, whose two premises are
% themselves the separately-PROVED `mon_cancel_base.p` and `mon_cancel_step.p`.
% What it used to be is worth recording, because it is the thing that changed:
% the fact was ADMITTED here, un-derived, and `wrap_roundtrip.p` and
% `card_wrap.p` were reported as PROVED while resting on it.
%
% WHY IT IS STILL A SEPARATE FILE.  Re-deriving it inside every consumer means
% carrying `_path_induction.p`'s nested-quantifier axiom through those searches.
% MEASURED 2026-09-02: `wrap_roundtrip.p` and `card_wrap.p` close in 0.08 s / 12.2 s with
% this one clause and did not close at a 180 s portfolio budget with
% `_path_induction.p` in place of it.  Asserting an already-proved lemma with a
% cheap form is the same discipline `terminating/fixpoint_is_lfp.smt2` applies
% to its four set-algebra stepping stones: PROVE it, then assert it, and say
% where the proof is.
%
% THE DEPENDENCY IS THEREFORE:  _path_induction.p (schema instance, trusted)
%                            +  _paths.p          (the free-monoid axioms)
%                            => mon_cancel.p      (PROVED)
%                            => this clause       (a proved lemma, re-asserted)
%                            => wrap_roundtrip.p, card_wrap.p
%
% RIGHT cancellation (`app(Q,P) = app(R,P) => Q = R`) is also true and is NOT
% assumed — nothing in the operator table needs it (`unwrap`/`wrap` strip and
% prepend on the LEFT), and assuming an unused axiom only widens the search.
% =============================================================================

tff(app_cancel_l, axiom,
    ! [P: path, Q: path, R: path] : ( app(P,Q) = app(P,R) => Q = R ) ).
