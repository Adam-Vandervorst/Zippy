% =============================================================================
% TIER 3 add-on: LEFT CANCELLATION of path append.
%
%     app(P,Q) = app(P,R)  =>  Q = R
%
% TRUE in the free monoid over `item` — the standard induction on P: the base
% case is `app(nil,Q) = Q`, and the step case follows from `app(cons(H,T),Q) =
% cons(H, app(T,Q))` plus injectivity of `cons`.  Both halves are already in
% `_signature.p`; what is missing is the INDUCTION PRINCIPLE, which plain
% first-order saturation does not have.
%
% WHY IT IS AN AXIOM HERE AND NOT A LEMMA.  Deriving it inside a theorem file
% would need the induction rule in that file's search, which vampire only
% offers under `--induction`.  Rather than sprinkle induction flags across the
% corpus, the fact is isolated in this one file, imported ONLY by the three
% theorems that genuinely need it (wrap/unwrap round trips and the
% cardinality-of-wrap image argument), and the induction proof itself is
% attempted in `mon_cancel.p` with the attempt log in that file's header.  The
% split is what keeps `mon_cancel.p` non-vacuous: it does NOT include this file.
%
% RIGHT cancellation (`app(Q,P) = app(R,P) => Q = R`) is also true and is NOT
% assumed — nothing in the operator table needs it (`unwrap`/`wrap` strip and
% prepend on the LEFT), and assuming an unused axiom only widens the search.
% =============================================================================

tff(app_cancel_l, axiom,
    ! [P: path, Q: path, R: path] : ( app(P,Q) = app(P,R) => Q = R ) ).
