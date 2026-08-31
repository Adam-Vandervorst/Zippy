% ===========================================================================
% TIER 3 / paths.  LEFT CANCELLATION OF APPEND, as a THEOREM attempt.
%
%     app(P,Q) = app(P,R)  =>  Q = R
%
% This file deliberately does NOT include `_cancel.p` — `_cancel.p` is the
% axiom form of exactly this statement, imported by `wrap_roundtrip.p` and
% `card_wrap.p`.  Keeping it out is what makes this file a real obligation
% instead of a tautology.
%
% THE STAGED PROOF IS IN THE CORPUS.  `mon_cancel_base.p` and
% `mon_cancel_step.p` discharge the two halves of the induction on P as ordinary
% first-order obligations (both PROVED), and the ForAll-P statement follows from
% them by induction on the path.  THIS file is the DIRECT attempt — the same
% statement handed to the prover with no staging — and it stays in the corpus,
% OPEN, so the one unmechanised step in tier 3 (the induction principle itself)
% is visible in STATUS.tsv instead of being papered over by the staged pair.
%
% WHY IT IS HARD.  The fact is true in the free monoid and its proof is the
% textbook induction on P: base `app(nil,Q) = Q`, step `app(cons(H,T),Q) =
% cons(H, app(T,Q))` plus injectivity of `cons`.  Both halves ARE in
% `_paths.p`.  What is missing is the INDUCTION PRINCIPLE.  Saturation-based
% first-order proving has no induction rule, and `path` is declared as an
% opaque `$tType` in TFF, so vampire's `--induction struct` has no term-algebra
% declaration to induct over either; `--induction int` has no integer to
% recurse on unless the statement is re-indexed by `plen`, which changes the
% statement.
%
% GENERALISES: the `(cons k2 p) = (append q r)` split lemma certified in
% proofs/lemma_append_cons.smt2, which is the FINITE-DEPTH consequence z3 can
% discharge from `declare-datatypes`; cancellation is its unbounded form.
%
% ATTEMPT LOG (vampire 5.1.0, 16-core machine, 2026-08-31):
%   vampire --mode casc -t 120s                                      Timeout
%   vampire --mode casc --induction struct -t 120s                   Timeout
%   vampire --mode casc --induction int -t 120s                      Timeout
%   vampire --mode casc --induction struct
%           --structural_induction_kind all -t 120s                  Timeout
%   vampire --mode casc -t 180s                                      Timeout
% No countermodel either, as expected — the statement is true.  It is admitted
% as the axiom `_cancel.p` (used by exactly two theorems), justified by the
% staged pair above, and listed in run.sh's EXPECTED_OPEN.
%
% VERDICT: OPEN — no proof, no countermodel (180.0s budget exhausted).
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.  See the attempt log above.
% ===========================================================================

include('_signature.p').
include('_paths.p').

tff(mon_cancel, conjecture,
    ! [P: path, Q: path, R: path] :
      ( app(P,Q) = app(P,R) => Q = R ) ).
