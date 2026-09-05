% ===========================================================================
% TIER 3 / wrap.
%
% |wrap(A,W)| = |A| — wrapping is SIZE-PRESERVING.  This is the one
% cardinality fact in the corpus that does not follow from the inclusion lattice,
% and the proof shows exactly why: it needs the injective-image principle
% (`card_image` in `_card.p`), applied to the reified prefix map `pfxmap(W)`,
% whose injectivity on A is LEFT CANCELLATION of append (`_cancel.p`) and whose
% image is `wrap(A,W)` by `wrap_def`.  Neither `card_image` nor `_cancel.p`
% mentions `wrap`, so the theorem is a derivation, not a restatement of an axiom.
% Tier-1 gets `n = n_src` for free by fiat; this is the fact that makes it true.
%
% GENERALISES: tier-1's Wrap arm (`n = n_src` exactly) and the corresponding
% SizeConstraints equality constraint
%
% VERDICT: PROVED by vampire in 12.2s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').
include('_nat.p').
include('_card.p').
include('_card_image.p').
include('_cancel.p').

tff(card_wrap, conjecture,
    ! [A: space, W: path] :
      ( card(wrap(A,W)) = card(A) ) ).
