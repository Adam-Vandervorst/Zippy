% =========================================================================
% NEGATIVE CONTROL — this conjecture is FALSE and MUST NOT be provable.
%
% `|A u B| = |A| + |B|` without disjointness.  `_card.p` assumes additivity
% only for DISJOINT spaces; if this unconditional form were derivable the
% inclusion-exclusion theorem would collapse and `card` would not be a measure.
% This control is what shows `card_subadd.p`'s `=<` is not secretly an `=`.
%
% TRUE COUNTERPART: card_subadd.p (PROVED — see ../STATUS.tsv).  Same axiom modules,
% same prover, same flags: if this file is ever reported PROVED, the encoding is
% broken (an inconsistent axiom set, or a definition transcribed with the wrong
% polarity) and every verdict in the corpus is void.  run.sh treats a refutation
% here as a HARD FAILURE.
%
% VERDICT: NOT-PROVED (the expected outcome) — vampire exhausts a 60 s budget without a
% refutation, while the file's true counterpart closes in seconds from the same axioms.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% =========================================================================

include('../_signature.p').
include('../_nat.p').
include('../_card.p').

tff(not_card_additive, conjecture,
    ! [A: space, B: space] : card(cup(A,B)) = plus(card(A), card(B)) ).
