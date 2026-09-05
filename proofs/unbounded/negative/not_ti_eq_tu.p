% =========================================================================
% NEGATIVE CONTROL — this conjecture is FALSE and MUST NOT be provable.
%
% `ti(A) = tu(A)` UNCONDITIONALLY.  True only when A has exactly one head
% (`tails_intersection.p` proves the guarded form).  With two heads the
% intersection of the two groups is generally a proper subset of their union.
%
% TRUE COUNTERPART: tails_intersection.p (PROVED — see ../STATUS.tsv).  Same axiom modules,
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
include('../_paths.p').
include('../_tails_ops.p').

tff(not_ti_eq_tu, conjecture,
    ! [A: space] : ti(A) = tu(A) ).
