% =========================================================================
% NEGATIVE CONTROL — this conjecture is FALSE and MUST NOT be provable.
%
% `tu(A n B) = tu(A) n tu(B)`.  Only `sub` holds: a tail can occur under head
% h in A and under a DIFFERENT head k in B, so it is in both tails-unions without
% being in the tails-union of the intersection.
%
% TRUE COUNTERPART: tails_union.p (PROVED — see ../STATUS.tsv).  Same axiom modules,
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

tff(not_tu_cap_equality, conjecture,
    ! [A: space, B: space] : tu(cap(A,B)) = cap(tu(A), tu(B)) ).
