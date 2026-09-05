% =========================================================================
% NEGATIVE CONTROL — this conjecture is FALSE and MUST NOT be provable.
%
% Iteration splits over an ARBITRARY union of sources.  False: a SHARED head
% merges the two rest-groups into ONE call of the body on the combined rest-space,
% which is not the union of the two separate calls.  docs/traps.md 1 records the
% same shape as "`IterateLiteral_Union` must group by distinct HEAD, not unroll
% per path".  `iteration_split.p` proves the head-disjoint version.
%
% TRUE COUNTERPART: iteration_split.p (PROVED — see ../STATUS.tsv).  Same axiom modules,
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
include('../_lattice_lemmas.p').
include('../_paths.p').
include('../_tails_ops.p').
include('../_grp_lemmas.p').
include('../_iter_ops.p').

tff(not_iter_split, conjecture,
    ! [A: space, B: space, F: bodyF] : iter(cup(A,B),F) = cup(iter(A,F), iter(B,F)) ).
