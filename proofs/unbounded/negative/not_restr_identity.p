% =========================================================================
% NEGATIVE CONTROL — this conjecture is FALSE and MUST NOT be provable.
%
% `restr(X,Y) = X`.  Restriction is the identity only when the prefix set
% contains the empty path (`restriction.p` proves `restr(X, sing(nil)) = X`); in
% general it FILTERS.  If this were provable the restriction/raffination partition
% would be vacuous, since the raffination would always be empty.
%
% TRUE COUNTERPART: restriction.p (PROVED — see ../STATUS.tsv).  Same axiom modules,
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
include('../_prefix.p').
include('../_prefix_ops.p').

tff(not_restr_identity, conjecture,
    ! [X: space, Y: space] : restr(X,Y) = X ).
