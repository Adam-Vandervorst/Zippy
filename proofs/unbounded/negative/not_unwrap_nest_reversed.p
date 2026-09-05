% =========================================================================
% NEGATIVE CONTROL — this conjecture is FALSE and MUST NOT be provable.
%
% `unwrap(unwrap(A,U),V) = unwrap(A, app(V,U))` — the REVERSED nesting order for
% unwrap.  Unwrap STRIPS FROM THE FRONT, so the inner prefix U is consumed first
% and the true law is `unwrap(A, app(U,V))`.  The two operators nest in OPPOSITE
% orders, which is precisely the pair a hand transcription gets wrong.
%
% TRUE COUNTERPART: wrap_nest.p (PROVED — see ../STATUS.tsv).  Same axiom modules,
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
include('../_concat_ops.p').

tff(not_unwrap_nest_reversed, conjecture,
    ! [A: space, U: path, V: path] : unwrap(unwrap(A,U),V) = unwrap(A, app(V,U)) ).
