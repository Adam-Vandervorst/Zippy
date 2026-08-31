% =========================================================================
% NEGATIVE CONTROL — this conjecture is FALSE and MUST NOT be provable.
%
% `wrap(wrap(A,U),V) = wrap(A, app(U,V))` — the REVERSED nesting order.  Wrap
% PREPENDS, so the outer prefix V must end up in FRONT: the true law is
% `wrap(A, app(V,U))`.  docs/traps.md 4 records this exact inversion as a bug that
% shipped ("`UnwrapConcat_Unwraps` stripped Concat-prefix factors in reversed
% order"), which is why it is a control and not a hypothetical.
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

tff(not_wrap_nest_reversed, conjecture,
    ! [A: space, U: path, V: path] : wrap(wrap(A,U),V) = wrap(A, app(U,V)) ).
