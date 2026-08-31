% =========================================================================
% NEGATIVE CONTROL — this conjecture is FALSE and MUST NOT be provable.
%
% `sub(A,B) => sub(ti(A), ti(B))` UNGUARDED.  Growing the source can add a NEW
% HEAD whose group then intersects away tails that were in the old result, so
% tails-intersection is NOT monotone.  `mono_tails.p` proves the version guarded
% by "B introduces no new head" — the guard docs/traps.md 1 insists must be the
% exact enabling predicate and never a cheaper superset.
%
% TRUE COUNTERPART: mono_tails.p (PROVED — see ../STATUS.tsv).  Same axiom modules,
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

tff(not_ti_monotone, conjecture,
    ! [A: space, B: space] : ( sub(A,B) => sub(ti(A), ti(B)) ) ).
