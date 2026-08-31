% ===========================================================================
% TIER 3 / fixpoint.
%
% THE FIXPOINT UNFOLDS: for a MONOTONE body, `fix(I,G) = I u G(fix(I,G))`.
% The forward inclusion is immediate from the two positive axioms; the reverse is
% the substantive half and is where monotonicity is used — `cup(I, G(fix))` has to
% be shown to be itself a pre-fixpoint before `fix_least` applies.  This is the
% equation `eval`'s `while` loop is computing one round at a time, and the reason
% tier-2 can only say `n >= n init, hi = inf` for the node.
%
% GENERALISES: docs/SUPERCOMPILER.md's denotation `init u body[init] u
% body^2[init] ...`; the `Fixpoint` arm of SizeConstraints (`n >= n init`,
% `hi = inf`)
%
% VERDICT: PROVED by vampire in 2.6s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_lattice_lemmas.p').
include('_fix_ops.p').

tff(fixpoint_unfold, conjecture,
    ! [I: space, G: bodyG] :
      ( ( monoG(G) => fix(I,G) = cup(I, ap1(G, fix(I,G))) ) ) ).
