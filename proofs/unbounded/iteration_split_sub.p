% ===========================================================================
% TIER 3 / iteration.
%
% ITERATION SPLITS OVER A HEAD-DISJOINT UNION OF SOURCES.  If no head is
% shared, the head groups of the union are exactly the head groups of the two
% sides, so the iteration decomposes.  The guard is essential and is stated in
% full: with a SHARED head the two groups MERGE into one call of the body on the
% combined rest-space, and `cup(iter(S1,F), iter(S2,F))` is then wrong — a
% union-of-iterations is not an iteration-of-union.  docs/traps.md 1 records the
% same shape as "`IterateLiteral_Union` must group by distinct HEAD, not unroll
% per path".
%
% FORM.  The three arguments are SKOLEM CONSTANTS (`a0`, `b0`, `f0`) with the
% head-disjointness guard as an axiom, rather than universally quantified
% variables with the guard as an antecedent.  The two are logically the same
% statement — proving it for uninterpreted constants IS proving it for all
% spaces and all bodies — but the constant form is dramatically easier for
% saturation: MEASURED, the quantified form did not close in 90 s while this one
% closes in seconds, because the negated guard no longer has to be re-Skolemised
% inside every inference.
%
% The head-group lemmas come from `grp_union.p` via `_grp_lemmas.p` (PROVED),
% and the lattice facts from `_lattice_lemmas.p`; neither mentions `iter`.
%
% GENERALISES: IterUnion_Indep / the same-source iteration merges in SC.reduce
%
%
% THIS FILE: THE FORWARD INCLUSION.  Every path the iteration over the merged
% source produces already comes out of one of the two component iterations.
%
% VERDICT: PROVED by vampire in 0.8s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_lattice_lemmas.p').
include('_paths.p').
include('_tails_ops.p').
include('_grp_lemmas.p').
include('_iter_ops.p').

tff(a0_type, type, a0: space ).
tff(b0_type, type, b0: space ).
tff(f0_type, type, f0: bodyF ).

% the guard: a0 and b0 share no head
tff(head_disjoint, axiom, ! [H: item] : ~ ( headed(H,a0) & headed(H,b0) ) ).

tff(iteration_split_sub, conjecture,
    sub(iter(cup(a0,b0), f0), cup(iter(a0,f0), iter(b0,f0))) ).
