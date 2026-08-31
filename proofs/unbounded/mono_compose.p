% ===========================================================================
% TIER 3 / composition.
%
% COMPOSITION IS MONOTONE IN BOTH ARGUMENTS.  Split out of both
% `composition_distrib.p` and `mono_concat.p`: in each of those it was the one
% conjunct that pushed an otherwise-fast goal into a timeout (5.6 s -> 60 s and
% 6.6 s -> 90 s respectively), because it is the only conjunct whose proof has
% to unpack `comp_def`'s two existentials on both sides.
%
% This is the law that licenses replacing either factor of a product by a
% superset when over-approximating, which is what every widening step of the
% spatial analysis does to a `Composition` node.
%
% GENERALISES: tier-1's Composition size arm (`n_a * n_b`, monotone in each
% factor by construction) and the `Composition` arm of SpatialTypes.infer
%
% VERDICT: PROVED by vampire in 0.7s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').

tff(mono_compose, conjecture,
    ! [A: space, B: space, C: space, D: space] :
      ( ( sub(A,B) & sub(C,D) ) => sub(comp(A,C), comp(B,D)) ) ).
