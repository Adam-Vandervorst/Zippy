% ===========================================================================
% TIER 3 / composition / wrap / unwrap.
%
% MONOTONICITY of the three concatenation operators, plus wrap's distribution
% over union.  Wrap is monotone and union-preserving; unwrap is monotone (its full
% homomorphism property is `unwrap_hom.p`); composition's monotonicity is
% `mono_compose.p`, split out because adding it here pushed this file from 6.6 s
% to a 90 s timeout — a five-conjunct goal is a five-way disjunction after
% negation and saturation has to refute all of it at once.
%
% GENERALISES: the Composition/Wrap/Unwrap arms of SpatialTypes.infer
%
% VERDICT: PROVED by vampire in 6.6s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').

tff(mono_concat, conjecture,
    ! [A: space, B: space, W: path] :
      ( ( sub(A,B) => sub(wrap(A,W), wrap(B,W)) )
      & wrap(cup(A,B),W) = cup(wrap(A,W), wrap(B,W))
      & wrap(empty,W) = empty
      & ( sub(A,B) => sub(unwrap(A,W), unwrap(B,W)) ) ) ).
