% ===========================================================================
% TIER 3 / restriction / raffination.
%
% MONOTONICITY of the two prefix operators.  Restriction is monotone in both
% arguments; raffination is monotone in its first and ANTITONE in its second —
% enlarging the prefix set removes more.  Getting this variance backwards is a
% silent wrong answer, and neither tier-1 nor tier-2 can state it.
%
% GENERALISES: the `Restriction`/`Raffination` arms of SpatialTypes.infer,
% which widen rather than reason about variance
%
% VERDICT: PROVED by vampire in 0.9s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_prefix.p').
include('_prefix_ops.p').

tff(mono_prefix, conjecture,
    ! [X: space, Y: space, Z: space, W: space] :
      ( ( ( sub(X,Z) & sub(Y,W) ) => sub(restr(X,Y), restr(Z,W)) )
      & ( sub(X,Z) => sub(raff(X,Y), cup(raff(Z,Y), restr(Z,Y))) )
      & ( sub(W,Y) => sub(raff(X,Y), raff(X,W)) ) ) ).
