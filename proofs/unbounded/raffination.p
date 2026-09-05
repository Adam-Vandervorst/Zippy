% ===========================================================================
% TIER 3 / raffination.
%
% THE RESTRICTION / RAFFINATION PARTITION.  `raff` is defined as
% `x \ restr(x,y)`, so what has to be proved is that restriction and raffination
% PARTITION their first argument: their union is x and they are disjoint.  This is
% the schematic form of the fact the cost model uses when it prices a
% restriction/raffination pair as one traversal of x.  The two degenerate corners
% are included on purpose (docs/traps.md 1): raffinating by `{eps}` removes
% everything, raffinating by `{}` removes nothing.
%
% GENERALISES: the Raffination arm of `eval` and of tier-1 Lower.sizeBounds;
% proofs/restriction.smt2 (instance tier)
%
% VERDICT: PROVED by vampire in 0.3s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_prefix.p').
include('_prefix_ops.p').

tff(raffination, conjecture,
    ! [X: space, Y: space] :
      ( cup(restr(X,Y), raff(X,Y)) = X
      & disj(restr(X,Y), raff(X,Y))
      & sub(raff(X,Y), X)
      & raff(X, sing(nil)) = empty
      & raff(X, empty) = X
      & raff(raff(X,Y),Y) = raff(X,Y) ) ).
