% ===========================================================================
% TIER 3 / restriction.
%
% Restriction(x,y) = { p in x : SOME PREFIX of p is in y }.  It is a FILTER
% (hence inside its first argument and idempotent), it is annihilated by an empty
% prefix set, it is the identity when the prefix set contains the empty path, and
% it distributes over union in BOTH arguments.  The `restr(X, sing(nil)) = X`
% conjunct is the epsilon corner docs/traps.md 1 insists on enumerating: `{eps}`
% is not `{}`, and a prefix set containing eps restricts nothing away.
%
% GENERALISES: tier-1 Lower.sizeBounds Restriction arm (`lo = 0`, `hi =
% hi_x`) and keys_restriction.smt2
%
% VERDICT: PROVED by vampire in 0.3s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_prefix.p').
include('_prefix_ops.p').

tff(restriction, conjecture,
    ! [X: space, Y: space, Z: space] :
      ( sub(restr(X,Y), X)
      & restr(restr(X,Y),Y) = restr(X,Y)
      & restr(X, empty) = empty
      & restr(X, sing(nil)) = X
      & restr(cup(X,Z), Y) = cup(restr(X,Y), restr(Z,Y))
      & restr(X, cup(Y,Z)) = cup(restr(X,Y), restr(X,Z)) ) ).
