% ===========================================================================
% TIER 3 / fixpoint.
%
% THE PARK CHARACTERISATION MAKES THE FIXPOINT UNIQUE AND MONOTONE.  Three
% facts, none of which is one of the three defining axioms:
%   * UNIQUENESS: any X that is a pre-fixpoint above `init` and below every other
%     such X IS `fix(init,G)`.  This is the space-algebra instance of
%     terminating/least_fixpoint_unique.p, which proves the same thing for an
%     abstract join-semilattice with an uninterpreted `f`;
%   * MONOTONICITY in the initial value — and note it needs NO monotonicity of the
%     body, which is worth knowing because `SpatialCost.fixRounds` decides body
%     monotonicity only syntactically;
%   * IDEMPOTENCE: re-seeding the fixpoint with its own value changes nothing.
%
% GENERALISES: terminating/least_fixpoint_unique.p (the same uniqueness fact
% in an ABSTRACT join-semilattice; here it is over the actual space algebra
% with the actual `fix`)
%
% VERDICT: PROVED by vampire in 0.1s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_fix_ops.p').

tff(fixpoint, conjecture,
    ! [I: space, J: space, X: space, G: bodyG] :
      ( ( ( sub(I,X) & sub(ap1(G,X),X)
          & ! [Y: space] : ( ( sub(I,Y) & sub(ap1(G,Y),Y) ) => sub(X,Y) ) )
        => X = fix(I,G) )
      & ( sub(I,J) => sub(fix(I,G), fix(J,G)) )
      & fix(fix(I,G), G) = fix(I,G) ) ).
