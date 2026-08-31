% ===========================================================================
% TIER 3 / inclusion.
%
% `sub` is a PARTIAL order with `empty` as bottom, and it agrees with both
% algebraic characterisations.  Antisymmetry is the one place extensionality is
% load-bearing: without it two spaces with the same members need not be equal, and
% every equational theorem in this corpus would be unprovable.
% Tier-2's `SizeZ3.encode` computes a saturated `sub` relation over the FINITE set
% of nodes of one term; this is the same relation over all spaces.
%
% GENERALISES: the subset relation SizeConstraints.scala saturates (`sub` in
% `encode`) — there per node, here for all spaces
%
% VERDICT: PROVED by vampire in 0.0s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').

tff(lattice_order, conjecture,
    ! [A: space, B: space, C: space] :
      ( sub(A,A)
      & ( ( sub(A,B) & sub(B,C) ) => sub(A,C) )
      & ( ( sub(A,B) & sub(B,A) ) => A = B )
      & sub(empty, A)
      & ( sub(A,B) <=> cup(A,B) = B )
      & ( sub(A,B) <=> cap(A,B) = A ) ) ).
