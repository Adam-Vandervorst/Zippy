% ===========================================================================
% TIER 3 / intersection.
%
% `n` is a commutative idempotent monoid annihilated by `empty`, and it is the
% MEET of the inclusion order.  The `empty` arm is the one docs/traps.md 1 warns
% about ("never let an empty operand vanish from a meet") — here it is a theorem
% rather than a convention.
%
% GENERALISES: tier-1 Lower.sizeBounds Intersection arm; the trie meet fast
% paths in AlgebraicResult
%
% VERDICT: PROVED by vampire in 0.1s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').

tff(lattice_inter, conjecture,
    ! [A: space, B: space, C: space] :
      ( cap(A,A) = A
      & cap(A,B) = cap(B,A)
      & cap(cap(A,B),C) = cap(A,cap(B,C))
      & cap(A, empty) = empty
      & sub(cap(A,B), A)
      & ( ( sub(C,A) & sub(C,B) ) => sub(C, cap(A,B)) ) ) ).
