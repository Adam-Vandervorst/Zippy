% ===========================================================================
% TIER 3 / union / intersection.
%
% The inclusion lattice is DISTRIBUTIVE, both ways, and the two absorption
% laws hold.  This is what licenses a trie intersection to be pushed into a union
% of subtries (docs/guide.md's disjoint-prefix / pointer-equality shortcuts are
% only sound because the algebra distributes).
%
% GENERALISES: the push-intersection-through-union rewrite the trie backends
% rely on
%
% VERDICT: PROVED by vampire in 0.2s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').

tff(lattice_distrib, conjecture,
    ! [A: space, B: space, C: space] :
      ( cup(A, cap(A,B)) = A
      & cap(A, cup(A,B)) = A
      & cap(A, cup(B,C)) = cup(cap(A,B), cap(A,C))
      & cup(A, cap(B,C)) = cap(cup(A,B), cup(A,C)) ) ).
