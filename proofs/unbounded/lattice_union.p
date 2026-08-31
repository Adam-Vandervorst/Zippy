% ===========================================================================
% TIER 3 / union.
%
% `u` is a commutative idempotent monoid with `empty` as unit, and it is the
% JOIN of the inclusion order.  Every union rewrite in `SC.reduce` and every
% `Union` arm of `Lower.sizeBounds` presupposes this and none of them states it:
% tier-1 has no quantifiers, and tier-2's `(declare-const n<i> Int)` per node
% cannot mention "all spaces" at all.
%
% GENERALISES: tier-1 Lower.sizeBounds Union arm; SC.reduce union
% normalisation; formal.egg union laws
%
% VERDICT: PROVED by vampire in 0.2s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').

tff(lattice_union, conjecture,
    ! [A: space, B: space, C: space] :
      ( cup(A,A) = A
      & cup(A,B) = cup(B,A)
      & cup(cup(A,B),C) = cup(A,cup(B,C))
      & cup(A, empty) = A
      & sub(A, cup(A,B))
      & ( ( sub(A,C) & sub(B,C) ) => sub(cup(A,B), C) ) ) ).
