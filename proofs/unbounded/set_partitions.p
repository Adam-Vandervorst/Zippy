% ===========================================================================
% TIER 3 / union / intersection / subtraction.
%
% THE TWO DISJOINT DECOMPOSITIONS every counting argument runs on:
%
%   A u B  =  A  +  (B \ A)          disjointly
%   B      =  (A n B)  +  (B \ A)    disjointly
%
% Purely set-theoretic — no cardinality anywhere — which is the point: the
% counting theorems (`card_subadd.p`, `card_incl_excl.p`) get their partitions
% from HERE, so `_card.p`'s additivity axiom is applied to decompositions that
% were proved rather than asserted.  Subtracting the overlap once on each side
% is what makes inclusion-exclusion come out; asserting the partition instead
% would make that theorem circular.
%
% GENERALISES: the "saturated subset relation" SizeConstraints.encode computes
% over the finite node set of one term — the same decompositions, but only for
% the subterms that happen to occur.
%
% VERDICT: PROVED by vampire in 0.0s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').

tff(set_partitions, conjecture,
    ! [A: space, B: space] :
      ( cup(A, sdiff(B,A)) = cup(A,B)
      & disj(A, sdiff(B,A))
      & cup(cap(A,B), sdiff(B,A)) = B
      & disj(cap(A,B), sdiff(B,A)) ) ).
