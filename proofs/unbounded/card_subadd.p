% ===========================================================================
% TIER 3 / union / intersection / subtraction.
%
% THE CARDINALITY BOUNDS TIER-1 AND TIER-2 IMPLEMENT, stated once for all
% spaces.  `Lower.sizeBounds` computes `hi_a + hi_b` for a union and
% `min(hi_a,hi_b)` for an intersection; `SizeZ3.encode` emits the same as ground
% linear constraints over `n<i>`.  Here they are proved from the five counting
% axioms of `_card.p` — NONE of which is one of these four facts, so this is a
% derivation and not a restatement:
%   |A u B| =< |A| + |B|        subadditivity
%   |A n B| =< |A|, |A n B| =< |B|
%   |A \ B| >= |A| - |B|
%   |A u B| + |A n B| = |A| + |B|   inclusion-exclusion
% The last needs the partition A u B = A + (B \ A) and B = (A n B) + (B \ A),
% each supplied by `card_disj_add`.
%
% GENERALISES: tier-1 Lower.sizeBounds Union/Intersection/Subtraction arms
% and the linear constraints SizeConstraints.encode emits per node
%
% THIS FILE: SUBADDITIVITY and the inverse-free difference bound.  Split from
% the meet bounds and inclusion-exclusion because the five-conjunct goal did not
% close in 60 s while each group does.  Both conjuncts go through the SAME
% partition — `A u B = A + (B \ A)` with the two halves disjoint — which is the
% only place `card_disj_add` is used.
%
% VERDICT: PROVED by vampire in 0.6s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_lattice_lemmas.p').
include('_partitions.p').
include('_nat.p').
include('_card.p').

tff(card_subadd, conjecture,
    ! [A: space, B: space] :
      ( le(card(cup(A,B)), plus(card(A), card(B)))
      & le(card(A), plus(card(sdiff(A,B)), card(B))) ) ).
