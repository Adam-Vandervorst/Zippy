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
% THIS FILE: THE MEET BOUNDS `|A n B| =< |A|` and `|A n B| =< |B|` — the
% schematic form of tier-1's `hi = min(hi_a, hi_b)` for Intersection.  They follow
% from `card_mono` alone, with no additivity: this is the cheapest theorem in the
% cardinality family and it is stated separately so that the expensive ones cannot
% hide behind it.
%
% VERDICT: PROVED by vampire in 0.0s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_lattice_lemmas.p').
include('_nat.p').
include('_card.p').

tff(card_meet, conjecture,
    ! [A: space, B: space] :
      ( le(card(cap(A,B)), card(A))
      & le(card(cap(A,B)), card(B)) ) ).
