% =============================================================================
% TIER 3 add-on: CARDINALITY.  The counting axioms, stated explicitly.
%
% COUNTING IS NOT EXPRESSIBLE IN PURE FIRST-ORDER LOGIC.  `card(A)` is "the
% number of paths in A", and there is no first-order sentence over the
% signature of `_signature.p` that pins that number down: finiteness itself is
% not first-order.  The honest move — and the one `terminating/*.p` already
% takes for the datalog termination measures (`card_type` /`card_nonneg` /
% `card_strict_decrease` in terminating/bounded_growth_decrease.p,
% terminating/datalog_a_terminates.p) — is to leave `card` UNINTERPRETED and
% write down, as axioms, exactly the counting facts we rely on.  This file is
% that list, and it is deliberately short.
%
% ASSUMED (4 axioms; non-negativity comes free from `_nat.p`'s `zero_le`):
%   card_empty      |{}| = zero
%   card_sing       |{p}| = one
%   card_mono       A subset B  =>  |A| =< |B|
%   card_disj_add   A, B disjoint  =>  |A u B| = |A| + |B|
%
% ASSUMED, but of a different character (1 axiom + 1 comprehension):
%   card_image      an INJECTIVE image has the same cardinality.  This is the
%                   one counting principle that is not about the inclusion
%                   lattice, and it is unavoidable: |Wrap p A| = |A| holds
%                   because q |-> p++q is injective, and no amount of
%                   monotonicity/additivity implies that.  FOL cannot quantify
%                   over functions, so path maps are REIFIED into the sort
%                   `pmap` (declared below) with `apm` as application;
%                   `pfxmap` is the comprehension axiom asserting
%                   that the particular map q |-> W++q exists as an object of
%                   that sort.  Note this does NOT hand us |Wrap p A| = |A|:
%                   `card_wrap.p` still has to prove that `pfxmap(W)` is
%                   injective on A (which needs `_cancel.p`) and that
%                   `wrap(A,W)` is its image (which needs `wrap_def`).
%
% DERIVED, NOT ASSUMED — these are conjectures elsewhere in the corpus, so the
% axiom list above cannot be accused of containing its own conclusions:
%   |A u B| =< |A| + |B|            subadditivity        (card_subadd.p)
%   |A n B| =< |A| and =< |B|                            (card_meet.p)
%   |A| =< |A \ B| + |B|            (the inverse-free form of |A\B| >= |A|-|B|,
%                                    which is what an ordered monoid without
%                                    subtraction can state)   (card_subadd.p)
%   |A u B| + |A n B| = |A| + |B|   inclusion-exclusion  (card_incl_excl.p)
%   |A| = |restr(A,B)| + |raff(A,B)|                     (card_partition.p)
%   |wrap(A,W)| = |A|                                    (card_wrap.p)
%
% NOT ASSUMED AND NOT DERIVABLE (recorded so the gap is visible rather than
% implied): nothing here forces `card` to be the cardinality of a FINITE set.
% A model in which every infinite space is given the same "size" satisfies all
% of these axioms.  Every theorem below is therefore a fact about ANY measure with
% these properties — which is exactly the class of facts tier-1
% (`Lower.sizeBounds`) and tier-2 (`SizeZ3`) implement, so the generalisation
% is faithful.  Strict decrease under proper inclusion — the extra axiom the
% termination corpus needs — is deliberately NOT here: no operator law uses it.
% =============================================================================

% INCLUDE AFTER `_signature.p` AND `_nat.p`.  `card` lands in the uninterpreted
% ordered commutative monoid `num`, not in `$int`: see `_nat.p` for the measured
% reason (vampire 5.1.0 refutes `_signature.p + _card.p` outright when `card` is
% `$int`-valued, using only its own internally introduced theory axioms, and an
% inconsistent axiom set proves every conjecture).  `card_nonneg` is `le(zero,
% card(A))`, which `_nat.p`'s `zero_le` already gives for every element of
% `num`, so it is not repeated here.

tff(card_type, type, card: space > num ).

tff(card_empty,   axiom, card(empty) = zero ).
tff(card_sing,    axiom, ! [P: path] : card(sing(P)) = one ).
tff(card_mono,    axiom,
    ! [A: space, B: space] : ( sub(A,B) => le(card(A), card(B)) ) ).
tff(card_disj_add, axiom,
    ! [A: space, B: space] :
      ( disj(A,B) => card(cup(A,B)) = plus(card(A), card(B)) ) ).
