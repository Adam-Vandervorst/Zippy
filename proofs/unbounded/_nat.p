% =============================================================================
% TIER 3 module: SIZES AND LENGTHS AS AN ORDERED COMMUTATIVE MONOID.
% Include after `_signature.p`.  Declares the sort `num` used by `_card.p`
% (cardinality) and `_plen.p` (path length).
%
% WHY NOT `$int`.  Because vampire 5.1.0's built-in integer theory is UNSOUND on
% this corpus.  MEASURED, three times, reproducibly:
%
%   probe A = _signature.p + _card.p with `card : space > $int`,
%            conjecture `$false` (i.e. the axiom set alone)
%   probe B = _signature.p + _paths.p + _plen.p with `plen : path > $int`, ditto
%
%   $ vampire --mode casc -t 60s probeA.p   =>  % SZS status ContradictoryAxioms
%   $ vampire --mode casc -t 60s probeB.p   =>  % SZS status ContradictoryAxioms
%
% Both axiom sets are plainly CONSISTENT — take `space` to be the finite subsets
% of a countable set of paths, `card` its cardinality, `plen` the word length;
% every axiom holds.  The refutations use only vampire's INTERNALLY INTRODUCED
% theory axioms (`tha_right_identity`, `tha_order_monotonicity`,
% `tha_non-reflexivity`, ...), and the last step of the printed derivation is an
% `equality_resolution` turning `$sum(X0,X1) != X1 | 2 != X0` into `2 != X0`,
% which does not follow.  Running the same file with `-tha off` produces a plain
% timeout instead, which confirms where the unsoundness lives.
%
% An inconsistent axiom set proves EVERY conjecture, so a "PROVED" verdict from
% such a file is worth nothing (docs/traps.md 3: a semantics-critical path must
% never silently degrade).  Rather than ship verdicts we cannot trust, the whole
% corpus is arithmetic-FREE: sizes and lengths live in an uninterpreted sort
% `num` with exactly the eight axioms below, all of which are true of the
% naturals, and `run.sh` additionally runs a VACUITY PROBE per file (the same
% axioms with the conjecture `$false`) so that any future axiom set that admits
% a refutation is caught rather than reported as a proof.
%
% WHAT IS ASSUMED: `(num, plus, zero)` is a commutative monoid, `le` is a
% partial order with `zero` least, and the two are compatible in BOTH directions
% (`le_plus` is an iff, which is what makes "one item shorter" reasoning work
% without a subtraction operator).  Nothing else — no totality, no cancellation,
% no induction, no finiteness.  Every theorem in the corpus therefore holds of
% ANY such measure, which is exactly the class tier-1's intervals and tier-2's
% linear constraints implement.
%
% `one` carries no axiom of its own: it is simply the increment `plen` uses per
% path item.  Statements that would need subtraction are written in ADDITIVE
% form instead (`lenUB(A, plus(M,one)) => lenUB(tu(A), M)` rather than `N - 1`),
% which is equivalent given `le_plus` and needs no inverse.
% =============================================================================

tff(num_type,  type, num:  $tType ).
tff(zero_type, type, zero: num ).
tff(one_type,  type, one:  num ).
tff(plus_type, type, plus: ( num * num ) > num ).
tff(le_type,   type, le:   ( num * num ) > $o ).

tff(plus_comm,  axiom, ! [A: num, B: num] : plus(A,B) = plus(B,A) ).
tff(plus_assoc, axiom, ! [A: num, B: num, C: num] : plus(plus(A,B),C) = plus(A,plus(B,C)) ).
tff(plus_zero,  axiom, ! [A: num] : plus(A,zero) = A ).

tff(le_refl,    axiom, ! [A: num] : le(A,A) ).
tff(le_trans,   axiom, ! [A: num, B: num, C: num] : ( ( le(A,B) & le(B,C) ) => le(A,C) ) ).
tff(le_antisym, axiom, ! [A: num, B: num] : ( ( le(A,B) & le(B,A) ) => A = B ) ).
tff(zero_le,    axiom, ! [A: num] : le(zero, A) ).
tff(le_plus,    axiom,
    ! [A: num, B: num, C: num] : ( le(plus(A,C), plus(B,C)) <=> le(A,B) ) ).
