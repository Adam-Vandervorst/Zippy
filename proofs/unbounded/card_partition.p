% ===========================================================================
% TIER 3 / restriction / raffination.
%
% |X| = |restr(X,Y)| + |raff(X,Y)|.  The counting consequence of the
% restriction/raffination partition proved in `raffination.p`: the two halves are
% disjoint and cover X, so their sizes add EXACTLY.  This is a stronger statement
% than anything tier-1 can express — `Lower.sizeBounds` gives each of the two
% operators the interval [0, hi_x] independently, and has no way to say that the
% two intervals are complementary.
%
% GENERALISES: the cost model's assumption that a restriction and its
% raffination together cost one traversal of the source
%
% VERDICT: PROVED by vampire in 2.7s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_lattice_lemmas.p').
include('_paths.p').
include('_prefix.p').
include('_prefix_ops.p').
include('_nat.p').
include('_card.p').

tff(card_partition, conjecture,
    ! [X: space, Y: space] :
      ( card(X) = plus(card(restr(X,Y)), card(raff(X,Y))) ) ).
