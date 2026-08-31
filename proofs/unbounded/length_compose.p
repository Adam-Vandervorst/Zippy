% ===========================================================================
% TIER 3 / composition / wrap.
%
% LENGTHS ADD UNDER CONCATENATION.  `len(comp A B)` is bounded below and
% above by the sums of the operand bounds, and `len(wrap p A) = |p| + len A`
% EXACTLY — the third conjunct states the exact form (every path of the wrap comes
% from a path of A with exactly |p| more items), which is strictly stronger than
% the interval version tier-1 computes and is where the additivity of `plen` over
% `app` is used.
%
% GENERALISES: tier-1 Lower.lenBounds Composition/Wrap arms (`lo = lo_a +
% lo_b`, `hi = hi_a + hi_b`; wrap adds |p|)
%
% THIS FILE: COMPOSITION ONLY.  Lengths ADD: a lower bound M on the left factor
% and N on the right give a lower bound M+N on the product, and likewise for upper
% bounds.  Split from the wrap rules because the five-conjunct goal did not close
% in 60 s.
%
% VERDICT: PROVED by vampire in 39.3s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').
include('_nat.p').
include('_plen.p').
include('_lenbounds.p').

tff(length_compose, conjecture,
    ! [A: space, B: space, M: num, N: num] :
      ( ( ( lenLB(A,M) & lenLB(B,N) ) => lenLB(comp(A,B), plus(M,N)) )
      & ( ( lenUB(A,M) & lenUB(B,N) ) => lenUB(comp(A,B), plus(M,N)) ) ) ).
