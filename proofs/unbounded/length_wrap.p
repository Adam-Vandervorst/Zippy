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
% THIS FILE: WRAP ONLY.  The first conjunct is the EXACT statement — every path
% of `wrap(A,W)` comes from a path of A with exactly `|W|` more items — which is
% strictly stronger than the interval rules that follow from it and is where
% additivity of `plen` over `app` is used.
%
% VERDICT: PROVED by vampire in 0.9s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').
include('_nat.p').
include('_plen.p').
include('_lenbounds.p').

tff(length_wrap, conjecture,
    ! [A: space, W: path, N: num] :
      ( ( ! [P: path] : ( mem(P, wrap(A,W))
            => ? [Q: path] : ( mem(Q,A) & plen(P) = plus(plen(W), plen(Q)) ) ) )
      & ( lenLB(A,N) => lenLB(wrap(A,W), plus(plen(W), N)) )
      & ( lenUB(A,N) => lenUB(wrap(A,W), plus(plen(W), N)) ) ) ).
