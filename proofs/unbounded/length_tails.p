% ===========================================================================
% TIER 3 / tails-union / unwrap.
%
% LENGTHS DECREASE BY EXACTLY ONE UNDER TAILS-UNION and by exactly |p| under
% unwrap.  `_nat.p` has no subtraction — deliberately, since the naturals do not
% have one — so the rules are stated in ADDITIVE form: a bound of `N + 1` on the
% source gives a bound of `N` on the tails.  That is equivalent to tier-1's
% `lo - 1` and it explains tier-1's clamp at 0: the additive form simply has
% nothing to clamp.  The last conjunct is the exact fact behind all of them —
% every path in a tails-union is one item shorter than some path of the source.
%
% GENERALISES: tier-1 Lower.lenBounds TailsUnion/Unwrap arms (`lo - 1` / `lo
% - |p|`, clamped at 0)
%
% VERDICT: PROVED by vampire in 0.1s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_tails_ops.p').
include('_concat_ops.p').
include('_nat.p').
include('_plen.p').
include('_lenbounds.p').

tff(length_tails, conjecture,
    ! [A: space, W: path, N: num] :
      ( ( lenUB(A, plus(N,one)) => lenUB(tu(A), N) )
      & ( lenLB(A, plus(N,one)) => lenLB(tu(A), N) )
      & ( lenUB(A, plus(plen(W),N)) => lenUB(unwrap(A,W), N) )
      & ( lenLB(A, plus(plen(W),N)) => lenLB(unwrap(A,W), N) )
      & ( ! [P: path] : ( mem(P, tu(A)) => ? [Q: path] : ( mem(Q,A) & plen(Q) = plus(plen(P), one) ) ) ) ) ).
