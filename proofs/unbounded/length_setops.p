% ===========================================================================
% TIER 3 / union / intersection / subtraction.
%
% THE LENGTH TRANSFER RULES OF TIER-1, SCHEMATICALLY.  `Lower.lenBounds`
% propagates a [lo,hi] length interval per node; `LenZ3` re-encodes the same
% per-node intervals as ground integer constants.  The rules themselves — a union
% keeps a bound both sides satisfy, a meet and a difference inherit either side's
% bound, a subspace inherits its superspace's bounds — are stated here once, for
% all spaces and ALL n, which is what makes them checkable at all.
%
% GENERALISES: tier-1 Lower.lenBounds Union/Intersection/Subtraction arms
% and tier-2 LenZ3
%
% VERDICT: PROVED by vampire in 0.0s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_nat.p').
include('_plen.p').
include('_lenbounds.p').

tff(length_setops, conjecture,
    ! [A: space, B: space, N: num] :
      ( ( ( lenLB(A,N) & lenLB(B,N) ) => lenLB(cup(A,B), N) )
      & ( ( lenUB(A,N) & lenUB(B,N) ) => lenUB(cup(A,B), N) )
      & ( lenLB(A,N) => lenLB(cap(A,B), N) )
      & ( lenUB(A,N) => lenUB(cap(A,B), N) )
      & ( lenLB(A,N) => lenLB(sdiff(A,B), N) )
      & ( ( sub(A,B) & lenUB(B,N) ) => lenUB(A,N) ) ) ).
