% ===========================================================================
% TIER 3 / range.  THE WINDOW IS INSIDE ITS SOURCE, AND A FULL WINDOW IS THE
% IDENTITY.
%
%   sub(rng(A,Lo,Hi), A)                      the containment tier-1 uses
%   (ForAll P in A. ~plt(P,Lo) & plt(P,Hi))  =>  rng(A,Lo,Hi) = A
%
% GENERALISES: tier-1 `Lower.sizeBounds`'s Range arm (lo = 0, hi = hi_src) and
% `IntTrie.range`'s O(1) full-window fast path, which returns the operand BY
% POINTER and is priced as one node visit by the cost model — an identity that
% has to hold for that to be sound.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_range_ops.p').
tff(range_window, conjecture,
    ! [A: space, Lo: path, Hi: path] :
      ( sub(rng(A,Lo,Hi), A)
      & ( ( ! [P: path] : ( mem(P,A) => ( ~ plt(P,Lo) & plt(P,Hi) ) ) )
          => rng(A,Lo,Hi) = A )
      & ( ! [Lo2: path, Hi2: path] : rng(empty,Lo2,Hi2) = empty ) ) ).
