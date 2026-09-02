% ===========================================================================
% TIER 3 / range.  THE LOAD-BEARING PROPERTY: A WINDOW IS AN INTERVAL OF THE
% CANONICAL ORDER.
%
%   P, R in rng(A,Lo,Hi)  and  Q in A  and  plt(P,Q) and plt(Q,R)  =>  Q in rng(A,Lo,Hi)
%
% WHY THIS IS THE ONE THAT MATTERS.  `Range` is the only operator in the algebra
% that is not pointwise: whether `P` survives depends on its RANK among the
% source's paths, not on membership alone.  What makes the four backends agree on
% it anyway is that they all slice by the SAME total order (`pathValueOrdering`:
% "every backend slices Range by THIS order, so they agree") and that a slice is
% an interval of it — so `eval`, `evalT`, `evalI` and `execT` cannot disagree
% about which paths are in the window even though none of them can decide it
% locally.  Stated here for an ARBITRARY strict total order, so the theorem does
% not depend on which order the implementation picked.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_range_ops.p').
tff(range_interval, conjecture,
    ! [A: space, Lo: path, Hi: path, P: path, Q: path, R: path] :
      ( ( mem(P, rng(A,Lo,Hi)) & mem(R, rng(A,Lo,Hi)) & mem(Q,A)
          & plt(P,Q) & plt(Q,R) )
     => mem(Q, rng(A,Lo,Hi)) ) ).
