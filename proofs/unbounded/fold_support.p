% ===========================================================================
% TIER 3 / fold.  THE SUPPORT BOUND.  Every path of a fold comes from the body
% applied at SOME present head, to that head's group — whatever the accumulator
% reached there was, and whatever order the walk used.
%
% This is the statement tier-1's Fold arm needs and cannot make: `Lower.sizeBounds`
% widens a Fold to [0, inf) because it has no way to say "the result is covered by
% the per-group images".  It is also the soundness condition for the spatial
% analysis's Fold transfer, which joins the per-group body shapes.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_tails_ops.p').
include('_fold_ops.p').
tff(fold_support, conjecture,
    ! [P: path, A: space, F: bodyA, U: updA, I: path] :
      ( mem(P, fold(A,F,U,I))
     => ? [H: item, Acc: path] :
          ( headed(H,A) & mem(P, ap3(F, Acc, H, grp(H,A))) ) ) ).
