% ===========================================================================
% NEGATIVE CONTROL / fold.  `fold(A,F,U,I) = iter(A, F-at-I)` UNCONDITIONALLY —
% FALSE.  It holds only when the update never moves the accumulator
% (`constU(U)`), which is what `fold_iter_const.p` proves.
%
% THIS IS THE NEAR-MISS THAT SHIPPED: `src/test/scala/UnboundedTier.scala`'s
% `operators` function mapped a `Fold` node to the string "iteration", so the
% printed cornerstone coverage table reported the iteration laws as covering
% folds.  A fold body sees an accumulator that depends on every earlier group,
% so the groups are interdependent and the group ORDER is observable; an
% iteration body sees only `(head, tails)`.
%
% Expected: NOT-PROVED.
% ===========================================================================
include('../_signature.p').
include('../_paths.p').
include('../_tails_ops.p').
include('../_iter_ops.p').
include('../_fold_ops.p').
tff(atacc_type, type, atAcc: ( bodyA * path ) > bodyF ).
tff(atacc_def, axiom,
    ! [F: bodyA, I: path, H: item, S: space] :
      ap2(atAcc(F,I), H, S) = ap3(F, I, H, S) ).
tff(not_fold_eq_iter, conjecture,
    ! [A: space, F: bodyA, U: updA, I: path] :
      fold(A,F,U,I) = iter(A, atAcc(F,I)) ).
