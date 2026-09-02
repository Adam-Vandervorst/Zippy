% ===========================================================================
% TIER 3 / fold + iteration.  THE ONE CONDITION UNDER WHICH A FOLD IS AN
% ITERATION: an update that never moves the accumulator.
%
%   constU(U)  =>  fold(A, F, U, I) = iter(A, F-at-I)
%
% WHY THIS FILE EXISTS.  `src/test/scala/UnboundedTier.scala` keyed a `Fold`
% node to the string "iteration", so the coverage table reported the iteration
% laws as covering folds.  UNCONDITIONALLY that is false — the accumulator makes
% the groups interdependent and the group ORDER observable — and
% `negative/not_fold_eq_iter.p` is the machine-checked witness that it is false.
% This file certifies the hypothesis under which the identification IS sound, so
% the alias becomes a law with a premise instead of a mapping-table entry.
%
% The `F-at-I` iteration body is the reified `bodyF` whose `ap2(-,H,S)` is
% `ap3(F,I,H,S)`; `atAcc` names it and `atacc_def` is its defining equation.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_tails_ops.p').
include('_iter_ops.p').
include('_fold_ops.p').
tff(atacc_type, type, atAcc: ( bodyA * path ) > bodyF ).
tff(atacc_def, axiom,
    ! [F: bodyA, I: path, H: item, S: space] :
      ap2(atAcc(F,I), H, S) = ap3(F, I, H, S) ).
tff(fold_iter_const, conjecture,
    ! [A: space, F: bodyA, U: updA, I: path] :
      ( constU(U) => fold(A,F,U,I) = iter(A, atAcc(F,I)) ) ).
