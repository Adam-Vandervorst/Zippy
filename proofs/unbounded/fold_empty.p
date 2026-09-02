% ===========================================================================
% TIER 3 / fold.  THE CORNERS.  A fold over a source with no heads is empty —
% both for the empty source and for `{eps}`, which HAS a member but no head.
% `{eps}` is the case `proofs/laws/law_iterc_set.smt2` caught as a false
% unguarded rule for `IterC`; the same trap applies to `Fold` and is closed
% here rather than left to be rediscovered.
% GENERALISES: tier-1 `Lower.sizeBounds`'s Fold arm (lo = 0) and eval's
% `groups.isEmpty` short-circuit.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_tails_ops.p').
include('_fold_ops.p').
tff(fold_empty, conjecture,
    ! [F: bodyA, U: updA, I: path] :
      ( fold(empty,F,U,I) = empty
      & fold(sing(nil),F,U,I) = empty ) ).
