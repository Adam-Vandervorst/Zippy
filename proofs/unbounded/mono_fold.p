% ===========================================================================
% TIER 3 / fold.  MONOTONICITY IN THE BODY, and the exact sense in which a fold
% is monotone at all: a body that is monotone in the tails it is handed gives a
% fold whose per-group images grow with the groups.  There is NO claim of
% monotonicity in the SOURCE — enlarging the source adds head groups AND changes
% the accumulator every later group sees, which is why
% `AgnosticPipeline.monotoneInMention` treats `Fold` as unknown variance and why
% `MORKL.mono` forbids an SCC call under one.
% GENERALISES: the Fold arm of `SpatialTypes.infer`, which joins per-group body
% shapes and therefore needs exactly this.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_tails_ops.p').
include('_fold_ops.p').
tff(mono_fold, conjecture,
    ! [A: space, F: bodyA, U: updA, I: path, H: item, S1: space, S2: space] :
      ( ( monoA(F) & sub(S1,S2) )
     => sub(ap3(F, facc(A,U,I,H), H, S1), ap3(F, facc(A,U,I,H), H, S2)) ) ).
