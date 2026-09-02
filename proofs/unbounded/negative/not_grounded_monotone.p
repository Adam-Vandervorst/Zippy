% ===========================================================================
% NEGATIVE CONTROL / grounded.  `sub(S1,S2) => sub(gss(F,S1), gss(F,S2))` —
% FALSE.  `f` is an arbitrary Scala function; nothing forces it to be monotone,
% and a grounded node that complements or counts its argument is not.
%
% THIS IS THE CONTROL BEHIND A REAL GATE.  Without monotonicity the
% least-post-fixpoint reading of an enclosing `Space.Fixpoint` is not available
% at all (terminating/fixpoint_is_lfp.smt2, O1), which is why
% `AgnosticPipeline.monotoneInMention` returns false for a recursion variable
% under a grounded node and why `MORKL.mono`/`monoIn` forbid an SCC call there.
% If this were provable those three gates would be needlessly conservative AND
% the encoding would be proving something about an opaque function.
%
% Expected: NOT-PROVED.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_grounded_ops.p').
tff(not_grounded_monotone, conjecture,
    ! [F: gfun, S1: space, S2: space] :
      ( sub(S1,S2) => sub(gss(F,S1), gss(F,S2)) ) ).
