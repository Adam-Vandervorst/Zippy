% ===========================================================================
% TIER 3 / call.  UNFOLDING AN ACYCLIC CALL IS MEANING-PRESERVING, and equal
% arguments give equal results.
%
%   call(R,S) = ap1(rbody(R), S)        and       S1 = S2 => call(R,S1) = call(R,S2)
%
% GENERALISES: `eval`'s Call rule and the licence `Lower.inline` needs to splice
% a non-recursive routine body in place of the call.
%
% WHAT THIS IS NOT.  It is NOT the capture-avoiding-substitution theorem (O6a in
% terminating/REGISTRY.tsv, OPEN).  Here a body IS its semantic function, so
% "substitute then evaluate = evaluate then apply" is congruence; the open
% obligation is that `substMention`/`substPathRef`/`Lower.inline` COMPUTE that
% function under `Iteration`/`Fold`/`Fixpoint` binders.  See `_call_ops.p`'s
% header and `src/test/scala/SubstConformance.scala`.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_fix_ops.p').
include('_call_ops.p').
tff(call_unfold, conjecture,
    ! [R: routine, S: space, S2: space] :
      ( call(R,S) = ap1(rbody(R), S)
      & ( S = S2 => call(R,S) = call(R,S2) ) ) ).
