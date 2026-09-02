% ===========================================================================
% NEGATIVE CONTROL / range.  `sub(A,B) => sub(rng(A,Lo,Hi), rng(B,Lo,Hi))` —
% FALSE for a POSITIONAL window.
%
% A window is not pointwise: whether a path survives depends on its RANK among
% the source's paths.  Adding a path to the source shifts every later rank, so a
% BIGGER source can give a SMALLER window.  (In the order-interval encoding of
% `_range_ops.p` the endpoints are paths rather than ranks, so this particular
% rendering is only UNPROVABLE rather than refutable — see the file's header;
% what the control pins is that the corpus does not derive monotonicity, which
% is what `AgnosticPipeline.monotoneInMention` and `MORKL.mono`/`monoIn` rely on
% when they refuse a recursion variable under a `Range`.)
%
% Expected: NOT-PROVED.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_range_ops.p').
tff(not_range_monotone, conjecture,
    ! [A: space, B: space, Lo: path, Hi: path] :
      ( sub(A,B) => sub(rng(A,Lo,Hi), rng(B,Lo,Hi)) ) ).
