% ===========================================================================
% TIER 3 / call + fixpoint.  `union(I, ap1(G,fix(I,G)))  SUBSET  fix(I,G)` — the
% easy half of "the `Fix` node is a solution of the recursion it replaced"
% (`call_fix_solves_sub.p` is the other half, and `call_fix_least.p` is
% leastness).  It is `fix_pre` and `fix_closed` and needs no hypothesis at all.
% ===========================================================================
include('_signature.p').
include('_paths.p').
include('_fix_ops.p').
include('_call_ops.p').
tff(call_fix_solves_sup, conjecture,
    ! [I: space, G: bodyG] : sub(cup(I, ap1(G, fix(I,G))), fix(I,G)) ).
