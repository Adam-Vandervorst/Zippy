% =============================================================================
% TIER 3 operator module: RANGE (the POSITIONAL ordered slice).  Include after
% `_signature.p`.
%
%   Range(x, start, end) = the canonical-order slice [lo, hi) of x,
%                          with (lo, hi) = RangeBounds.normalize(|x|, start, end)
%
% RANGE IS OUTSIDE THE PATH-SET ALGEBRA and this module says exactly why, rather
% than leaving it as the one constructor with no obligation at all (which is what
% `src/test/scala/UnboundedTier.scala` did: its `operators` function fell through
% `Range` into its operand and reported the operand's coverage as the node's).
%
% WHAT MAKES IT DIFFERENT.  Every other operator is POINTWISE — whether `P` is in
% the result depends only on which paths are in the operands.  A window depends
% on the RANK of `P` among them, so it is not a function of membership alone: it
% is the one operator for which `mem(P, op(A))` cannot be written as a formula in
% `mem(-, A)`.  Two things follow, and both are certified here rather than
% assumed:
%   * a window is an INTERVAL of the canonical order (`range_interval.p`) — this
%     is the property that makes the four backends agree, since they all slice by
%     the SAME order (`pathValueOrdering`, "every backend slices Range by THIS
%     order, so they agree");
%   * a window is NOT THE IDENTITY for arbitrary endpoints
%     (`negative/not_range_identity.p`) — the near-miss of U61, whose full-window
%     hypothesis would be vacuous if it were provable.
%
% WHAT THIS MODULE CANNOT SAY, stated here because a previous revision claimed it
% could.  The ENDPOINTS BELOW ARE PATHS, NOT RANKS, so with them fixed the window
% is a pointwise order-interval filter — and such a filter IS MONOTONE: this
% module PROVES `sub(A,B) => sub(rng(A,Lo,Hi), rng(B,Lo,Hi))` from `rng_sub`,
% `rng_bounds` and `rng_full`.  The non-monotonicity of `Space.Range` is about
% RANK arithmetic (integer bounds against |x|, i.e. `RangeBounds.normalize`), which
% is tier-1/tier-2's subject and not expressible here.  `docs/TRUSTED.md` T5 records
% it as an executed observation rather than a theorem, and it is still why
% `AgnosticPipeline.monotoneInMention` and `MORKL.mono`/`monoIn` refuse a recursion
% variable under a `Range` — conservatively, so nothing unsound follows from the gap.
%
% ENCODING.  `plt` is the canonical STRICT TOTAL ORDER on paths (Scala:
% `pathValueOrdering` — item order, shorter-is-less on a shared prefix).  It is
% axiomatised as a strict total order and NOTHING ELSE: no law below depends on
% which order it is, only that there is one and that the window is one of its
% intervals.  `rng(A,S,E)` is the window; `S`/`E` are `num` bounds from `_nat.p`
% only where a law needs them, so this module does not drag arithmetic in.
% =============================================================================

tff(plt_type, type, plt: ( path * path ) > $o ).
tff(rng_type, type, rng: ( space * path * path ) > space ).

% `plt` is a strict total order.
tff(plt_irrefl, axiom, ! [P: path] : ~ plt(P,P) ).
tff(plt_trans,  axiom, ! [P: path, Q: path, R: path] : ( ( plt(P,Q) & plt(Q,R) ) => plt(P,R) ) ).
tff(plt_total,  axiom, ! [P: path, Q: path] : ( plt(P,Q) | P = Q | plt(Q,P) ) ).

% THE WINDOW, given as its two defining properties.  `rng(A,Lo,Hi)` is the set of
% paths of `A` that lie in the order-interval [Lo, Hi) — the ENDPOINTS ARE PATHS
% here, not ranks: what a law can use is that the slice is an interval, and
% naming the endpoints by rank would need the counting `_nat.p` cannot do
% pointwise.  `RangeBounds.normalize` is what picks the endpoints from the
% integer bounds; that arithmetic is tier-1/tier-2's job (`SpatialTypeSystem`'s
% `windowWidth`) and is not restated here.
tff(rng_sub,   axiom, ! [P: path, A: space, Lo: path, Hi: path] :
    ( mem(P, rng(A,Lo,Hi)) => mem(P, A) ) ).
tff(rng_bounds, axiom, ! [P: path, A: space, Lo: path, Hi: path] :
    ( mem(P, rng(A,Lo,Hi)) => ( ~ plt(P,Lo) & plt(P,Hi) ) ) ).
tff(rng_full,  axiom, ! [P: path, A: space, Lo: path, Hi: path] :
    ( ( mem(P,A) & ~ plt(P,Lo) & plt(P,Hi) ) => mem(P, rng(A,Lo,Hi)) ) ).
