% =============================================================================
% TIER 3 operator module: FOLD (the SEQUENTIAL fold).  Include after
% `_signature.p` and `_tails_ops.p` (fold is defined over `headed` / `grp`).
%
%   Fold(src, initial, acc, sym, rest, body, update)
%
% `eval`'s rule (MORKL.scala): walk the head groups of `src` IN CANONICAL HEAD
% ORDER, threading a PATH-VALUED accumulator; at each group emit
% `body[acc, sym, rest]` and advance the accumulator by `update[acc, sym, rest]`.
% The result is the union of the per-group emissions.
%
% WHY IT IS NOT `Iteration`.  `src/test/scala/UnboundedTier.scala` used to key a
% `Fold` node to the string `"iteration"`, so the coverage table reported the
% iteration laws as covering it.  They do not: an `Iteration` body sees only
% `(head, tails)` and is therefore INDEPENDENT ACROSS GROUPS, while a `Fold`
% body additionally sees an accumulator that DEPENDS ON EVERY EARLIER GROUP.
% Two consequences the alias hid:
%   * the group order is observable, so no law may reorder or split the source
%     the way `iteration_split.p` splits an `Iteration` (negative control
%     `negative/not_fold_eq_iter.p`);
%   * the accumulator is a genuine extra input to the body, which is why
%     `AgnosticPipeline.monotoneInMention` treats `Fold` as unknown variance.
% The alias IS sound under one hypothesis — an update that never moves the
% accumulator — and that hypothesis is `constU` below, certified as
% `fold_iter_const.p` instead of assumed.
%
% ENCODING.  The body is third-order in Scala (accumulator, head, tails) and is
% REIFIED as the sort `bodyA`, applied by `ap3`; the update is `updA`, applied by
% `apu`.  `facc(A,U,I,H)` is the accumulator value the walk has REACHED when it
% arrives at head `H` — uninterpreted in general (it depends on the head order,
% which this tier deliberately does not axiomatise), and pinned to `I` exactly
% when the update is constant.  Everything provable below is provable WITHOUT
% knowing the order, which is the point: those are the laws that hold for every
% order, hence for the canonical one the backends agree on.
% =============================================================================

tff(bodya_type, type, bodyA: $tType ).
tff(upda_type,  type, updA:  $tType ).

tff(ap3_type,  type, ap3:  ( bodyA * path * item * space ) > space ).
tff(apu_type,  type, apu:  ( updA  * path * item * space ) > path ).
tff(facc_type, type, facc: ( space * updA * path * item ) > path ).
tff(fold_type, type, fold: ( space * bodyA * updA * path ) > space ).

% eval's Fold rule, with the reached accumulator abstracted into `facc`.
tff(fold_def, axiom,
    ! [P: path, A: space, F: bodyA, U: updA, I: path] :
      ( mem(P, fold(A,F,U,I))
    <=> ? [H: item] :
          ( headed(H,A) & mem(P, ap3(F, facc(A,U,I,H), H, grp(H,A))) ) ) ).

% an update that never moves the accumulator.  This is the ONLY hypothesis under
% which a Fold degenerates to an Iteration, and `fold_iter_const.p` proves that.
tff(constu_type, type, constU: updA > $o ).
tff(constu_def, axiom,
    ! [U: updA] :
      ( constU(U)
    <=> ! [Acc: path, H: item, S: space] : apu(U, Acc, H, S) = Acc ) ).

% under a constant update the walk never advances: every group sees `I`.
tff(facc_const, axiom,
    ! [A: space, U: updA, I: path, H: item] :
      ( constU(U) => facc(A,U,I,H) = I ) ).

% monotone fold body, in the TAILS argument only — the accumulator is a path, so
% there is no order on it to be monotone in.
tff(monoa_type, type, monoA: bodyA > $o ).
tff(monoa_def, axiom,
    ! [F: bodyA] :
      ( monoA(F)
    <=> ! [Acc: path, H: item, S1: space, S2: space] :
          ( sub(S1,S2) => sub(ap3(F,Acc,H,S1), ap3(F,Acc,H,S2)) ) ) ).
