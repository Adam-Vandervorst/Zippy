% =============================================================================
% TIER 3 operator module: CALL (routine application and recursion).  Include
% after `_signature.p` and `_fix_ops.p` (a recursive call's meaning IS a `fix`).
%
%   Call(r, refs; mentions) = eval the body of `r` with the arguments bound
%
% WHAT THE OBLIGATIONS ARE ABOUT.  `src/test/scala/UnboundedTier.scala` used to
% drop the `Call` node itself and recurse only into its arguments, so a program
% built entirely out of routine calls reported the coverage of its ARGUMENTS and
% nothing about the calls.  Two claims the compiler actually relies on:
%
%   (1) UNFOLDING an acyclic call is meaning-preserving: `call(R,S) = ap1(G_R,S)`
%       where `G_R` is the routine's reified body.  This is `eval`'s Call rule and
%       `Lower.inline`'s licence (`call_unfold.p`).
%   (2) A union-saturating SELF-recursion's least solution IS the `Fix` node the
%       lowering produces: if `S = union(I, ap1(G,S))` and `S` is least among such,
%       then `S = fix(I, G)` (`call_fix.p`).  This is the theorem `asFixpoint` and
%       `asFixpointGeneral` need at the unbounded tier, and it is the statement
%       `terminating/asfixpoint_sound.smt2` (O2) makes for one concrete recurrence.
%
% WHAT IS *NOT* CLAIMED, AND WHERE IT LIVES.  Neither file says anything about
% CAPTURE-AVOIDING SUBSTITUTION — that `body[m := s]` as computed by
% `substMention`/`Lower.inline` denotes `[[body]]{m -> [[s]]}` under an
% `Iteration`/`Fold`/`Fixpoint` binder.  That is a statement about the SYNTAX-TO-
% SEMANTICS map, which this tier's reified encoding cannot see: here a body IS
% its semantic function `bodyG`, so substitution is application and is true by
% congruence.  It is registry row O6a in `terminating/REGISTRY.tsv`, it is OPEN,
% and `src/test/scala/SubstConformance.scala` is the randomized differential that
% stands in for it.  Saying so is the point of this paragraph: `call_unfold.p`
% below is NOT that theorem and must not be read as it.
% =============================================================================

tff(routine_type, type, routine: $tType ).
tff(rbody_type,   type, rbody: routine > bodyG ).
tff(call_type,    type, call:  ( routine * space ) > space ).

% (1) eval's Call rule: a call is the body applied to the argument.
tff(call_def, axiom,
    ! [R: routine, S: space] : call(R,S) = ap1(rbody(R), S) ).

% a space that solves the union-saturating recursion `r(m) = m u r(T(m))`, in the
% form `asFixpoint` recognises: `S` is a solution above `I` for the step `G`.
tff(satsol_type, type, satSol: ( space * bodyG * space ) > $o ).
tff(satsol_def, axiom,
    ! [I: space, G: bodyG, S: space] :
      ( satSol(I,G,S) <=> S = cup(I, ap1(G,S)) ) ).
