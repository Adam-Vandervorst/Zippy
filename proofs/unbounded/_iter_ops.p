% =============================================================================
% TIER 3 operator module: ITERATION.  Include after `_signature.p`, `_paths.p`
% AND `_tails_ops.p` (iteration is defined over `headed` / `grp`).
%
% Iteration is SECOND ORDER in Scala: its body is a term with a free binder.
% FOL cannot quantify over functions, so the body is REIFIED into the sort
% `bodyF` (head item + rest space -> space), applied by `ap2`.  A theorem
% quantified over `bodyF` is then schematic IN THE BODY, which is the sharpest
% thing tier-1/tier-2 cannot do: `Lower.sizeBounds` and `SizeZ3` both re-analyse
% the one concrete body AST they are handed.
%
%   Iteration(src,h,rest,body) = union over the head groups of src of body[h,rest]
% =============================================================================

tff(bodyf_type, type, bodyF: $tType ).

tff(ap2_type,  type, ap2:  ( bodyF * item * space ) > space ).
tff(iter_type, type, iter: ( space * bodyF ) > space ).

tff(iter_def, axiom,
    ! [P: path, A: space, F: bodyF] :
      ( mem(P, iter(A,F))
    <=> ? [H: item] : ( headed(H,A) & mem(P, ap2(F, H, grp(H,A))) ) ) ).

% monotone iteration body — the hypothesis every iteration monotonicity theorem
% needs, and the one `SpatialCost.fixRounds` currently decides only
% SYNTACTICALLY (a `Union(Mention(rec), _)` pattern match).
tff(monoB_type, type, monoB: bodyF > $o ).
tff(monoB_def, axiom,
    ! [F: bodyF] :
      ( monoB(F)
    <=> ! [H: item, S1: space, S2: space] :
          ( sub(S1,S2) => sub(ap2(F,H,S1), ap2(F,H,S2)) ) ) ).
