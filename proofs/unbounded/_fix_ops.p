% =============================================================================
% TIER 3 operator module: FIXPOINT.  Include after `_signature.p`.  Needs
% nothing else — the fixpoint theory is pure lattice theory over `space`, so
% the fixpoint files carry no path structure and no arithmetic at all.
%
% Fixpoint is SECOND ORDER in Scala; its body is REIFIED into the sort `bodyG`
% (space -> space), applied by `ap1`, so the theorems below are schematic in the
% body.
%
%   Fixpoint(init,r,body) = the LEAST X containing init and closed under body
%
% ON THE AXIOMS.  docs/SUPERCOMPILER.md denotes `Space.Fixpoint` as "the
% union-saturating least fixpoint init u body[init] u body^2[init] ...", and
% `eval` runs exactly that Kleene chain until `nxt == cur`.  The three axioms
% below are instead the Knaster-Tarski / Park CHARACTERISATION of the least
% pre-fixpoint.  That the two agree is NOT assumed here: it is the separate
% conjecture of the six `kleene_*` files (`kleene_below_base/step`,
% `kleene_grows_base/step`, `kleene_acc_is_cur_base/step`) and their conclusion
% `kleene_conv.p`, which quantify over the chain index.  Assuming the agreement
% would have made those files vacuous.
% =============================================================================

tff(bodyg_type, type, bodyG: $tType ).

tff(ap1_type, type, ap1: ( bodyG * space ) > space ).
tff(fix_type, type, fix: ( space * bodyG ) > space ).

tff(fix_pre,    axiom, ! [I: space, G: bodyG] : sub(I, fix(I,G)) ).
tff(fix_closed, axiom, ! [I: space, G: bodyG] : sub(ap1(G, fix(I,G)), fix(I,G)) ).
tff(fix_least,  axiom,
    ! [I: space, G: bodyG, X: space] :
      ( ( sub(I,X) & sub(ap1(G,X), X) ) => sub(fix(I,G), X) ) ).

tff(monoG_type, type, monoG: bodyG > $o ).
tff(monoG_def, axiom,
    ! [G: bodyG] :
      ( monoG(G) <=> ! [S1: space, S2: space] : ( sub(S1,S2) => sub(ap1(G,S1), ap1(G,S2)) ) ) ).
