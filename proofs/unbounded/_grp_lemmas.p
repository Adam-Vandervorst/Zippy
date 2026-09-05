% =============================================================================
% TIER 3 module: STAGED HEAD-GROUP LEMMAS.  Include after `_signature.p`,
% `_paths.p` and `_tails_ops.p`.
%
% The five conjuncts of `grp_union.p`'s conjecture (PROVED — see STATUS.tsv),
% imported as premises for `iteration_split.p`.  Same staging discipline as
% `_lattice_lemmas.p` and `_partitions.p`.
% =============================================================================

tff(grp_cup,     axiom, ! [H: item, A: space, B: space] : grp(H, cup(A,B)) = cup(grp(H,A), grp(H,B)) ).
tff(grp_unheaded, axiom, ! [H: item, B: space] : ( ~ headed(H,B) => grp(H,B) = empty ) ).
tff(headed_cup,  axiom,
    ! [H: item, A: space, B: space] : ( headed(H, cup(A,B)) <=> ( headed(H,A) | headed(H,B) ) ) ).
tff(grp_cup_l,   axiom,
    ! [H: item, A: space, B: space] : ( ~ headed(H,B) => grp(H, cup(A,B)) = grp(H,A) ) ).
tff(grp_cup_r,   axiom,
    ! [H: item, A: space, B: space] : ( ~ headed(H,A) => grp(H, cup(A,B)) = grp(H,B) ) ).
