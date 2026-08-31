% =============================================================================
% TIER 3 module: THE STAGED LATTICE LEMMAS.  Include after `_signature.p`.
%
% Every formula in this file is a CONJUNCT OF A CONJECTURE PROVED ELSEWHERE IN
% THIS CORPUS, imported here so that the harder operator theorems do not have to
% re-derive the inclusion lattice from `mem` and extensionality inside their own
% saturation.  This is the staging discipline terminating/reachable_value.p uses
% for `step_in_mask` and terminating/scc_decrease.p for its `pred_*` / `desc_*`
% facts: a lemma is a premise HERE only because it is a conclusion THERE.
%
%   sub_refl / sub_trans / sub_antisym / empty_bot   lattice_order.p   PROVED
%   cup_ub1 / cup_ub2 / cup_lub                      lattice_union.p   PROVED
%   cup_idem / cup_comm / cup_assoc / cup_empty      lattice_union.p   PROVED
%   cap_lb1 / cap_lb2 / cap_glb                      lattice_inter.p   PROVED
%   sdiff_sub / sdiff_disj / sdiff_split             subtraction.p     PROVED
%   cup_mono / cap_mono                              mono_setops.p     PROVED
%
% NOTHING HERE IS NEW.  If a verdict in proofs/unbounded/STATUS.tsv ever regresses
% for one of the six source files above, the corresponding line below stops being
% a lemma and becomes an assumption — which is why `run.sh` runs the whole corpus
% and REGISTRY.tsv records the dependency explicitly.
% =============================================================================

tff(sub_refl,    axiom, ! [A: space] : sub(A,A) ).
tff(sub_trans,   axiom, ! [A: space, B: space, C: space] : ( ( sub(A,B) & sub(B,C) ) => sub(A,C) ) ).
tff(sub_antisym, axiom, ! [A: space, B: space] : ( ( sub(A,B) & sub(B,A) ) => A = B ) ).
tff(empty_bot,   axiom, ! [A: space] : sub(empty, A) ).

tff(cup_ub1,  axiom, ! [A: space, B: space] : sub(A, cup(A,B)) ).
tff(cup_ub2,  axiom, ! [A: space, B: space] : sub(B, cup(A,B)) ).
tff(cup_lub,  axiom, ! [A: space, B: space, C: space] : ( ( sub(A,C) & sub(B,C) ) => sub(cup(A,B), C) ) ).
tff(cup_idem,  axiom, ! [A: space] : cup(A,A) = A ).
tff(cup_comm,  axiom, ! [A: space, B: space] : cup(A,B) = cup(B,A) ).
tff(cup_assoc, axiom, ! [A: space, B: space, C: space] : cup(cup(A,B),C) = cup(A,cup(B,C)) ).
tff(cup_empty, axiom, ! [A: space] : cup(A, empty) = A ).

tff(cap_lb1, axiom, ! [A: space, B: space] : sub(cap(A,B), A) ).
tff(cap_lb2, axiom, ! [A: space, B: space] : sub(cap(A,B), B) ).
tff(cap_glb, axiom, ! [A: space, B: space, C: space] : ( ( sub(C,A) & sub(C,B) ) => sub(C, cap(A,B)) ) ).

tff(sdiff_sub,   axiom, ! [A: space, B: space] : sub(sdiff(A,B), A) ).
tff(sdiff_disj,  axiom, ! [A: space, B: space] : disj(sdiff(A,B), B) ).
tff(sdiff_split, axiom, ! [A: space, B: space] : cup(cap(A,B), sdiff(A,B)) = A ).

tff(cup_mono, axiom,
    ! [A: space, B: space, C: space, D: space] :
      ( ( sub(A,C) & sub(B,D) ) => sub(cup(A,B), cup(C,D)) ) ).
tff(cap_mono, axiom,
    ! [A: space, B: space, C: space, D: space] :
      ( ( sub(A,C) & sub(B,D) ) => sub(cap(A,B), cap(C,D)) ) ).
