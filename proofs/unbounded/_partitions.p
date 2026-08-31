% =============================================================================
% TIER 3 module: THE STAGED DISJOINT DECOMPOSITIONS.  Include after
% `_signature.p`.
%
% Every formula here is a conjunct of `set_partitions.p`'s conjecture (PROVED —
% see STATUS.tsv), imported so the cardinality theorems do not have to re-derive
% the decompositions from `mem` inside their own saturation.  Same staging
% discipline as `_lattice_lemmas.p`: a lemma is a premise here only because it
% is a conclusion there.
% =============================================================================

tff(part_cup,      axiom, ! [A: space, B: space] : cup(A, sdiff(B,A)) = cup(A,B) ).
tff(part_cup_disj, axiom, ! [A: space, B: space] : disj(A, sdiff(B,A)) ).
tff(part_cap,      axiom, ! [A: space, B: space] : cup(cap(A,B), sdiff(B,A)) = B ).
tff(part_cap_disj, axiom, ! [A: space, B: space] : disj(cap(A,B), sdiff(B,A)) ).
