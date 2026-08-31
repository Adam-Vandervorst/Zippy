% ===========================================================================
% TIER 3 / composition.
%
% Composition is a MONOID on spaces, with `{eps}` as its unit and `{}` as its
% annihilator.  Associativity is inherited from associativity of append; the unit
% laws are where the certified append-nil lemma (proofs/lemma_append_nil.smt2)
% does its work.  Tier-1 prices `Composition` as the product of the operand sizes
% and tier-2 linearises that product against the baseline endpoints; both take the
% underlying monoid structure for granted.
%
% GENERALISES: proofs/composition.smt2 and proofs/composition_norm.smt2
% (instance tier), tier-1's Composition size arm `n_a * n_b`
%
% THIS FILE: THE UNIT AND ANNIHILATOR LAWS.  `{eps}` is a two-sided unit (the
% right unit is where proofs/lemma_append_nil.smt2's `append q nil = q` is used)
% and `{}` is a two-sided annihilator.  Associativity is `composition_assoc.p`.
%
% VERDICT: PROVED by vampire in 0.3s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').

tff(composition_unit, conjecture,
    ! [A: space] :
      ( comp(sing(nil), A) = A
      & comp(A, sing(nil)) = A
      & comp(empty, A) = empty
      & comp(A, empty) = empty ) ).
