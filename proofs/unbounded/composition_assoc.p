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
% THIS FILE: ASSOCIATIVITY ALONE.  Split off from the unit/annihilator laws
% because it is by far the harder half — two nested existential unpackings on
% each side — and a conjunction of the two timed out at 120 s in portfolio mode
% while each half separately is closed in seconds.  A conjunctive goal is a
% DISJUNCTION after negation, and saturation has to refute all of it at once.
%
% VERDICT: PROVED by vampire in 6.1s.
% MEASURED 2026-08-31, vampire 5.1.0 (commit 7b2f410), --mode casc, 16-core x86_64 Linux 6.17.
% ===========================================================================

include('_signature.p').
include('_paths.p').
include('_concat_ops.p').

tff(composition_assoc, conjecture,
    ! [A: space, B: space, C: space] :
      ( comp(comp(A,B),C) = comp(A,comp(B,C)) ) ).
