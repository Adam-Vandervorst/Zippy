; AUTO-GENERATED — pipeline space (nqueens), data-agnostic
; LAW-JUSTIFIED-NO-RESIDUAL: all 4 differing pair(s) (of 4 candidates,
; 0 reflexive-after-freeing) are verified instances of the optimiser's ∀-certified law
; set — each right side is reproduced EXACTLY by replaying the named laws on the left side
; (proof-carrying transformation).  No per-program prover obligation remains; the universal
; certificates are the proofs/ files named per pair below.
; LAW-JUSTIFIED pair 0: reduce-join: constant-ops
;   certificate(s): constant-ops ⟶ GROUND — per-op threeway_*/impl_* characterizations, eval-gated (registry: constant-ops)
; LAW-JUSTIFIED pair 1: reduce-join: constant-ops + iterate-literal-union + singleton-space-op-path-op + algebraic-identities + comp-lit-to-wraps
;   certificate(s): constant-ops ⟶ GROUND — per-op threeway_*/impl_* characterizations, eval-gated (registry: constant-ops); iterate-literal-union ⟶ proofs/keyfold_iter.smt2 (SCHEMATIC: exact ground keys); singleton-space-op-path-op ⟶ proofs/laws/law_wrap_set.smt2 + proofs/laws/law_unwrap_set.smt2; algebraic-identities ⟶ proofs/laws/law_{union_unit,inter_empty,sub_empty,union_idem,inter_idem,sub_self}.smt2; comp-lit-to-wraps ⟶ proofs/laws/law_comp_lit_wraps.smt2
; LAW-JUSTIFIED pair 2: reduce-join: constant-ops + iterate-literal-union + singleton-space-op-path-op + algebraic-identities + comp-lit-to-wraps
;   certificate(s): constant-ops ⟶ GROUND — per-op threeway_*/impl_* characterizations, eval-gated (registry: constant-ops); iterate-literal-union ⟶ proofs/keyfold_iter.smt2 (SCHEMATIC: exact ground keys); singleton-space-op-path-op ⟶ proofs/laws/law_wrap_set.smt2 + proofs/laws/law_unwrap_set.smt2; algebraic-identities ⟶ proofs/laws/law_{union_unit,inter_empty,sub_empty,union_idem,inter_idem,sub_self}.smt2; comp-lit-to-wraps ⟶ proofs/laws/law_comp_lit_wraps.smt2
; LAW-JUSTIFIED pair 3: reduce-join: constant-ops + iterate-literal-union + singleton-space-op-path-op + comp-lit-to-wraps
;   certificate(s): constant-ops ⟶ GROUND — per-op threeway_*/impl_* characterizations, eval-gated (registry: constant-ops); iterate-literal-union ⟶ proofs/keyfold_iter.smt2 (SCHEMATIC: exact ground keys); singleton-space-op-path-op ⟶ proofs/laws/law_wrap_set.smt2 + proofs/laws/law_unwrap_set.smt2; comp-lit-to-wraps ⟶ proofs/laws/law_comp_lit_wraps.smt2
