; AUTO-GENERATED — pipeline space (puzzle15), data-agnostic
; LAW-JUSTIFIED-NO-RESIDUAL: all 3 differing pair(s) (of 3 candidates,
; 0 reflexive-after-freeing) are verified instances of the optimiser's ∀-certified law
; set — each right side is reproduced EXACTLY by replaying the named laws on the left side
; (proof-carrying transformation).  No per-program prover obligation remains; the universal
; certificates are the proofs/ files named per pair below.
; LAW-JUSTIFIED pair 0: constant-ops
;   certificate(s): constant-ops ⟶ GROUND — per-op threeway_*/impl_* characterizations, eval-gated (registry: constant-ops)
; LAW-JUSTIFIED pair 1: comp-wrap-assoc
;   certificate(s): comp-wrap-assoc ⟶ proofs/laws/law_comp_wrap_assoc.smt2
; LAW-JUSTIFIED pair 2: reduce-join: constant-ops + comp-assoc-right + unwrap-concat-unwraps
;   certificate(s): constant-ops ⟶ GROUND — per-op threeway_*/impl_* characterizations, eval-gated (registry: constant-ops); comp-assoc-right ⟶ proofs/laws/law_comp_assoc.smt2; unwrap-concat-unwraps ⟶ proofs/laws/law_unwrap_merge.smt2
