; TRUSTS: O6a, law:algebraic-identities, law:constant-ops, law:iter-comp-right-hoist, law:iter-union-indep

; BOUNDARY: graph
; AUTO-GENERATED — pipeline graph (puzzle15), data-agnostic
; LAW-JUSTIFIED-NO-RESIDUAL: all 3 differing pair(s) (of 3 candidates,
; 0 reflexive-after-freeing) are verified instances of the optimiser's ∀-certified law
; set — each right side is reproduced EXACTLY by replaying the named laws on the left side
; (proof-carrying transformation).  No per-program prover obligation remains; the universal
; certificates are the proofs/ files named per pair below.
; LAW-JUSTIFIED pair 0: join: algebraic-identities + iter-union-indep
;   certificate(s): algebraic-identities ⟶ proofs/laws/law_{union_unit,inter_empty,sub_empty,union_idem,inter_idem,sub_self}.smt2; iter-union-indep ⟶ proofs/laws/law_guard_hoist.smt2 (+ the bare-hoist fail-check in formal.egg)
; LAW-JUSTIFIED pair 1: join: algebraic-identities + iter-comp-right-hoist
;   certificate(s): algebraic-identities ⟶ proofs/laws/law_{union_unit,inter_empty,sub_empty,union_idem,inter_idem,sub_self}.smt2; iter-comp-right-hoist ⟶ proofs/laws/law_iter_comp_right_hoist.smt2
; LAW-JUSTIFIED pair 2: constant-ops
;   certificate(s): constant-ops ⟶ GROUND — per-op threeway_*/impl_* characterizations, eval-gated (registry: constant-ops)
