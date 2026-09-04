; TRUSTS: law:algebraic-identities, law:constant-ops, law:iterate-literal-union

; BOUNDARY: space
; AUTO-GENERATED pipeline stage 1 (nqueens) — INSTANCE: the program vs SC.reduce(program).
; LAW-JUSTIFIED-NO-RESIDUAL: the two sides are joined by 3 TRACE STEP(S), each a
; re-applied instance of a certified optimiser law (SC.verifyTrace: 0 failure(s); the laws'
; ∀-certificates are in proofs/laws/REGISTRY.tsv), composed end to end: the `after` of every
; step is the `before` of the next.  A step is a whole-term congruence (one law may rewrite
; several positions at once); the ∀-certificate covers every instance.
; INSTANCE-DIFFERENTIAL: 3 of 3 step results evaluate to the reference on this input.
; laws used: algebraic-identities, constant-ops, iterate-literal-union
; STEP   0  constant-ops                  db9a69a5c993 -> f0eac2a94dca   certificate(s): constant-ops ⟶ GROUND — per-op threeway_*/impl_* characterizations, eval-gated (registry: constant-ops)
; STEP   1  algebraic-identities          f0eac2a94dca -> 8eebcc06655b   certificate(s): algebraic-identities ⟶ proofs/laws/law_{union_unit,inter_empty,sub_empty,union_idem,inter_idem,sub_self}.smt2
; STEP   2  iterate-literal-union         8eebcc06655b -> b451e3688e85   certificate(s): iterate-literal-union ⟶ proofs/keyfold_iter.smt2 (SCHEMATIC: exact ground keys)
; endpoints: db9a69a5c993 (program) -> b451e3688e85 (SC.reduce)
