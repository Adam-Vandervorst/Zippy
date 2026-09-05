; TRUSTS: law:comp-wrap-assoc, law:constant-ops, law:unwrap-concat-unwraps

; BOUNDARY: space
; AUTO-GENERATED pipeline stage 1 (puzzle15) — INSTANCE: the program vs SC.reduce(program).
; LAW-JUSTIFIED-NO-RESIDUAL: the two sides are joined by 4 TRACE STEP(S), each a
; re-applied instance of a certified optimiser law (SC.verifyTrace: 0 failure(s); the laws'
; ∀-certificates are in proofs/laws/REGISTRY.tsv), composed end to end: the `after` of every
; step is the `before` of the next.  A step is a whole-term congruence (one law may rewrite
; several positions at once); the ∀-certificate covers every instance.
; INSTANCE-DIFFERENTIAL: 4 of 4 step results evaluate to the reference on this input.
; laws used: comp-wrap-assoc, constant-ops, unwrap-concat-unwraps
; STEP   0  constant-ops                  5f76bfdfdbb2 -> f3966b27a18e   certificate(s): constant-ops ⟶ GROUND — per-op threeway_*/impl_* characterizations, eval-gated (registry: constant-ops)
; STEP   1  unwrap-concat-unwraps         f3966b27a18e -> 332b479e5d38   certificate(s): unwrap-concat-unwraps ⟶ proofs/laws/law_unwrap_merge.smt2
; STEP   2  comp-wrap-assoc               332b479e5d38 -> 0a22646a30b3   certificate(s): comp-wrap-assoc ⟶ proofs/laws/law_comp_wrap_assoc.smt2
; STEP   3  unwrap-concat-unwraps         0a22646a30b3 -> 167fddd32b1b   certificate(s): unwrap-concat-unwraps ⟶ proofs/laws/law_unwrap_merge.smt2
; endpoints: 5f76bfdfdbb2 (program) -> 167fddd32b1b (SC.reduce)
