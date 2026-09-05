; TRUSTS: law:unwrap-concat-unwraps

; BOUNDARY: space
; AUTO-GENERATED pipeline stage 1 (aunt) — INSTANCE: the program vs SC.reduce(program).
; LAW-JUSTIFIED-NO-RESIDUAL: the two sides are joined by 1 TRACE STEP(S), each a
; re-applied instance of a certified optimiser law (SC.verifyTrace: 0 failure(s); the laws'
; ∀-certificates are in proofs/laws/REGISTRY.tsv), composed end to end: the `after` of every
; step is the `before` of the next.  A step is a whole-term congruence (one law may rewrite
; several positions at once); the ∀-certificate covers every instance.
; INSTANCE-DIFFERENTIAL: 1 of 1 step results evaluate to the reference on this input.
; laws used: unwrap-concat-unwraps
; STEP   0  unwrap-concat-unwraps         6fdc8f8b5ec9 -> 88999f83b9ec   certificate(s): unwrap-concat-unwraps ⟶ proofs/laws/law_unwrap_merge.smt2
; endpoints: 6fdc8f8b5ec9 (program) -> 88999f83b9ec (SC.reduce)
