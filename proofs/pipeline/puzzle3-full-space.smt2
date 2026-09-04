; TRUSTS: law:constant-ops

; BOUNDARY: space
; AUTO-GENERATED pipeline stage 1 (puzzle3-full) — INSTANCE: the program vs SC.reduce(program).
; LAW-JUSTIFIED-NO-RESIDUAL: the two sides are joined by 1 TRACE STEP(S), each a
; re-applied instance of a certified optimiser law (SC.verifyTrace: 0 failure(s); the laws'
; ∀-certificates are in proofs/laws/REGISTRY.tsv), composed end to end: the `after` of every
; step is the `before` of the next.  A step is a whole-term congruence (one law may rewrite
; several positions at once); the ∀-certificate covers every instance.
; INSTANCE-DIFFERENTIAL: 1 of 1 step results evaluate to the reference on this input.
; laws used: constant-ops
; STEP   0  constant-ops                  e9524e94292d -> d69426f24e10   certificate(s): constant-ops ⟶ GROUND — per-op threeway_*/impl_* characterizations, eval-gated (registry: constant-ops)
; endpoints: e9524e94292d (program) -> d69426f24e10 (SC.reduce)
