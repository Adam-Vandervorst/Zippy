; TRUSTS: law:zipper-refinement

; BOUNDARY: zipper
; AUTO-GENERATED pipeline stage 2 (temperature) — INSTANCE: transpileZ(program) vs the program.
; LAW-JUSTIFIED-NO-RESIDUAL: an INSTANCE of the universal zipper refinement theorem —
;   proofs/zipper_refinement.smt2 (first-order, over the key-free local algebra; PROVED) and
;   proofs/lean/Zippy/Zipper.lean#Zippy.Zip.refinement (every constructor, boundaries named).
; SHELL: 7 node(s) transpiled with EVERY source opaque (SpaceZipper.Opaque); read back
; SHELL CONSTRUCTORS: Union, Restriction, Mention, Literal
; PROGRAM CONSTRUCTORS: Union, Restriction, Mention, Literal
; BINDERS: 
; CALLS: 
; through spaceOfZipper it is alpha-EQUAL to the shell.
; HOLES (materialised by transpileZ and evaluated by the executor on BOTH sides — the theorem's
; `lit` boundaries): 0
; INSTANCE-DIFFERENTIAL: SpaceZipper.materialize(transpileZ(program)) == eval(program) on this input (Scala assertEquals).
