; TRUSTS: law:zipper-refinement

; BOUNDARY: zipper
; AUTO-GENERATED pipeline stage 2 (puzzle3-full) — DATA-AGNOSTIC: transpileZ(program) vs the program.
; LAW-JUSTIFIED-NO-RESIDUAL: an INSTANCE of the universal zipper refinement theorem —
;   proofs/zipper_refinement.smt2 (first-order, over the key-free local algebra; PROVED) and
;   proofs/lean/Zippy/Zipper.lean#Zippy.Zip.refinement (every constructor, boundaries named).
; SHELL: 1 node(s) transpiled with EVERY source opaque (SpaceZipper.Opaque); read back
; SHELL CONSTRUCTORS: Mention
; PROGRAM CONSTRUCTORS: Fixpoint, Singleton, Constant, Union, Mention, Iteration, Composition, TailsUnion, Intersection, Deref, Concat, Wrap, Unwrap, Literal, Raffination
; BINDERS: Fixpoint
; CALLS: 
; through spaceOfZipper it is alpha-EQUAL to the shell.
; HOLES (materialised by transpileZ and evaluated by the executor on BOTH sides — the theorem's
; `lit` boundaries): 1
;   #hole0 = Fixpoint
