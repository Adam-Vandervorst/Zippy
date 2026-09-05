; TRUSTS: -
; INSTANCE-DIFFERENTIAL: GraphExec.runGraphT(optimize(transpile(program))) == eval(program) on this input
; (Scala assertEquals); the obligation below is the instance (data-agnostic obligation + differential) one, which covers this input.

; BOUNDARY: graph
; RESIDUAL CUT (k=2) LIFTED: the sides carry 1 residual cut(s), the SAME on both sides:
;   sn_tc@2(; S"edges", (((S"edges" \/ (S"edges".iter(P"av1", S"ar2", 
 (P"av1" x TailsUnion((S"edges" <| S"ar2")))
) \ S"edges")) \/ ((S"edges".iter(P"av5", S"ar6", 
 (P"av5" x TailsUnion((S"edges" <| S"ar6")))
) \ S"edges").iter(P"av3", S"ar4", 
 (P"av3" x TailsUnion((S"edges" <| S"ar4")))
) \ (S"edges" \/ (S"edges".iter(P"av7", S"ar8", 
 (P"av7" x TailsUnion((S"edges" <| S"ar8")))
) \ S"edges")))) \/ (((S"edges".iter(P"av13", S"ar14", 
 (P"av13" x TailsUnion((S"edges" <| S"ar14")))
) \ S"edges").iter(P"av11", S"ar12", 
 (P"av11" x TailsUnion((S"edges" <| S"ar12")))
) \ (S"edges" \/ (S"edges".iter(P"av15", S"ar16", 
 (P"av15" x TailsUnion((S"edges" <| S"ar16")))
) \ S"edges"))).iter(P"av9", S"ar10", 
 (P"av9" x TailsUnion((S"edges" <| S"ar10")))
) \ ((S"edges" \/ (S"edges".iter(P"av17", S"ar18", 
 (P"av17" x TailsUnion((S"edges" <| S"ar18")))
) \ S"edges")) \/ ((S"edges".iter(P"av21", S"ar22", 
 (P"av21" x TailsUnion((S"edges" <| S"ar22")))
) \ S"edges").iter(P"av19", S"ar20", 
 (P"av19" x TailsUnion((S"edges" <| S"ar20")))
) \ (S"edges" \/ (S"edges".iter(P"av23", S"ar24", 
 (P"av23" x TailsUnion((S"edges" <| S"ar24")))
) \ S"edges")))))), (((S"edges".iter(P"av5", S"ar6", 
 (P"av5" x TailsUnion((S"edges" <| S"ar6")))
) \ S"edges").iter(P"av3", S"ar4", 
 (P"av3" x TailsUnion((S"edges" <| S"ar4")))
) \ (S"edges" \/ (S"edges".iter(P"av7", S"ar8", 
 (P"av7" x TailsUnion((S"edges" <| S"ar8")))
) \ S"edges"))).iter(P"av1", S"ar2", 
 (P"av1" x TailsUnion((S"edges" <| S"ar2")))
) \ ((S"edges" \/ (S"edges".iter(P"av9", S"ar10", 
 (P"av9" x TailsUnion((S"edges" <| S"ar10")))
) \ S"edges")) \/ ((S"edges".iter(P"av13", S"ar14", 
 (P"av13" x TailsUnion((S"edges" <| S"ar14")))
) \ S"edges").iter(P"av11", S"ar12", 
 (P"av11" x TailsUnion((S"edges" <| S"ar12")))
) \ (S"edges" \/ (S"edges".iter(P"av15", S"ar16", 
 (P"av15" x TailsUnion((S"edges" <| S"ar16")))
) \ S"edges"))))))
; so this cell's claim is quantified over the cut's free input, and holds for EVERY value of it;
; the recursion is identical on both sides, so by proofs/lean/Zippy/Positive.lean#
; Zippy.Space.fixpoint_denT_eq_of_step_eq (2E.1) the claim about the unrollings IS the claim
; about the recursion.  (Formerly stamped BOUNDED-UNROLLING under O10b, which is now mechanized.)
; AUTO-GENERATED — pipeline graph (datalog-sn), instance (data-agnostic obligation + differential)
; TRIVIAL-NO-OBLIGATION: the two sides are syntactically identical after alpha-normalisation
; (0 candidate pair(s), 0 reflexive after freeing binders).  Recorded as a
; no-obligation marker; the runner counts these and invokes no prover on them.
