; AUTO-GENERATED — pipeline stage 1 (datalog-sn): original vs optimised (∀ paths)
; IDENTICAL-STRUCTURE-NO-EQUIVALENCE-OBLIGATION: the two sides compile to the SAME shared
; membership macro — they are the same local-algebra term, so `(= (m_1 p) (m_1 p))` expands to
; `true` and no prover would do any work on it.  The structural identity IS the equivalence
; result for this cell (it is checked in Scala, not asserted here); the optimiser/transpiler
; comparison that is NOT definitional for this stone is carried by the -agnostic twin.
