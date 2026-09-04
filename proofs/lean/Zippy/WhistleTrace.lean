/-
==================================================================================================
GENERATED — the whistle correspondence trace (plan.md 2E.3).  DO NOT EDIT.

Regenerate with `ZIPPY_REGENERATE=1 sbt --server 'testOnly morkl.WhistleTrace'`; without the flag the suite
writes to `target/artifact-scratch` and DIFFS against this file.

WHAT THIS FILE IS.  Each `example` below is a pair of configurations `Matching.embeds` ACTUALLY
compared while running the seeded drives of `WhistleTrace`, rendered as label trees by `Matching.toLabel` (the alphabet
`Matching.labelOf` fixes), with the verdict the Scala returned.  `Zippy.Whistle.embedsB` re-decides
each one; `embedsB_iff` proves `embedsB` IS the relation `kruskal` shows to be a well-quasi-order,
so an agreeing trace is what makes that theorem a statement about the implemented whistle.

  pairs recorded            7
  emitted as EXAMPLES       7
  dropped, grounded         0   (a Grounded* closure's identity is not reproducible)
  dropped, over the cap     0
==================================================================================================
-/
import Zippy.Whistle

namespace Zippy.WhistleTrace
open Zippy.Whistle

/-- pair 1 (litAtoms = true) -/
example : embedsB
    (.node (.ctor "Iteration") [(.node (.litAtom) []), (.node (.ctor "Union") [(.node (.mentionVar) []), (.node (.litAtom) [])])])
    (.node (.ctor "Iteration") [(.node (.litAtom) []), (.node (.ctor "Iteration") [(.node (.mentionVar) []), (.node (.ctor "Union") [(.node (.mentionVar) []), (.node (.litAtom) [])])])])
  = true := by simp [embedsB, zipAll]

/-- pair 2 (litAtoms = true) -/
example : embedsB
    (.node (.ctor "Iteration") [(.node (.litAtom) []), (.node (.ctor "Iteration") [(.node (.mentionVar) []), (.node (.ctor "Union") [(.node (.mentionVar) []), (.node (.litAtom) [])])])])
    (.node (.ctor "Iteration") [(.node (.litAtom) []), (.node (.ctor "Union") [(.node (.mentionVar) []), (.node (.litAtom) [])])])
  = false := by simp [embedsB, zipAll]

/-- pair 3 (litAtoms = true) -/
example : embedsB
    (.node (.call "f" 0 1) [(.node (.litAtom) [])])
    (.node (.call "f" 0 1) [(.node (.ctor "Union") [(.node (.litAtom) []), (.node (.litAtom) [])])])
  = true := by simp [embedsB, zipAll]

/-- pair 4 (litAtoms = true) -/
example : embedsB
    (.node (.call "f" 0 1) [(.node (.litAtom) [])])
    (.node (.call "g" 0 1) [(.node (.litAtom) [])])
  = false := by simp [embedsB, zipAll]

/-- pair 5 (litAtoms = true) -/
example : embedsB
    (.node (.call "grow" 0 2) [(.node (.litAtom) []), (.node (.litAtom) [])])
    (.node (.call "grow" 0 2) [(.node (.litAtom) []), (.node (.litAtom) [])])
  = true := by simp [embedsB, zipAll]

/-- pair 6 (litAtoms = true) -/
example : embedsB
    (.node (.call "grow" 0 2) [(.node (.litAtom) []), (.node (.litAtom) [])])
    (.node (.call "grow" 0 2) [(.node (.mentionVar) []), (.node (.litAtom) [])])
  = false := by simp [embedsB, zipAll]

/-- pair 7 (litAtoms = true) -/
example : embedsB
    (.node (.call "grow" 0 2) [(.node (.mentionVar) []), (.node (.litAtom) [])])
    (.node (.call "grow" 0 2) [(.node (.ctor "Union") [(.node (.mentionVar) []), (.node (.ctor "Wrap") [(.node (.mentionVar) []), (.node (.constAtom) [])])]), (.node (.litAtom) [])])
  = true := by simp [embedsB, zipAll]

end Zippy.WhistleTrace
