/-
==================================================================================================
GENERATED — the correspondence trace (plan.md 1E.2).  DO NOT EDIT.

Regenerate with `ZIPPY_REGENERATE=1 sbt --server 'testOnly morkl.SubstTrace'`; without the flag the suite
writes to `target/artifact-scratch` and DIFFS against this file, so a drift in EITHER
implementation fails.  `src/main/scala/LeanRender.scala` is the emitter and explains the design.

WHAT THIS FILE IS.  Each `example` below is a substitution `src/main/scala/Subst.scala` ACTUALLY
PERFORMED while running the seeded production passes of `SubstTrace`, re-checked against `Zippy.substS` — the Lean definition
`Zippy/Subst.lean` proves its hygiene theorems about.  A disagreement between the two
implementations is a failing `lake build` on a real term, not a comment claiming they agree.

It is also what DISCHARGES the one deliberate difference between them: at a capturing binder the
Scala does two passes over the body (rename, then substitute) and the Lean merges the rename into
the map and does one.  `Zippy/Subst.lean`'s header states that as an obligation for this file.

  triples recorded          9
  emitted as EQUATIONS      9   (class A: no fresh name minted, so the result is
                                 independent of the naming policy and equality is checkable)
  emitted as COMMENTS       0   (class B: a capture WAS avoided; the Scala's naming is
                                 a stateful counter and no Lean `FreshSupply` reproduces it, so
                                 equality is not asserted.  `SubstCapture` and `substS_keeps_freeM`
                                 are what cover this class instead)
  dropped, grounded         0   (a `Grounded*` closure's Lean identity is not
                                 reproducible across runs, so the artifact would not be a golden file)
  dropped, over the cap     0   (LeanRender.DefaultLimit; repeats of one triple are
                                 deduplicated before the cap applies)
==================================================================================================
-/
import Zippy.Subst

namespace Zippy.Trace

/-- the supply the equations below are checked under.  Class-A triples mint no name, so `gen` is
never called and the choice cannot matter — which is exactly what makes the class checkable. -/
private def F : FreshSupply := FreshSupply.byLength

/-- triple 1 -/
example : substS F
    [("a", (.mention "b")), ("b", (.mention "a"))]
    []
    (.union (.mention "a") (.wrap (.mention "b") (.const ["k"])))
  = (.union (.mention "b") (.wrap (.mention "a") (.const ["k"]))) := by rfl

/-- triple 2 -/
example : substS F
    [("rest", (.lit [["R"]]))]
    []
    (.union (.mention "rest") (.iteration (.lit [["s"]]) "y" "rest" (.mention "rest")))
  = (.union (.lit [["R"]]) (.iteration (.lit [["s"]]) "y" "rest" (.mention "rest"))) := by rfl

/-- triple 3 -/
example : substS F
    [("a", (.lit [["A"]]))]
    [("r", (.const ["k"]))]
    (.fixpoint (.singleton (.deref "r")) "rec" (.union (.mention "rec") (.mention "a")))
  = (.fixpoint (.singleton (.const ["k"])) "rec" (.union (.mention "rec") (.lit [["A"]]))) := by rfl

/-- triple 4 -/
example : substS F
    [("a", (.lit [["X"]])), ("b", (.lit [["Y"]]))]
    [("q", (.const ["k"]))]
    (.union (.wrap (.mention "a") (.deref "q")) (.mention "b"))
  = (.union (.wrap (.lit [["X"]]) (.const ["k"])) (.lit [["Y"]])) := by rfl

/-- triple 5 -/
example : substS F
    [("a", (.mention "b")), ("b", (.mention "a"))]
    [("q", (.const ["k"]))]
    (.union (.wrap (.mention "a") (.deref "q")) (.mention "b"))
  = (.union (.wrap (.mention "b") (.const ["k"])) (.mention "a")) := by rfl

/-- triple 6 -/
example : substS F
    [("rest", (.mention "#s1"))]
    [("y", (.deref "#p0"))]
    (.iteration (.mention "rest") "y2" "r2" (.union (.mention "r2") (.mention "rest")))
  = (.iteration (.mention "#s1") "y2" "r2" (.union (.mention "r2") (.mention "#s1"))) := by rfl

/-- triple 7 -/
example : substS F
    [("r2", (.mention "#s3"))]
    [("y2", (.deref "#p2"))]
    (.union (.mention "r2") (.mention "#s1"))
  = (.union (.mention "#s3") (.mention "#s1")) := by rfl

/-- triple 8 -/
example : substS F
    [("rest", (.mention "#s2"))]
    [("acc", (.deref "#p0")), ("sym", (.deref "#p1"))]
    (.mention "rest")
  = (.mention "#s2") := by rfl

/-- triple 9 -/
example : substS F
    [("rest", (.mention "#s2"))]
    [("acc", (.deref "#p0")), ("sym", (.deref "#p1"))]
    (.singleton (.concat (.deref "acc") (.deref "sym")))
  = (.singleton (.concat (.deref "#p0") (.deref "#p1"))) := by rfl

end Zippy.Trace
