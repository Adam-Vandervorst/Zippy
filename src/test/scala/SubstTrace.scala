package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==================================================================================================
 *  THE CORRESPONDENCE BETWEEN THE TWO SUBSTITUTIONS, AS A TRACE.
 *
 *  `1E.2` asks for correspondence to the executable — "a Lean-checked TRACE of the production
 *  substitutions ... Not a citation."  This suite is the producer: it runs real programs through the
 *  passes that substitute, records every distinct `(term, σ, result)` the Scala performed, and emits
 *  them as `proofs/lean/Zippy/Trace.lean`.
 *
 *  ==WHERE THE CHECK ACTUALLY HAPPENS, WHICH IS NOT HERE==
 *  This suite writes the artifact.  `lake build` ELABORATES it, and every `example` in it is an
 *  equation between the Scala's recorded result and what Lean's `substS` computes on the same input.
 *  So a disagreement between the two implementations is a failing Lean build — and because the file
 *  goes through `ArtifactSink`, a drift on the SCALA side is a failing artifact diff here.  Two
 *  independent failure modes, one for each side:
 *
 *    Scala changed, Lean unchanged  ->  this suite fails (the committed artifact no longer matches)
 *    Lean changed, Scala unchanged  ->  `scripts/check_lean.sh` fails (an `example` stops elaborating)
 *
 *  ==WHAT IS TRACED==
 *  The passes that substitute, on the cornerstone programs: `AgnosticPipeline.unrollControl` (which
 *  is `Lower.inline`, the `g(y,x)` site), `SC.reduce` (which drives the optimiser's
 *  `IterateLiteral_Union` / `IterateSingleton_Deref` rules and `asFixpointGeneral`), and
 *  `Matching.canon` through the supercompiler.  Those are the four production call sites `Subst.scala`
 *  lists, so the trace is over the paths that actually run rather than over hand-written terms.
 *
 *  A HAND-WRITTEN SEED IS ADDED DELIBERATELY, and it is not padding: the `g(y,x)` shape and one
 *  shadowing shape are included so the trace is guaranteed to contain the two cases the whole
 *  exercise is about even if a future optimiser change stops the cornerstones from producing them.
 *  Without that, "0 triples of the interesting kind" would look like a pass.
 *  ================================================================================================== */
class SubstTrace extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def lit(ps: PathValue*): Space = Literal(SpaceValue(ps.toSet))
  val K: Path = Path.Constant(p("k"))

  test("the production substitutions re-check against the Lean definition") {
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map.empty)

    val entries = Subst.Trace.record(LeanRender.DefaultLimit) {
      // ---- THE SEED: the two shapes this exercise exists for, so the trace cannot be vacuous ----
      val a = SpaceMention("a"); val b = SpaceMention("b")
      // `g(y,x)`: a routine called with its own formals swapped — simultaneous vs sequential
      Subst(Union(Mention(a), Wrap(Mention(b), K)), Map(a -> Mention(b), b -> Mention(a)))
      // shadowing: the free occurrence is substituted, the bound one is not
      Subst.mention(Union(Mention(SpaceMention("rest")),
                          Iteration(lit(p("s")), PathRef("y"), SpaceMention("rest"),
                                    Mention(SpaceMention("rest")))),
                    SpaceMention("rest"), lit(p("R")))
      // both sorts at once, and a path ref under a binder that does NOT bind it
      Subst(Fixpoint(Singleton(Path.Deref(PathRef("r"))), SpaceMention("rec"),
                     Union(Mention(SpaceMention("rec")), Mention(a))),
            Map(a -> lit(p("A"))), Map(PathRef("r") -> K))

      // ---- THE PRODUCTION PASSES, on real programs -------------------------------------------
      // `unrollControl` is `Lower.inline`: one simultaneous substitution per inlined call.
      val g = RoutinePtr("g")
      val routine = Routine(g, Vector(PathRef("q")), Vector(a, b),
                            Union(Wrap(Mention(a), Path.Deref(PathRef("q"))), Mention(b)))
      val rc: PartialFunction[RoutinePtr, Routine] = { case `g` => routine }
      AgnosticPipeline.unrollControl(
        Call(g, Vector(K), Vector(lit(p("X")), lit(p("Y")))), 2)(using rc)
      AgnosticPipeline.unrollControl(
        Union(Call(g, Vector(K), Vector(Mention(b), Mention(a))), lit(p("Z"))), 2)(using rc)

      // `SC.reduce` drives the optimiser rules that substitute an Iteration's binders.
      for prog <- Vector(
            Iteration(lit(p("h", "t1"), p("h", "t2"), p("g", "t3")), PathRef("y"),
                      SpaceMention("rest"),
                      Union(Mention(SpaceMention("rest")), Singleton(Path.Deref(PathRef("y"))))),
            Iteration(Singleton(Path.Constant(p("a", "b", "c"))), PathRef("y"),
                      SpaceMention("rest"), TailsUnion(Mention(SpaceMention("rest")))),
            Fixpoint(lit(p("a")), SpaceMention("rec"),
                     Union(Mention(SpaceMention("rec")), lit(p("b"))))) do
        SC.reduce(prog)

      // `Matching.canon` renames every binder through `Subst`, so the supercompiler's own
      // canonicalisation is traced too.
      for prog <- Vector(
            Iteration(lit(p("a")), PathRef("y"), SpaceMention("rest"),
                      Iteration(Mention(SpaceMention("rest")), PathRef("y2"), SpaceMention("r2"),
                                Union(Mention(SpaceMention("r2")), Mention(SpaceMention("rest"))))),
            Fold(lit(p("a"), p("b")), K, PathRef("acc"), PathRef("sym"), SpaceMention("rest"),
                 Mention(SpaceMention("rest")),
                 Path.Concat(Path.Deref(PathRef("acc")), Path.Deref(PathRef("sym"))))) do
        Matching.canon(prog)
    }

    val dropped = Subst.Trace.droppedCount
    val classA = entries.count(_.exactlyCheckable)
    val classB = entries.length - classA
    println(s"SUBST-TRACE: ${entries.length} distinct triple(s) recorded, $classA class A, " +
            s"$classB class B, $dropped over the cap")

    // A TRACE THAT RECORDED NOTHING IS NOT A PASS.  The whole check is downstream in `lake build`,
    // so an empty artifact would elaborate green and mean nothing.
    assert(entries.length >= 8,
      s"only ${entries.length} triples recorded — the correspondence check would be near-vacuous.  " +
      "Either the passes stopped substituting or `Subst.Trace` stopped recording.")
    assert(classA >= 6,
      s"only $classA class-A triples: those are the ones Lean checks by EQUALITY, and they are the " +
      "whole strength of this artifact.  Class B is recorded but not asserted (see LeanRender).")

    val text = LeanRender.render(entries, dropped, "the seeded production passes of `SubstTrace`")
    val f = new java.io.File(Loaders.repoRoot, "proofs/lean/Zippy/Trace.lean")
    ArtifactSink.write(f, text)
    ArtifactSink.assertClean("morkl.SubstTrace")
  }
end SubstTrace
