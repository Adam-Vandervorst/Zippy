package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==================================================================================================
 *  THE WHISTLE CORRESPONDENCE (plan.md 2E.3): the pairs `Matching.embeds` actually compared, re-decided
 *  by Lean.
 *
 *  `proofs/lean/Zippy/Whistle.lean` proves Kruskal's tree theorem for `Emb (· = ·)` on label trees and
 *  `embedsB_iff`: the executable `embedsB` IS that relation.  What connects the theorem to the SCALA
 *  whistle is `Matching.toLabel`: it renders a configuration as the label tree `embedsB` reads, and
 *  this suite records every pair the whistle compared during real supercompilation runs and writes
 *  them as `example`s that `lake build` re-decides.  A verdict Lean disagrees with is a build failure
 *  on a real pair — the same discipline as `SubstTrace`.
 *
 *  THE SEED is deliberate: the nested-`Iteration` antichain that made the OLD whistle (bound names
 *  compared by equality) NOT a well-quasi-order is driven here so the trace is guaranteed to contain
 *  the pair the alphabet change was for — `#s0` vs `#s1` inner mentions now couple, so the ancestor
 *  embeds and the whistle blows.
 *  ================================================================================================== */
class WhistleTrace extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def lit(ps: PathValue*): Space = Literal(SpaceValue(ps.toSet))

  test("the whistle's comparisons re-check against the Lean embedding") {
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map.empty)
    val entries = Matching.WhistleTrace.record(LeanRender.DefaultLimit) {
      // ---- THE SEED: the antichain of the old whistle -------------------------------------------
      val rest = SpaceMention("rest"); val y = PathRef("y")
      val a1 = Iteration(lit(p("s")), y, rest, Union(Mention(rest), lit(p("z"))))
      val a2 = Iteration(lit(p("s")), y, rest, Iteration(Mention(rest), PathRef("y2"), SpaceMention("r2"),
                 Union(Mention(SpaceMention("r2")), lit(p("z")))))
      assert(Matching.embeds(a1, a2), "the nested-iteration pair must embed under the label alphabet")
      assert(!Matching.embeds(a2, a1), "and not the other way round (the smaller does not contain the bigger)")
      // two different routines never couple; the same routine's residual name does
      val f = RoutinePtr("f"); val f7 = RoutinePtr("f_sc7"); val g = RoutinePtr("g")
      assert(Matching.embeds(Call(f, Vector.empty, Vector(lit(p("a")))), Call(f7, Vector.empty, Vector(Union(lit(p("a")), lit(p("b")))))))
      assert(!Matching.embeds(Call(f, Vector.empty, Vector(lit(p("a")))), Call(g, Vector.empty, Vector(lit(p("a"))))))
      // ---- REAL DRIVES: the supercompiler's whistle on recursive routines ----------------------
      val self = RoutinePtr("grow")
      val acc = SpaceMention("acc"); val e = SpaceMention("e")
      // `grow(acc, e) = acc ∪ grow(acc ∪ (e ▷ acc), e)` — a datalog-shaped self-call
      val growR = Routine(self, Vector.empty, Vector(acc, e),
        Union(Mention(acc), Call(self, Vector.empty, Vector(Union(Mention(acc), Composition(Mention(e), Mention(acc))), Mention(e)))))
      val defs: PartialFunction[RoutinePtr, Routine] = { case `self` => growR }
      val (res, st, _) = SC.run(Call(self, Vector.empty, Vector(lit(p("a")), lit(p("x", "y")))), defs,
                                SC.Config(compileBudgetMs = 5000.0))
      println(s"WHISTLE-TRACE: drive folds=${st.folds} whistles=${st.whistles} gen=${st.generalizations} " +
              s"fallbacks=${st.whistleFallbacks} escapes=${st.alphabetEscapes.size} converged=${st.converged}")
      assertEquals(st.alphabetEscapes.toVector, Vector.empty, "the drive minted a label outside its input alphabet")
      // a second shape: the nqueens-style acyclic call under an iteration, driven to a residual
      val h = RoutinePtr("step")
      val stepR = Routine(h, Vector(PathRef("q")), Vector(acc),
        Wrap(Iteration(Mention(acc), PathRef("v"), SpaceMention("r"), Union(Mention(SpaceMention("r")), Singleton(Path.Deref(PathRef("q"))))), Path.Deref(PathRef("q"))))
      val defs2: PartialFunction[RoutinePtr, Routine] = { case `h` => stepR }
      SC.run(Call(h, Vector(Path.Constant(p("k"))), Vector(lit(p("a", "b")))), defs2, SC.Config(compileBudgetMs = 5000.0))
    }
    val dropped = Matching.WhistleTrace.droppedCount
    val renderable = entries.count(_.renderable)
    println(s"WHISTLE-TRACE: ${entries.length} distinct pair(s) recorded, $renderable renderable, $dropped over the cap, " +
            s"${entries.count(_.verdict)} embedding")
    assert(entries.length >= 4, s"only ${entries.length} pairs recorded — the correspondence check would be near-vacuous")
    assert(entries.exists(_.verdict) && entries.exists(!_.verdict),
           "the trace must contain BOTH verdicts, or it checks only one direction of the equivalence")
    val text = LeanRender.renderWhistle(entries, dropped, "the seeded drives of `WhistleTrace`")
    val f = new java.io.File(Loaders.repoRoot, "proofs/lean/Zippy/WhistleTrace.lean")
    ArtifactSink.write(f, text)
    ArtifactSink.assertClean("morkl.WhistleTrace")
  }
end WhistleTrace
