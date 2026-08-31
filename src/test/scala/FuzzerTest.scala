package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}

/** Demonstrates the space/expression fuzzer: it samples dependent (program, argument, result) triples
 *  — the argument space is drawn first, the program is drawn OVER it, and the result is the program
 *  evaluated on it.  Every sampled triple is differentially validated (eval == evalI == evalT ==
 *  execT-on-the-optimized-graph), which doubles as a randomized soundness test of the whole stack. */
class FuzzerDemo extends FunSuite:
  import Space.*

  /** check the reference Set `eval` result agrees with all the other evaluators / the compiled graph */
  def crossCheck(ex: SpaceFuzzer.Example, i: Int): Unit =
    val ref = ex.result
    assertEquals(evalI(ex.program)(using PathContextMap(Map.empty), Map(SpaceFuzzer.argM -> ITrie.fromSpaceValue(ex.arg)), PartialFunction.empty).toSpaceValue, ref, s"evalI #$i: ${ex.program.show}")
    assertEquals(evalT(ex.program)(using tc = Map(SpaceFuzzer.argM -> Trie.fromSpaceValue(ex.arg))).toSpaceValue, ref, s"evalT #$i: ${ex.program.show}")
    val main = Routine(RoutinePtr("main"), Vector.empty, Vector(SpaceFuzzer.argM), ex.program)
    val g = optimize(transpile(main))
    assertEquals(runGraphT(g, mentions = Map("x" -> ITrie.fromSpaceValue(ex.arg))).toSpaceValue, ref, s"execT(opt) #$i: ${ex.program.show}")

  def fmt(sv: SpaceValue): String = sv.paths.map(p => if p.items.isEmpty then "ε" else p.show).toSeq.sorted.mkString("{", ", ", "}")
  def show1(s: Space): String = s.show.replaceAll("\\s+", " ").trim   // Iteration.show is multi-line; collapse it

  test("space fuzzer: 10 large dependent (program, argument, result) examples") {
    val rng = new java.util.Random(20260625L)
    val examples = LazyList.continually(SpaceFuzzer.example(maxDepth = 6).sample(using rng))
      .filter(ex => nodes(ex.program) >= 12).distinctBy(_.program.show).take(10).toVector
    for (ex, i) <- examples.zipWithIndex do
      crossCheck(ex, i)
      println(s"\n=== example ${i + 1}  (program nodes=${nodes(ex.program)}) ===")
      println(s"  program : ${show1(ex.program)}")
      println(s"  argument: ${fmt(ex.arg)}")
      println(s"  result  : ${fmt(ex.result)}")
    assertEquals(examples.size, 10)
  }

  /** rough size of a program expression — ONE OWNER (SpatialPipeline.nodeCount, over the total
   *  SizeZ3.children), shared with ProgramStats / ProgramExpressivity / CorpusRuntimes. */
  def nodes(s: Space): Int = SpatialPipeline.nodeCount(s)

  test("space fuzzer: 200 random triples are sound across all evaluators".tag(SlowTag.Slow)) {
    val rng = new java.util.Random(1L)
    for i <- 0 until 200 do crossCheck(SpaceFuzzer.example(maxDepth = 5).sample(using rng), i)
  }
end FuzzerDemo
