package morkl

import morkl.Syntax.{*, given}
import java.nio.file.{Files, Paths}
import scala.util.Try

object ZipperLargeBenchmarks:
  import Space.*
  import Unification.MQT

  case class ProgramCase(name: String,
                         size: String,
                         expr: Space,
                         sc: SpaceContextMap,
                         tc: TrieSpaceContextMap,
                         zc: ZipperSpaceContextMap,
                         rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                         runs: Int = 3)

  case class Row(name: String,
                 size: String,
                 resultPaths: Int,
                 trieMs: Double,
                 zipperMs: Option[Double],
                 speedup: Option[Double],
                 note: String)

  private def ms[A](runs: Int)(f: => A): (A, Double) =
    var last: A = f
    for _ <- 0 until 1 do last = f
    val samples = Vector.tabulate(runs.max(1)) { _ =>
      val start = System.nanoTime()
      last = f
      (System.nanoTime() - start).toDouble / 1_000_000.0
    }.sorted
    last -> samples(samples.length / 2)

  private def context(values: (String, SpaceValue)*): (SpaceContextMap, TrieSpaceContextMap, ZipperSpaceContextMap) =
    val ref = SpaceContextMap(values.map((k, v) => SpaceMention(k) -> v).toMap)
    val trie = TrieSpaceContext.fromReference(ref)
    val zipper = ZipperSpaceContext.fromTrie(trie)
    (ref, trie, zipper)

  private def oneItemSpace(prefix: String, n: Int): SpaceValue =
    SpaceValue((0 until n).map(i => PathValue(List(PathItem(s"$prefix$i")))).toSet)

  private def chainGraph(n: Int): SpaceValue =
    SpaceValue((0 until n).flatMap { i =>
      Seq(Syntax.parse(s"edge.n$i.n${i + 1}")) ++
        Option.when(i + 2 <= n)(Syntax.parse(s"edge.n$i.n${i + 2}"))
    }.toSet)

  private def twoHopCase(n: Int): ProgramCase =
    val graph = chainGraph(n)
    val (sc, tc, zc) = context("g" -> graph)
    ProgramCase(
      "nonrecursive graph two-hop",
      s"$n nodes, ${graph.paths.size} edge facts",
      "TwoHop" x MQT(S"g"("edge"), List("$x.$y", "$y.$z"), "$x.$z"),
      sc,
      tc,
      zc,
      runs = 5,
    )

  private def syntheticFamily(generations: Int, width: Int): (SpaceValue, SpaceValue) =
    val facts = Set.newBuilder[PathValue]
    val people = Set.newBuilder[PathValue]
    for g <- 0 to generations; i <- 0 until width do
      val id = s"p${g}_$i"
      people += Syntax.parse(id)
      facts += Syntax.parse(s"person.$id")
      facts += Syntax.parse((if (g + i) % 2 == 0 then s"female.$id" else s"male.$id"))
    for g <- 0 until generations; i <- 0 until width do
      val child1 = s"p${g + 1}_${(2 * i) % width}"
      val child2 = s"p${g + 1}_${(2 * i + 1) % width}"
      facts += Syntax.parse(s"parent.p${g}_$i.$child1")
      facts += Syntax.parse(s"parent.p${g}_$i.$child2")
    SpaceValue(facts.result()) -> SpaceValue(people.result())

  private def productRestrictionCase(n: Int): ProgramCase =
    val a = oneItemSpace("a", n)
    val b = oneItemSpace("b", n)
    val prefix = SpaceValue(PathValue(List(PathItem(s"a${n / 2}"))))
    val (sc, tc, zc) = context("a" -> a, "b" -> b, "prefix" -> prefix)
    ProgramCase(
      "product restricted by one first-level prefix",
      s"$n x $n product, ${n} result paths",
      (S"a" x S"b") <| S"prefix",
      sc,
      tc,
      zc,
      runs = if n >= 2000 then 1 else 3
    )

  private def productExactIntersectionCase(n: Int): ProgramCase =
    val a = oneItemSpace("a", n)
    val b = oneItemSpace("b", n)
    val exact = SpaceValue(PathValue(List(PathItem(s"a${n / 2}"), PathItem(s"b${n / 2}"))))
    val (sc, tc, zc) = context("a" -> a, "b" -> b, "exact" -> exact)
    ProgramCase(
      "product intersected by one exact path",
      s"$n x $n product, 1 result path",
      (S"a" x S"b") /\ S"exact",
      sc,
      tc,
      zc,
      runs = if n >= 2000 then 1 else 3
    )

  private def auntSinglePersonCase(generations: Int, width: Int): ProgramCase =
    val (family, _) = syntheticFamily(generations, width)
    val target = SpaceValue(Syntax.parse(s"p${generations}_${width / 2}"))
    val (sc, tc, zc) = context("family" -> family, "people" -> target)
    ProgramCase(
      "aunt query over large generated family, one queried person",
      s"${generations + 1} generations x $width people (${family.paths.size} facts)",
      Routines.aunt_query_routine.name(S"family", S"people"),
      sc,
      tc,
      zc,
      rc = { case Routines.aunt_query_routine.name => Routines.aunt_query_routine },
      runs = 3
    )

  private def datalogCase(n: Int): ProgramCase =
    val edges = chainGraph(n)
    val semiNaive = DatalogExample.semiNaiveTransitive
    val (sc, tc, zc) = context("edges" -> edges)
    ProgramCase(
      "semi-naive datalog over generated chain graph",
      s"$n nodes, ${edges.paths.size} edge facts",
      semiNaive.name(DatalogExample.semiNaiveInitial(S"edges"))("complete.path"),
      sc,
      tc,
      zc,
      rc = { case semiNaive.name => semiNaive },
      runs = if n >= 80 then 1 else 2
    )

  private def sccCase: ProgramCase =
    val (sc, tc, zc) = context()
    ProgramCase(
      "SCC divide-and-conquer",
      s"${SccCornerstone.edges.paths.size} directed edges, ${SccCornerstone.expected.paths.size} representative/member pairs",
      SccCornerstone.body,
      sc,
      tc,
      zc,
      rc = SccCornerstone.rc,
      runs = 3,
    )

  private def cases(): Vector[ProgramCase] =
    Vector(
      twoHopCase(180),
      twoHopCase(360),
      twoHopCase(720),
      productExactIntersectionCase(2000),
      productExactIntersectionCase(10000),
      productExactIntersectionCase(30000),
      productRestrictionCase(2000),
      productRestrictionCase(10000),
      productRestrictionCase(30000),
      auntSinglePersonCase(generations = 8, width = 80),
      auntSinglePersonCase(generations = 10, width = 160),
      sccCase,
      datalogCase(40),
      datalogCase(80)
    )

  private def row(c: ProgramCase): Row =
    Console.err.println(s"[zipper-large] ${c.name} / ${c.size}")
    given PathContext = PathContext.emptyMap
    val trie = evalTrie(c.expr)(using summon[PathContext], c.tc, c.rc)
    val zipperAttempt = Try(evalZ(c.expr)(using summon[PathContext], c.zc, c.rc))
    zipperAttempt.foreach(zipper => assert(trie == zipper, s"${c.name}/${c.size} evalTrie/evalZ mismatch"))
    val (_, trieMs) = ms(c.runs)(evalTrie(c.expr)(using summon[PathContext], c.tc, c.rc).pathCount)
    val zipperMs = zipperAttempt.toOption.map(_ =>
      ms(c.runs)(evalZ(c.expr)(using summon[PathContext], c.zc, c.rc).pathCount)._2
    )
    val note =
      if c.name.startsWith("nonrecursive") then "generic iteration materializes branch tries natively at the final boundary"
      else if c.name.startsWith("product") then "large intermediate product should not be materialized by zipper traversal"
      else if c.name.startsWith("aunt") then "large query-shaped dataset with small queried person set"
      else if c.name.startsWith("SCC") then "paper pivot/partition recursion with masked reachability lowered to a native fixpoint"
      else zipperAttempt.failed.toOption
        .map(error => s"evalZ unsupported: ${Option(error.getMessage).getOrElse(error.getClass.getSimpleName)}")
        .getOrElse("recursive union-saturating routine lowered to lazy native-trie synchronous rounds")
    Row(c.name, c.size, trie.pathCount, trieMs, zipperMs, zipperMs.map(trieMs / _), note)

  def markdown(): String =
    val rows = cases().map(row)
    def optMs(value: Option[Double]): String = value.fold("unsupported")(v => f"$v%.3f")
    def optSpeed(value: Option[Double]): String = value.fold("n/a")(v => f"$v%.2f x")
    val body = rows.map { r =>
      f"| ${r.name} | ${r.size} | ${r.resultPaths}%,d | ${r.trieMs}%.3f | ${optMs(r.zipperMs)} | ${optSpeed(r.speedup)} | ${r.note} |"
    }.mkString("\n")
    Vector(
      "# Large Zipper Benchmarks",
      "",
      "These rows are intentionally larger and more asymptotic than the mixed publication table. They compare direct `evalTrie` against direct `evalZ` after checking both produce the same `TrieSpace` result. Times are medians after two warmup evaluations. The nonrecursive two-hop rows expose generic-iteration scaling; the product rows stress selective traversal, where the source expression denotes an `n x n` product but the consumer asks for one prefix or one exact path.",
      "",
      "| benchmark | size | result paths | evalTrie ms | evalZ ms | evalTrie / evalZ | note |",
      "|---|---:|---:|---:|---:|---:|---|",
      body,
      "",
      "A ratio above `1.00 x` means the zipper evaluator is faster. Recursive Datalog is included as a large generated control case and is timed through direct `evalZ` lowering; its state-negative delta subtraction selects lazy exact synchronous rounds executed directly in native trie algebra, while structurally positive, productive recursive steps use prefix-demand cells. An unsupported cell is reserved for a genuine lowering failure."
    ).mkString("\n")

@main def zipperLargeBenchmarkReport(): Unit =
  val report = ZipperLargeBenchmarks.markdown()
  Files.writeString(Paths.get("docs/ZIPPER_LARGE_BENCHMARKS.md"), report + "\n")
  println(report)
