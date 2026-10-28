package morkl

import morkl.Syntax.{*, given}
import scala.language.implicitConversions
import java.util.Locale
import java.nio.file.{Files, Paths}
import scala.util.Try

object TrieBenchmarks:
  import Space.*
  import Unification.MQT

  case class ProgramCase(
    name: String,
    variant: String,
    expr: Space,
    sc: SpaceContextMap = SpaceContextMap(Map.empty),
    tc: TrieSpaceContextMap = TrieSpaceContext.emptyMap,
    rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
    defs: Vector[Routine] = Vector.empty,
    runs: Int = 5,
    prep: Option[CompileProfile] = None,
    zipperNote: Option[String] = None
  )

  case class CompileProfile(totalMs: Double,
                            sourcePassMs: Double,
                            lowerInlineMs: Double,
                            graphOptimizeMs: Double,
                            constantFoldEvalMs: Double,
                            constantFoldEvalTrieMs: Double,
                            constantFoldEvalZMs: Double,
                            constantFoldExecTMs: Double,
                            constantFoldEvalCalls: Int,
                            constantFoldEvalTrieCalls: Int,
                            constantFoldEvalZCalls: Int,
                            constantFoldExecTCalls: Int,
                            graphTranspileMs: Double,
                            sourcePasses: Int,
                            graphPasses: Int,
                            budgetMs: Long,
                            note: String)

  object CompileProfile:
    def fromCompile(report: SupercompileReport, note: String): CompileProfile =
      CompileProfile(
        report.compileMs,
        report.sourceOptimizeMs,
        report.loweringMs + report.inlineMs,
        report.graphOptimizeMs,
        report.constantFoldEvalMs,
        report.constantFoldEvalTrieMs,
        report.constantFoldEvalZMs,
        report.constantFoldExecTMs,
        report.constantFoldEvalCalls,
        report.constantFoldEvalTrieCalls,
        report.constantFoldEvalZCalls,
        report.constantFoldExecTCalls,
        report.graphTranspileMs,
        report.sourceTimings.size,
        report.graphTimings.size,
        report.maxCompileMillis,
        note
      )

    def fromReports(reports: Vector[SupercompileReport], totalMs: Double, note: String): CompileProfile =
      CompileProfile(
        totalMs,
        reports.map(_.sourceOptimizeMs).sum,
        reports.map(r => r.loweringMs + r.inlineMs).sum,
        reports.map(_.graphOptimizeMs).sum,
        reports.map(_.constantFoldEvalMs).sum,
        reports.map(_.constantFoldEvalTrieMs).sum,
        reports.map(_.constantFoldEvalZMs).sum,
        reports.map(_.constantFoldExecTMs).sum,
        reports.map(_.constantFoldEvalCalls).sum,
        reports.map(_.constantFoldEvalTrieCalls).sum,
        reports.map(_.constantFoldEvalZCalls).sum,
        reports.map(_.constantFoldExecTCalls).sum,
        reports.map(_.graphTranspileMs).sum,
        reports.map(_.sourceTimings.size).sum,
        reports.map(_.graphTimings.size).sum,
        reports.map(_.maxCompileMillis).sum,
        note
      )

    def fromSC(report: SCReport, note: String): CompileProfile =
      CompileProfile(report.elapsedMs, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0, 0, 0, 0, 0.0, 0, 0, report.maxMillis, note)

  case class GraphPlan(
    top: RecursiveOpGraph,
    index: Map[String, RecursiveOpGraph],
    mentions: Vector[SpaceMention],
    stats: GraphStats,
    compileProfile: CompileProfile,
    compiledAway: Boolean
  )

  private case class CallIndex(index: Map[String, RecursiveOpGraph], reports: Vector[SupercompileReport])

  case class Row(
    name: String,
    variant: String,
    paths: Int,
    refMs: Double,
    graphMs: Option[Double],
    trieMs: Double,
    zipperMs: Option[Double],
    execTMs: Option[Double],
    graphNodes: Option[Int],
    compiledAway: Boolean,
    graphNote: Option[String],
    prep: Option[CompileProfile],
    graphCompile: Option[CompileProfile]
  ):
    def trieSpeedup: Double = refMs / trieMs
    def zipperSpeedup: Option[Double] = zipperMs.map(refMs / _)
    def zipperOverTrie: Option[Double] = zipperMs.map(trieMs / _)
    def graphSpeedup: Option[Double] = Option.when(!compiledAway)(graphMs).flatten.map(refMs / _)
    def execTSpeedup: Option[Double] = Option.when(!compiledAway)(execTMs).flatten.map(refMs / _)
    def execTOverTrie: Option[Double] = Option.when(!compiledAway)(execTMs).flatten.map(trieMs / _)
    def totalCompileMs: Option[Double] =
      val total = Vector(prep, graphCompile).flatten.map(_.totalMs).sum
      Option.when(total > 0.0)(total)
    def compileRunRatio: Option[Double] =
      Option.when(!compiledAway) {
        for
          compile <- totalCompileMs
          run <- execTMs
          if run > 0.0
        yield compile / run
      }.flatten
    def compilePlusExecTMs: Option[Double] =
      for
        compile <- totalCompileMs
        run <- execTMs
      yield compile + run

  private def ms[A](runs: Int)(f: => A): (A, Double) =
    var last: A = f
    for _ <- 0 until 2 do last = f
    val start = System.nanoTime()
    for _ <- 0 until runs do last = f
    val elapsed = (System.nanoTime() - start).toDouble / 1_000_000.0 / runs.max(1)
    last -> elapsed

  private def row(c: ProgramCase): Row =
    Console.err.println(s"[bench] ${c.name} / ${c.variant}")
    given PathContext = PathContext.emptyMap
    val ref = eval(c.expr)(using summon[PathContext], c.sc, c.rc)
    val trie = evalTrieValue(c.expr)(using summon[PathContext], c.tc, c.rc)
    assert(ref == trie, s"${c.name}/${c.variant} trie evaluator mismatch")
    val zctx = ZipperSpaceContext.fromTrie(c.tc)
    val zipperMs =
      if c.zipperNote.isEmpty then
        val zipper = evalZValue(c.expr)(using summon[PathContext], zctx, c.rc)
        assert(ref == zipper, s"${c.name}/${c.variant} zipper evaluator mismatch")
        Some(ms(c.runs)(evalZ(c.expr)(using summon[PathContext], zctx, c.rc).pathCount)._2)
      else None
    val graph = graphPlan(c)
    graph.foreach { plan =>
      val got = execGraphValue(plan, c)
      assert(ref == got, s"${c.name}/${c.variant} RecursiveOpGraph exec mismatch")
      val gotTrie = execTGraphValue(plan, c).toSpaceValue
      assert(ref == gotTrie, s"${c.name}/${c.variant} RecursiveOpGraph trie exec mismatch")
    }
    val (_, refMs) = ms(c.runs)(eval(c.expr)(using summon[PathContext], c.sc, c.rc).paths.size)
    val (_, trieMs) = ms(c.runs)(evalTrie(c.expr)(using summon[PathContext], c.tc, c.rc).pathCount)
    val graphMs = graph.map(plan => ms(c.runs)(execGraphValue(plan, c).paths.size)._2)
    val execTMs = graph.map(plan => ms(c.runs)(execTGraphValue(plan, c).pathCount)._2)
    val graphNote =
      graph match
        case Some(plan) if plan.compiledAway => Some("compiled away; use compile+run")
        case Some(plan) => fallbackCallNote(plan.top, plan.index)
        case None => graphBuildError(c)
    val note = Vector(graphNote, c.zipperNote).flatten.distinct.mkString("; ") match
      case "" => None
      case text => Some(text)
    Row(
      c.name,
      c.variant,
      ref.paths.size,
      refMs,
      graphMs,
      trieMs,
      zipperMs,
      execTMs,
      graph.map(_.stats.nodes),
      graph.exists(_.compiledAway),
      note,
      c.prep,
      graph.map(_.compileProfile)
    )

  private def wrapperName(c: ProgramCase): RoutinePtr =
    RoutinePtr("bench_" + (c.name + "_" + c.variant).replaceAll("[^A-Za-z0-9]+", "_"))

  private def graphMentions(c: ProgramCase): Vector[SpaceMention] =
    c.sc.m.keys.toVector.sortBy(_.s)

  private def graphOps(g: RecursiveOpGraph): Vector[String] =
    g.root.operation +: g.nodes.toVector.flatMap {
      case Left(n) => Vector(n.operation)
      case Right(sg) => graphOps(sg)
    }

  private def graphCalls(g: RecursiveOpGraph): Set[String] =
    val own = g.nodes.toVector.flatMap {
      case Left(Node("Call", constant, _, _)) => Vector(constant)
      case Left(_) => Vector.empty
      case Right(sg) => graphCalls(sg).toVector
    }.toSet
    if g.root.operation == "Call" then own + g.root.constant else own

  private def fallbackCallNote(top: RecursiveOpGraph, index: Map[String, RecursiveOpGraph]): Option[String] =
    val calls = (graphCalls(top) ++ index.valuesIterator.flatMap(g => graphCalls(g))).toVector.sorted
    Option.when(calls.nonEmpty)(
      s"exec fallback Call dispatch to optimized callee graph(s): ${calls.mkString(", ")}"
    )

  private[morkl] def fallbackCallNoteForTest(top: RecursiveOpGraph, index: Map[String, RecursiveOpGraph]): Option[String] =
    fallbackCallNote(top, index)

  private def graphCompiledAway(g: RecursiveOpGraph): Boolean =
    g.nodes.length == 1 && g.nodes.headOption.exists {
      case Left(Node(op, _, "space", inputs)) => inputs.isEmpty && (op == "Literal" || op == "Empty")
      case _ => false
    }

  private def graphPlan(c: ProgramCase): Option[GraphPlan] =
    val mentions = graphMentions(c)
    val wrapper = Routine(wrapperName(c), Vector.empty, mentions, c.expr)
    Try {
      val started = System.nanoTime()
      val defs = c.defs.map(r => r.name -> r).toMap
      val compiled = Supercompiler.compile(wrapper, ctx = defs.lift.unlift)
      val top = compiled.graph.getOrElse(throw RuntimeException("compile did not produce a graph"))
      val callIndex = compileCallIndex(top, defs)
      val elapsed = (System.nanoTime() - started).toDouble / 1_000_000.0
      val profile = CompileProfile.fromReports(compiled.report +: callIndex.reports, elapsed, "graph compile + optimized callees")
      GraphPlan(top, callIndex.index, mentions, Supercompiler.graphStats(top), profile, graphCompiledAway(top))
    }.toOption

  private def graphBuildError(c: ProgramCase): Option[String] =
    val unsupported = Supercompiler.backendUnsupported(c.expr) ++ c.defs.flatMap(r => Supercompiler.backendUnsupported(r.body))
    if unsupported.nonEmpty then Some(unsupported.distinct.sorted.mkString(", "))
    else
      val mentions = graphMentions(c)
      val wrapper = Routine(wrapperName(c), Vector.empty, mentions, c.expr)
      val defs = c.defs.map(r => r.name -> r).toMap
      Try(Supercompiler.compile(wrapper, ctx = defs.lift.unlift)).toOption match
        case Some(compiled) if compiled.graph.exists(g => Try(compileCallIndex(g, defs)).isFailure) => Some("Call not inlined/lowered")
        case Some(compiled) if compiled.report.backendUnsupported.nonEmpty => Some(compiled.report.backendUnsupported.distinct.sorted.mkString(", "))
        case Some(compiled) if compiled.report.graphError.nonEmpty => compiled.report.graphError
        case _ => Some("graph build failed")

  private def compileCallIndex(top: RecursiveOpGraph, defs: Map[RoutinePtr, Routine]): CallIndex =
    val byName = defs.map((rp, r) => rp.s -> r)
    val compiled = collection.mutable.Map.empty[String, RecursiveOpGraph]
    val reports = Vector.newBuilder[SupercompileReport]
    val worklist = collection.mutable.Queue.from(graphCalls(top).filter(byName.contains))
    while worklist.nonEmpty do
      val name = worklist.dequeue()
      if !compiled.contains(name) then
        val callee = Supercompiler.compile(byName(name), ctx = defs.lift.unlift)
        reports += callee.report
        val graph = callee.graph.getOrElse(throw RuntimeException(s"callee $name did not produce a graph"))
        compiled(name) = graph
        worklist.enqueueAll(graphCalls(graph).filter(byName.contains).filterNot(compiled.contains))
    val reachableCalls = graphCalls(top) ++ compiled.valuesIterator.flatMap(graphCalls)
    val missing = reachableCalls.filterNot(compiled.contains)
    if missing.nonEmpty then
      throw RuntimeException(s"missing callee graph(s): ${missing.toSeq.sorted.mkString(", ")}")
    val callGraph = compiled.view.mapValues(g => graphCalls(g).filter(compiled.contains)).toMap
    def cyclic(name: String, visiting: Set[String], visited: Set[String]): Boolean =
      if visiting(name) then true
      else if visited(name) then false
      else callGraph.getOrElse(name, Set.empty).exists(cyclic(_, visiting + name, visited + name))
    val recursive = compiled.keysIterator.filter(cyclic(_, Set.empty, Set.empty)).toVector.sorted
    val unsafe = recursive.filterNot(name =>
      Supercompiler.wellFoundedPartitionRecursion(byName(name), defs.lift.unlift)
    )
    if unsafe.nonEmpty then
      throw RuntimeException(s"recursive Call not lowered or certified well-founded: ${unsafe.mkString(", ")}")
    CallIndex(compiled.toMap, reports.result())

  private def execGraphValue(plan: GraphPlan, c: ProgramCase): SpaceValue =
    val stack = collection.mutable.Stack(new Array[PathValue | SpaceValue | Null](plan.top.nodes.length))
    for (sm, i) <- plan.mentions.zipWithIndex do
      stack.top(i) = c.sc.resolve(sm)
    exec(plan.top, stack, plan.index)
    stack.top.last.asInstanceOf[SpaceValue]

  private def execTGraphValue(plan: GraphPlan, c: ProgramCase): TrieSpace =
    val stack = collection.mutable.Stack(new Array[List[Int] | TrieSpace | Null](plan.top.nodes.length))
    for (sm, i) <- plan.mentions.zipWithIndex do
      stack.top(i) = c.tc.resolve(sm)
    execT(plan.top, stack, plan.index)
    stack.top.last.asInstanceOf[TrieSpace]

  private def chainGraph(n: Int): SpaceValue =
    SpaceValue((0 until n).flatMap(i =>
      Seq(Syntax.parse(s"edge.n$i.n${i + 1}")) ++
        Option.when(i + 2 <= n)(Syntax.parse(s"edge.n$i.n${i + 2}"))
    ).toSet)

  private def syntheticFamily(generations: Int, width: Int): (SpaceValue, SpaceValue) =
    val facts = Set.newBuilder[PathValue]
    val people = Set.newBuilder[PathValue]
    for g <- 0 to generations; i <- 0 until width do
      val id = s"p${g}_$i"
      people += Syntax.parse(id)
      facts += Syntax.parse(s"person.$id")
      facts += Syntax.parse(if i % 2 == 0 then s"female.$id" else s"male.$id")
    for g <- 0 until generations; i <- 0 until width do
      val parentA = s"p${g}_$i"
      val parentB = s"p${g}_${(i + 1) % width}"
      val child = s"p${g + 1}_$i"
      facts += Syntax.parse(s"parent.$parentA.$child")
      facts += Syntax.parse(s"child.$child.$parentA")
      facts += Syntax.parse(s"parent.$parentB.$child")
      facts += Syntax.parse(s"child.$child.$parentB")
    SpaceValue(facts.result()) -> SpaceValue(people.result())

  private def lifeField(width: Int, height: Int, count: Int, seed: Long): SpaceValue =
    GoalExampleData.randomLife(width, height, count, seed)

  private def noaaSynthetic(width: Int, height: Int): SpaceValue =
    val latBits = 6
    val lonBits = 9
    val rows = for
      lat <- 0 until height
      lon <- 0 until width
      bucket = (lat * 7 + lon * 3) & 31
      label = if bucket < 12 then "C" else if bucket > 19 then "H" else "M"
      bits = TemperatureExample.bits(lat, latBits) ++ TemperatureExample.bits(lon, lonBits) ++ TemperatureExample.bits(bucket, 5)
    yield Syntax.parse((Vector("cell") ++ bits :+ label).mkString("."))
    SpaceValue(rows.toSet)

  private def puzzleNeighbors(n: Int, state: Vector[Int]): Set[Vector[Int]] =
    val blank = state.indexOf(0)
    val row = blank / n
    val col = blank % n
    Vector(row - 1 -> col, row + 1 -> col, row -> (col - 1), row -> (col + 1))
      .filter((r, c) => r >= 0 && c >= 0 && r < n && c < n)
      .map((r, c) =>
        val j = r * n + c
        state.updated(blank, state(j)).updated(j, 0)
      ).toSet

  private def puzzleReachable(n: Int, maxDepth: Int): SpaceValue =
    val start = (0 until n * n).toVector
    var seen = Set(start)
    var frontier = Set(start)
    var depth = 0
    while frontier.nonEmpty && depth < maxDepth do
      val next = frontier.flatMap(puzzleNeighbors(n, _)) -- seen
      seen ++= next
      frontier = next
      depth += 1
    SpaceValue(seen.map(xs => SlidingPuzzleExample.pathState(n, xs)))

  private def nQueensBitCount(n: Int): Int =
    def loop(row: Int, cols: Int, diagA: Int, diagB: Int): Int =
      if row == n then 1
      else
        val all = (1 << n) - 1
        var free = all & ~(cols | diagA | diagB)
        var total = 0
        while free != 0 do
          val bit = free & -free
          free -= bit
          total += loop(row + 1, cols | bit, ((diagA | bit) << 1) & all, (diagB | bit) >> 1)
        total
    loop(0, 0, 0, 0)

  private def bitQueenRows(): Vector[String] =
    (8 to 12).toVector.map { n =>
      val (count, time) = ms(1)(nQueensBitCount(n))
      f"| n-queens bit reference | n=$n | $count | $time%.3f | independent reference, not MORKL eval |"
    }

  case class ConstantFoldExecutorRow(benchmark: String,
                                     backend: ConstantFoldEval.Backend,
                                     profile: CompileProfile):
    def foldMs: Double =
      profile.constantFoldEvalMs +
        profile.constantFoldEvalTrieMs +
        profile.constantFoldEvalZMs +
        profile.constantFoldExecTMs
    def calls: Int =
      profile.constantFoldEvalCalls +
        profile.constantFoldEvalTrieCalls +
        profile.constantFoldEvalZCalls +
        profile.constantFoldExecTCalls

  private def focusedConstantFoldRows(backend: ConstantFoldEval.Backend): Vector[ConstantFoldExecutorRow] =
    ConstantFoldEval.withBackend(backend) {
      Console.err.println(s"[constant-fold] backend ${backend.toString}")

      val lifeInitial = lifeField(24, 24, 120, 2406)
      val lifeCompiledIn = Supercompiler.specialize(
        LifeExample.nextStep,
        spaceArgs = Map(SpaceMention("field") -> Literal(lifeInitial)),
        ctx = mod(LifeExample.neigh)
      )

      val puzzle3 = Literal(puzzleReachable(3, 8))
      val slide3 = SlidingPuzzleExample.step(3, puzzle3)
      val slide3Compiled = Supercompiler.compile(
        R"slide3"() := slide3,
        ctx = SlidingPuzzleExample.context(3),
        buildGraph = false
      )

      val (queens8, queens8Ctx) = NQueensExample.program(8)
      val queens8Defs = NQueensExample.routines(8).filterNot(_.name == queens8.name)
      val queensSourceCase = ProgramCase(
        "n-queens",
        "MORKL 8x8 source",
        queens8.body,
        tc = TrieSpaceContext.emptyMap,
        rc = queens8Ctx,
        defs = queens8Defs,
        runs = 1
      )
      val queensSourceProfile = graphPlan(queensSourceCase).get.compileProfile
      val queens8Compiled = Supercompiler.compile(queens8, ctx = queens8Ctx, buildGraph = false)

      Vector(
        ConstantFoldExecutorRow(
          "life compile-pass random 24x24 initial literal",
          backend,
          CompileProfile.fromCompile(lifeCompiledIn.report, "focused setup compile")
        ),
        ConstantFoldExecutorRow(
          "sliding puzzle 3x3 pure compile-pass depth-8 step",
          backend,
          CompileProfile.fromCompile(slide3Compiled.report, "focused setup compile")
        ),
        ConstantFoldExecutorRow(
          "n-queens MORKL 8x8 source graph compile",
          backend,
          queensSourceProfile
        ),
        ConstantFoldExecutorRow(
          "n-queens MORKL 8x8 compile-pass",
          backend,
          CompileProfile.fromCompile(queens8Compiled.report, "focused setup compile")
        )
      )
    }

  def constantFoldExecutorMarkdown(): String =
    val backends = Vector(
      ConstantFoldEval.Backend.Reference,
      ConstantFoldEval.Backend.Trie,
      ConstantFoldEval.Backend.Zipper,
      ConstantFoldEval.Backend.ExecT,
      ConstantFoldEval.Backend.Hybrid
    )
    backends.foreach(focusedConstantFoldRows)
    val rows = backends.flatMap(focusedConstantFoldRows)
    val baseline = rows.collect {
      case row if row.backend == ConstantFoldEval.Backend.Reference => row.benchmark -> row.foldMs
    }.toMap
    val body = rows.map { row =>
      val base = baseline(row.benchmark)
      val speed = if row.foldMs == 0.0 then "n/a" else f"${base / row.foldMs}%.2f x"
      f"| ${row.benchmark} | ${row.backend.toString} | ${row.profile.totalMs}%.3f | ${row.profile.sourcePassMs}%.3f | ${row.foldMs}%.3f | $speed | ${row.profile.constantFoldEvalMs}%.3f | ${row.profile.constantFoldEvalTrieMs}%.3f | ${row.profile.constantFoldEvalZMs}%.3f | ${row.profile.constantFoldExecTMs}%.3f | ${row.profile.constantFoldEvalCalls} | ${row.profile.constantFoldEvalTrieCalls} | ${row.profile.constantFoldEvalZCalls} | ${row.profile.constantFoldExecTCalls} | ${row.calls} |"
    }.mkString("\n")
    Vector(
      "# Constant Fold Executor Report",
      "",
      "Focused sweep over the four previously reported long constant-fold rows. `speedup vs reference` compares total constant-fold executor time within the same focused run.",
      "",
      "| benchmark | backend | compile ms | source pass ms | const-fold total ms | speedup vs reference | eval ms | evalTrie ms | evalZ ms | execT ms | eval calls | evalTrie calls | evalZ calls | execT calls | total calls |",
      "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
      body
    ).mkString("\n")

  def cases(): Vector[ProgramCase] =
    Console.err.println("[bench-setup] aunt fixtures")
    val family = TrieSpaceContext.fromReference(AuntQuery.context)
    val auntCall = R"aunts"(S"family", S"people")
    val auntStatic = R"aunts"(Literal(AuntQuery.context.resolve(SpaceMention("family"))), S"people")
    val auntResidual = Supercompiler.supercompile(auntStatic, mod(Routines.aunt_query_routine), SC.Config(maxNodes = 200, maxDepth = 80))
    val auntResidualProfile = CompileProfile.fromSC(auntResidual.report, "process SC setup")
    val auntPeopleOnly = SpaceContextMap(Map(SpaceMention("people") -> AuntQuery.context.resolve(SpaceMention("people"))))
    val auntPeopleTrie = TrieSpaceContext.fromReference(auntPeopleOnly)

    val (bigFamily, bigPeople) = syntheticFamily(4, 12)
    val bigAuntCtx = SpaceContextMap(Map(SpaceMention("family") -> bigFamily, SpaceMention("people") -> bigPeople))
    val bigAuntTrie = TrieSpaceContext.fromReference(bigAuntCtx)
    val royal92 = GoalExampleData.royal92Family
    val royal92Ctx = SpaceContextMap(Map(SpaceMention("family") -> royal92.family, SpaceMention("people") -> royal92.people))
    val royal92Trie = TrieSpaceContext.fromReference(royal92Ctx)
    val royal92Variant =
      if royal92.usedReal then s"reference royal92_simple.metta ${royal92.people.paths.size} people"
      else "reference royal92_simple.metta fallback"
    val (scFamily, scPeople) = syntheticFamily(3, 6)
    val scAuntStatic = R"aunts"(Literal(scFamily), S"people")
    val scAuntResidual = Supercompiler.supercompile(scAuntStatic, mod(Routines.aunt_query_routine), SC.Config(maxNodes = 220, maxDepth = 80))
    val scAuntResidualProfile = CompileProfile.fromSC(scAuntResidual.report, "process SC setup")
    val scPeopleCtx = SpaceContextMap(Map(SpaceMention("people") -> scPeople))
    val scPeopleTrie = TrieSpaceContext.fromReference(scPeopleCtx)

    Console.err.println("[bench-setup] graph fixtures")
    val graph = chainGraph(90)
    val graphCtx = SpaceContextMap(Map(SpaceMention("g") -> graph))
    val graphTrie = TrieSpaceContext.fromReference(graphCtx)
    val twoHop = R"two_hop"(S"g") := "TwoHop" x MQT(S"g"("edge"), List("$x.$y", "$y.$z"), "$x.$z")
    val mutual = R"mutual"(S"g") := "Mutual" x MQT(S"g"("edge"), List("$x.$y", "$y.$x"), "$x.$y")

    Console.err.println("[bench-setup] datalog residual")
    val semiNaive = DatalogExample.semiNaiveTransitive
    val datalogEdges = chainGraph(24)
    val datalogInitial = DatalogExample.semiNaiveInitial(Literal(datalogEdges))
    val datalogCall = semiNaive.name(datalogInitial)("complete.path")
    val datalogDefs: PartialFunction[RoutinePtr, Routine] = { case semiNaive.name => semiNaive }
    val datalogResidual = SC.supercompile(datalogCall, datalogDefs, SC.Config(maxNodes = 160, maxDepth = 120))
    val datalogResidualProfile = CompileProfile.fromSC(datalogResidual.report, "process SC setup")

    Console.err.println("[bench-setup] life compile")
    val lifeInitial = lifeField(24, 24, 120, 2406)
    val lifeInitialLiteral = Literal(lifeInitial)
    val life = R"nextStep"(lifeInitialLiteral)
    val lifeCompiled = Supercompiler.compile(LifeExample.nextStep, ctx = mod(LifeExample.neigh))
    val lifeCompiledProfile = CompileProfile.fromCompile(lifeCompiled.report, "compile-pass setup")
    val lifeCompiledIn = Supercompiler.specialize(
      LifeExample.nextStep,
      spaceArgs = Map(SpaceMention("field") -> lifeInitialLiteral),
      ctx = mod(LifeExample.neigh)
    )
    val lifeCompiledInProfile = CompileProfile.fromCompile(lifeCompiledIn.report, "compile-pass setup with initial grid literal")

    Console.err.println("[bench-setup] temperature fixtures")
    Console.err.println("[bench-setup] temperature committed load")
    val noaaWorld = GoalExampleData.noaaTemperatureData.world
    val noaaCtx = SpaceContextMap(Map(SpaceMention("world") -> noaaWorld))
    Console.err.println("[bench-setup] temperature committed trie")
    val noaaTrie = TrieSpaceContext.fromReference(noaaCtx)
    Console.err.println("[bench-setup] temperature committed query")
    val noaaQuery = R"temp_band"(S"world") :=
      S"world" <| ("cell" x Literal(TemperatureExample.interval(4, 20, GoalExampleData.noaaTemperatureData.latBits)) x Literal(TemperatureExample.interval(3, 28, GoalExampleData.noaaTemperatureData.lonBits)))
    Console.err.println("[bench-setup] temperature synthetic data")
    val noaaSyntheticWorld = noaaSynthetic(64, 32)
    val noaaSyntheticCtx = SpaceContextMap(Map(SpaceMention("world") -> noaaSyntheticWorld))
    Console.err.println("[bench-setup] temperature synthetic trie")
    val noaaSyntheticTrie = TrieSpaceContext.fromReference(noaaSyntheticCtx)
    Console.err.println("[bench-setup] temperature synthetic query")
    val noaaSyntheticQuery = R"temp_band_big"(S"world") :=
      S"world" <| ("cell" x Literal(TemperatureExample.interval(8, 40, 6)) x Literal(TemperatureExample.interval(32, 180, 9)))

    Console.err.println("[bench-setup] puzzle fixtures")
    val puzzle2 = Literal(puzzleReachable(2, 16))
    val puzzle3 = Literal(puzzleReachable(3, 8))
    val puzzle4 = Literal(puzzleReachable(4, 5))
    val slide2 = SlidingPuzzleExample.step(2, puzzle2)
    val slide3 = SlidingPuzzleExample.step(3, puzzle3)
    val slide4 = SlidingPuzzleExample.step(4, puzzle4)
    val slide2Compiled = Supercompiler.compile(R"slide2"() := slide2, ctx = SlidingPuzzleExample.context(2), buildGraph = false)
    val slide3Compiled = Supercompiler.compile(R"slide3"() := slide3, ctx = SlidingPuzzleExample.context(3), buildGraph = false)
    val slide2CompiledProfile = CompileProfile.fromCompile(slide2Compiled.report, "compile-pass setup")
    val slide3CompiledProfile = CompileProfile.fromCompile(slide3Compiled.report, "compile-pass setup")
    val slide2Defs = SlidingPuzzleExample.routines(2)
    val slide3Defs = SlidingPuzzleExample.routines(3)
    val slide4Defs = SlidingPuzzleExample.routines(4)

    Console.err.println("[bench-setup] n-queens fixture")
    val (queens8, queens8Ctx) = NQueensExample.program(8)
    val queens8Compiled = Supercompiler.compile(queens8, ctx = queens8Ctx, buildGraph = false)
    val queens8CompiledProfile = CompileProfile.fromCompile(queens8Compiled.report, "compile-pass setup")
    val queens8Defs = NQueensExample.routines(8).filterNot(_.name == queens8.name)
    val emptyTrie = TrieSpaceContext.emptyMap

    Vector(
      ProgramCase("aunt", "reference", auntCall, AuntQuery.context, family, mod(Routines.aunt_query_routine), defs = Vector(Routines.aunt_query_routine)),
      ProgramCase("aunt", "process-sc static family", auntResidual.top, auntPeopleOnly, auntPeopleTrie, auntResidual.env, defs = auntResidual.routines.values.toVector, prep = Some(auntResidualProfile)),
      ProgramCase("aunt synthetic", "reference 60 people", auntCall, bigAuntCtx, bigAuntTrie, mod(Routines.aunt_query_routine), defs = Vector(Routines.aunt_query_routine), runs = 3),
      ProgramCase("aunt royal92", royal92Variant, auntCall, royal92Ctx, royal92Trie, mod(Routines.aunt_query_routine), defs = Vector(Routines.aunt_query_routine), runs = 2),
      ProgramCase("aunt synthetic", "process-sc static family 24 people", scAuntResidual.top, scPeopleCtx, scPeopleTrie, scAuntResidual.env, defs = scAuntResidual.routines.values.toVector, runs = 3, prep = Some(scAuntResidualProfile)),
      ProgramCase("graph two-hop", "reference 90-chain", twoHop.body, graphCtx, graphTrie, runs = 3),
      ProgramCase("graph mutual", "reference 90-chain", mutual.body, graphCtx, graphTrie, runs = 3),
      ProgramCase(
        "scc",
        "paper divide-and-conquer",
        SccCornerstone.body,
        rc = SccCornerstone.rc,
        defs = SccCornerstone.defs,
        runs = 3,
      ),
      ProgramCase(
        "datalog semi-naive",
        "reference 24-chain",
        datalogCall,
        rc = datalogDefs,
        defs = Vector(semiNaive),
        runs = 2,
      ),
      ProgramCase(
        "datalog semi-naive",
        "process-sc 24-chain",
        datalogResidual.top,
        rc = datalogResidual.env,
        defs = datalogResidual.routines.values.toVector,
        runs = 2,
        prep = Some(datalogResidualProfile),
      ),
      ProgramCase("life", "reference random 24x24", life, rc = mod(LifeExample.neigh, LifeExample.nextStep), defs = Vector(LifeExample.neigh, LifeExample.nextStep), runs = 2),
      ProgramCase("life", "compile-pass random 24x24", lifeCompiled.routine.name(lifeInitialLiteral), rc = mod(LifeExample.neigh, lifeCompiled.routine), defs = Vector(LifeExample.neigh, lifeCompiled.routine), runs = 2, prep = Some(lifeCompiledProfile)),
      ProgramCase("life", "compile-pass random 24x24 initial literal", lifeCompiledIn.routine.body, runs = 2, prep = Some(lifeCompiledInProfile)),
      ProgramCase("temperature", "NOAA committed slice", noaaQuery.body, noaaCtx, noaaTrie),
      ProgramCase("temperature", "synthetic 32x64", noaaSyntheticQuery.body, noaaSyntheticCtx, noaaSyntheticTrie, runs = 3),
      ProgramCase("sliding puzzle", "2x2 pure source full frontier step", slide2, rc = SlidingPuzzleExample.context(2), defs = slide2Defs, runs = 2),
      ProgramCase("sliding puzzle", "2x2 pure compile-pass full frontier step", slide2Compiled.routine.body, rc = SlidingPuzzleExample.context(2), defs = slide2Defs, runs = 2, prep = Some(slide2CompiledProfile)),
      ProgramCase(
        "sliding puzzle",
        "3x3 pure source depth-8 step",
        slide3,
        rc = SlidingPuzzleExample.context(3),
        defs = slide3Defs,
        runs = 1,
        zipperNote = Some("direct evalZ source search tree exceeds the benchmark heap; use evalTrie/graph rows")
      ),
      ProgramCase("sliding puzzle", "3x3 pure compile-pass depth-8 step", slide3Compiled.routine.body, rc = SlidingPuzzleExample.context(3), defs = slide3Defs, runs = 1, prep = Some(slide3CompiledProfile)),
      ProgramCase(
        "sliding puzzle",
        "4x4 pure source depth-5 step",
        slide4,
        rc = SlidingPuzzleExample.context(4),
        defs = slide4Defs,
        runs = 1,
        zipperNote = Some("direct evalZ source search tree exceeds the benchmark heap; use evalTrie/graph rows")
      ),
      ProgramCase("n-queens", "MORKL 8x8 source", queens8.body, tc = emptyTrie, rc = queens8Ctx, defs = queens8Defs, runs = 1, zipperNote = Some("direct evalZ is currently omitted for the high-level source search tree; use compile-pass/graph rows")),
      ProgramCase("n-queens", "MORKL 8x8 compile-pass", queens8Compiled.routine.body, tc = emptyTrie, rc = queens8Ctx, defs = queens8Defs, runs = 1, prep = Some(queens8CompiledProfile))
    )

  def markdown(): String =
    val rows = cases().map(row)
    def optMs(x: Option[Double]): String = x.fold("n/a")(v => f"$v%.3f")
    def optSpeed(x: Option[Double]): String = x.fold("n/a")(v => f"$v%.2f x")
    def optRatio(x: Option[Double]): String = x.fold("n/a")(v => f"$v%.2f x")
    def optInt(x: Option[Int]): String = x.fold("n/a")(v => f"$v%,d")
    val body = rows.map { r =>
      f"| ${r.name} | ${r.variant} | ${r.paths}%,d | ${r.refMs}%.3f | ${optMs(r.graphMs)} | ${r.trieMs}%.3f | ${optMs(r.zipperMs)} | ${optMs(r.execTMs)} | ${r.trieSpeedup}%.2f x | ${optSpeed(r.zipperSpeedup)} | ${optSpeed(r.zipperOverTrie)} | ${optSpeed(r.graphSpeedup)} | ${optSpeed(r.execTSpeedup)} | ${optSpeed(r.execTOverTrie)} | ${optInt(r.graphNodes)} | ${r.graphNote.getOrElse("")} |"
    }.mkString("\n")
    def compileMs(p: Option[CompileProfile]): String = p.fold("n/a")(v => f"${v.totalMs}%.3f")
    def combined(profiles: Seq[CompileProfile])(f: CompileProfile => Double): String =
      if profiles.isEmpty then "n/a" else f"${profiles.map(f).sum}%.3f"
    def combinedInt(profiles: Seq[CompileProfile])(f: CompileProfile => Int): String =
      if profiles.isEmpty then "n/a" else profiles.map(f).sum.toString
    def combinedLong(profiles: Seq[CompileProfile])(f: CompileProfile => Long): String =
      if profiles.isEmpty then "n/a" else profiles.map(f).sum.toString
    val compileBody = rows.map { r =>
      val profiles = Vector(r.prep, r.graphCompile).flatten
      val notes = profiles.map(_.note).distinct.mkString("; ")
      f"| ${r.name} | ${r.variant} | ${compileMs(r.prep)} | ${compileMs(r.graphCompile)} | ${optMs(r.totalCompileMs)} | ${optRatio(r.compileRunRatio)} | ${optMs(r.compilePlusExecTMs)} | ${combined(profiles)(_.lowerInlineMs)} | ${combined(profiles)(_.sourcePassMs)} | ${combined(profiles)(_.constantFoldEvalMs)} | ${combined(profiles)(_.constantFoldEvalTrieMs)} | ${combined(profiles)(_.constantFoldEvalZMs)} | ${combined(profiles)(_.constantFoldExecTMs)} | ${combinedInt(profiles)(_.constantFoldEvalCalls)} | ${combinedInt(profiles)(_.constantFoldEvalTrieCalls)} | ${combinedInt(profiles)(_.constantFoldEvalZCalls)} | ${combinedInt(profiles)(_.constantFoldExecTCalls)} | ${combined(profiles)(_.graphTranspileMs)} | ${combined(profiles)(_.graphOptimizeMs)} | ${combinedInt(profiles)(_.sourcePasses)} | ${combinedInt(profiles)(_.graphPasses)} | ${combinedLong(profiles)(_.budgetMs)} | $notes |"
    }.mkString("\n")
    Vector(
      "# Trie Runtime Benchmarks",
      "",
      "Measured with `TrieBenchmarks` on this worktree. Runtime times are average milliseconds per evaluation after two warmup runs. The first table excludes compilation/supercompilation and graph construction; rows labelled `process-sc` or `compile-pass` time the residual/compiled runtime. Runtime speedup cells and compile/run ratios are deliberately omitted for graphs that have been completely residualized to a one-node literal; use the compile+run column in the second table for those rows. The second table reports setup supercompilation time, graph compilation time, total compile time, compile/run ratio for non-residual graph execution, compile+`ROG execT` time, timed compile-stage totals, constant-folding eval time, and optimization-pass totals under explicit compile budgets. Graph optimization includes loop-invariant subgraph hoisting, push-out, and sharing. `ROG exec` is the legacy `RecursiveOpGraph` executor over `SpaceValue`; `evalZ` is the declarative zipper traversal evaluator that composes logical trie cursors and materializes only at the result boundary; `ROG execT` is the interned trie executor over `TrieSpace` and `List[Int]` path slots. Graph rows use fully optimized graphs: helper functions are inlined/expanded/lowered where possible, surviving `Call`s dispatch to optimized callee graphs, and graph-note cells list retained calls found in both the top graph and optimized callees. Recursive cycles are unsupported unless structurally certified as the paper SCC routine's strict three-way node partition.",
      "",
      "## Runtime",
      "",
      "| benchmark | variant | result paths | eval Set ms | ROG exec ms | evalTrie ms | evalZ ms | ROG execT ms | evalTrie / eval | evalZ / eval | evalZ / evalTrie | ROG exec / eval | ROG execT / eval | ROG execT / evalTrie | graph nodes | graph note |",
      "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|",
      body,
      "",
      "## Compilation And Optimization",
      "",
      "| benchmark | variant | prep compile ms | graph compile ms | total compile ms | compile/run | compile+ROG execT ms | lower+inline ms | source pass ms | const-fold eval ms | const-fold evalTrie ms | const-fold evalZ ms | const-fold execT ms | const-fold eval calls | const-fold evalTrie calls | const-fold evalZ calls | const-fold execT calls | graph transpile ms | graph optimize ms | source pass attempts | graph pass steps | budget ms sum | note |",
      "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|",
      compileBody,
      "",
      "| benchmark | variant | result | ms | note |",
      "|---|---:|---:|---:|---|",
      bitQueenRows().mkString("\n"),
      "",
      "## Interpretation",
      "",
      "The trie evaluator remains strongest on native path algebra with shared prefixes, joins, restriction, unwrap, and first-symbol iteration. The direct `execT` backend compounds that advantage when the graph is lowered to native ops and optimized callee graphs because it avoids rebuilding old `PathValue` and `SpaceValue` intermediates.",
      "",
      "`evalZ` is included as a correctness-backed zipper traversal runtime. Generic iteration now joins materialized branch tries directly at the final boundary, keeping nonrecursive scaling near `evalTrie`; union-saturating recursion is lowered and measured directly. Structurally positive, productive steps use prefix-demand cells, while state-negative semi-naive Datalog uses lazy exact synchronous rounds executed directly in native trie algebra. The SCC row executes the paper's well-founded pivot/partition recursion with masked reachability lowered to a fixpoint. The separate `ZIPPER_LARGE_BENCHMARKS.md` report contains larger nonrecursive scaling and product-selector rows. Direct source n-queens remains omitted for `evalZ` with an explicit note because that high-level search tree still needs a dedicated recursive zipper strategy.",
      "",
      "The pure Game-of-Life source is now intentionally a lowering benchmark: direct `evalTrie` still interprets the high-level relation program, while the graph backend lowers `Range`, `Unwrap`, joins, and literal coordinate relations into direct operations; use the `ROG execT` and compile+`ROG execT` columns for the lowered result.",
      "",
      "Graph timings are intentionally conservative about semantics. Raw routine calls are not timed as raw helper graphs; helper routines are inlined/expanded and lowered before graph execution when possible, and surviving calls use optimized callee graphs. Fixpoint lowering handles both single-state and invariant-parameter union-saturating shapes. Recursive residual cycles remain unsupported unless the structural checker certifies the paper SCC routine's three strict node partitions; that certified cycle dispatches through optimized callee graphs.",
      "",
      "Compilation is now explicitly bounded by wall-clock budgets as well as structural caps. Source normalization records every pass attempt, graph optimization records `hoist_loop_invariant_subgraphs`, `push_out`, and `optimize_sharing` per round, constant folding records eval/evalTrie/evalZ/execT time and call counts, and the compilation table separates setup SC time, lowering/inlining time, source-pass time, graph-build time, graph-optimization time, compile/run ratio, and compile+run time so runtime speedups are not mistaken for free compilation.",
      "",
      "`budget ms sum` is the sum of the independent compile invocation budgets used for a row, including optimized callee-graph compiles when present; it is not elapsed time and not a single shared deadline across all rows.",
      "",
      "Rows marked `compiled away; use compile+run` have been fully residualized to a one-node literal by the compile pipeline before execution. Their executor timings are still shown as an implementation sanity check, but their graph speedup factors are intentionally reported as `n/a`; the meaningful number is the compile+`ROG execT` total in the compilation table.",
      "",
      "The independent bit-recursive n-queens rows are scaling references, not MORKL runtime rows. They record the known targets through 12x12 while the pure MORKL path-algebra program is executed exactly at 8x8 and compiled/residualized for graph execution."
    ).mkString("\n")

@main def trieBenchmarkReport(): Unit =
  val report = TrieBenchmarks.markdown()
  Files.writeString(Paths.get("docs/TRIE_BENCHMARKS.md"), report + "\n")
  println(report)

@main def constantFoldExecutorReport(): Unit =
  val report = TrieBenchmarks.constantFoldExecutorMarkdown()
  Files.writeString(Paths.get("docs/CONSTANT_FOLD_EXECUTOR_BENCHMARKS.md"), report + "\n")
  println(report)
