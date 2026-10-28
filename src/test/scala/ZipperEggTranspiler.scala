package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path as JPath, Paths}
import scala.concurrent.duration.*
import scala.sys.process.*

case class ZipperEggExample(name: String,
                            expr: Space,
                            tc: TrieSpaceContextMap = TrieSpaceContext.emptyMap,
                            rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                            note: String = "")

case class ZipperEggProgram(example: ZipperEggExample,
                            zipper: SpaceZipper,
                            structuralSpaceEgg: String,
                            concreteSpaceEgg: String,
                            pathCount: Int,
                            materializationRounds: Int,
                            positiveDescentChecks: Vector[ZipperEggDescentCheck],
                            negativeDescentChecks: Vector[ZipperEggDescentCheck])

case class ZipperEggDescentCheck(label: String, path: Vector[String], expectedFocusEgg: String)

object ZipperEggTranspiler:
  private val Root: JPath = Paths.get(".")
  private val OutDir: JPath = Paths.get("zipper-egg-tests")
  private val MaxNegativeDescentChecks = 64
  private val ContextMovementName = "context-movement"
  private val FrontierAntimirovName = "frontier-antimirov"
  private val IterFixpointName = "iter-fixpoint"
  private val RangeObservationName = "range-observation"
  private val RangeBorderChildName = "range-border-child"
  private val RangeBorderOperationalName = "range-border-operational"
  private val TailsIntersectionFrontierName = "tails-intersection-frontier"
  private val NegativeKeyName = "negative-key"

  def examples: Vector[ZipperEggExample] =
    val aunt = ZipperEggExample(
      "aunt-kg",
      R"aunts"(S"family", S"people"),
      TrieSpaceContext.fromReference(AuntQuery.context),
      mod(Routines.aunt_query_routine),
      "Aunt graph query over the committed tiny family knowledge graph."
    )

    val puzzle2 = ZipperEggExample(
      "puzzle-2x2-step",
      SlidingPuzzleExample.step(2, Space.Literal(SlidingPuzzleExample.solved(2))),
      rc = SlidingPuzzleExample.context(2),
      note = "Pure 2x2 sliding-puzzle one-step expansion from the solved state."
    )

    val datalogEdges = chainGraph(5)
    val semiNaive = DatalogExample.semiNaiveTransitive
    val datalog = ZipperEggExample(
      "datalog-semi-naive",
      semiNaive.name(DatalogExample.semiNaiveInitial(Space.Literal(datalogEdges)))("complete.path"),
      rc = { case semiNaive.name => semiNaive },
      note = "Semi-naive transitive closure over a five-node chain."
    )

    val lifeField = SpaceValue(
      "Cell.0.0",
      "Cell.0.1",
      "Cell.1.0"
    )
    val life = ZipperEggExample(
      "game-of-life-small",
      R"nextStep"(Space.Literal(lifeField)),
      rc = mod(LifeExample.neigh, LifeExample.nextStep),
      note = "Small pure Game-of-Life B3/S23 step."
    )

    val tempWorld = SpaceValue(
      "cell.0.0.C",
      "cell.0.1.M",
      "cell.1.0.H",
      "cell.1.1.M"
    )
    val tempPrefixes =
      "cell" x
        Space.Literal(TemperatureExample.interval(0, 1, height = 2)) x
        Space.Literal(TemperatureExample.interval(0, 1, height = 2))
    val temperature = ZipperEggExample(
      "temperature-small",
      Space.Literal(tempWorld) <| tempPrefixes,
      note = "Small temperature prefix restriction shaped like the NOAA spatial query."
    )

    val (queens4, queens4Ctx) = NQueensExample.program(4)
    val nqueens = ZipperEggExample(
      "nqueens-4",
      queens4.body,
      rc = queens4Ctx,
      note = "Pure MORKL 4-queens search, kept small enough for generated egg artifacts."
    )

    Vector(aunt, puzzle2, datalog, life, temperature, nqueens)

  private def chainGraph(n: Int): SpaceValue =
    SpaceValue((0 until n).map(i => Syntax.parse(s"edge.n$i.n${i + 1}")).toSet)

  def build(example: ZipperEggExample): ZipperEggProgram =
    given PathContext = PathContext.emptyMap
    val zipperCtx = ZipperSpaceContext.fromTrie(example.tc)
    val loweredExpr = Supercompiler.lowerFixpointCalls(example.expr, example.rc)
    val zipper = transpileZ(loweredExpr)(using summon[PathContext], zipperCtx, example.rc)
    val actual = zipper.materialize
    val expected = evalTrie(example.expr)(using summon[PathContext], example.tc, example.rc)
    val loweredExpected = evalTrie(loweredExpr)(using summon[PathContext], example.tc, example.rc)
    require(
      loweredExpected == expected,
      s"${example.name}: recursion lowering changed evalTrie (${loweredExpected.pathCount} vs ${expected.pathCount} paths)"
    )
    require(
      actual == expected,
      s"${example.name}: transpileZ materialization disagrees with evalTrie (${actual.pathCount} vs ${expected.pathCount} paths)"
    )
    ZipperEggProgram(
      example,
      zipper,
      structuralSpace(zipper),
      space(expected),
      expected.pathCount,
      zipperDepth(zipper) + 2,
      positiveDescentChecks(expected),
      negativeDescentChecks(example.name, expected)
    )

  def writeAll(outDir: JPath = OutDir): Vector[JPath] =
    writeSelected(Set.empty, outDir)

  def writeSelected(names: Set[String], outDir: JPath = OutDir): Vector[JPath] =
    Files.createDirectories(outDir)
    val prelude = descentPrelude()
    val wantsContextMovement = names.isEmpty || names(ContextMovementName)
    val wantsFrontierAntimirov = names.isEmpty || names(FrontierAntimirovName)
    val wantsIterFixpoint = names.isEmpty || names(IterFixpointName)
    val wantsRangeObservation = names.isEmpty || names(RangeObservationName)
    val wantsRangeBorderChild = names.isEmpty || names(RangeBorderChildName)
    val wantsRangeBorderOperational = names.isEmpty || names(RangeBorderOperationalName)
    val wantsTailsIntersectionFrontier = names.isEmpty || names(TailsIntersectionFrontierName)
    val wantsNegativeKey = names.isEmpty || names(NegativeKeyName)
    val selected =
      if names.isEmpty then examples
      else
        val known =
          examples.map(_.name).toSet +
            ContextMovementName +
            FrontierAntimirovName +
            IterFixpointName +
            RangeObservationName +
            RangeBorderChildName +
            RangeBorderOperationalName +
            TailsIntersectionFrontierName +
            NegativeKeyName
        val unknown = names -- known
        require(unknown.isEmpty, s"Unknown zipper/egg examples: ${unknown.toVector.sorted.mkString(", ")}")
        examples.filter(example => names(example.name))
    require(
      selected.nonEmpty ||
        wantsContextMovement ||
        wantsFrontierAntimirov ||
        wantsIterFixpoint ||
        wantsRangeObservation ||
        wantsRangeBorderChild ||
        wantsRangeBorderOperational ||
        wantsTailsIntersectionFrontier ||
        wantsNegativeKey,
      s"No zipper/egg examples selected from: ${names.toVector.sorted.mkString(", ")}"
    )
    val outputs = selected.map { example =>
      val started = System.nanoTime()
      val program = render(build(example), prelude)
      val out = outDir.resolve(example.name + ".egg")
      Files.writeString(out, program, StandardCharsets.UTF_8)
      val elapsedMs = (System.nanoTime() - started) / 1000000L
      println(s"wrote $out in ${elapsedMs}ms")
      out
    }
    val withContext =
      if wantsContextMovement then outputs :+ writeContextMovement(outDir) else outputs
    val withFrontier =
      if wantsFrontierAntimirov then withContext :+ writeFrontierAntimirov(outDir) else withContext
    val withIter =
      if wantsIterFixpoint then withFrontier :+ writeIterFixpoint(outDir) else withFrontier
    val withRange =
      if wantsRangeObservation then withIter :+ writeRangeObservation(outDir) else withIter
    val withRangeBorder =
      if wantsRangeBorderChild then withRange :+ writeRangeBorderChild(outDir) else withRange
    val withRangeOperational =
      if wantsRangeBorderOperational then withRangeBorder :+ writeRangeBorderOperational(outDir) else withRangeBorder
    val withTailsIntersection =
      if wantsTailsIntersectionFrontier then withRangeOperational :+ writeTailsIntersectionFrontier(outDir) else withRangeOperational
    if wantsNegativeKey then withTailsIntersection :+ writeNegativeKey(outDir) else withTailsIntersection

  private def writeContextMovement(outDir: JPath): JPath =
    val started = System.nanoTime()
    val out = outDir.resolve(ContextMovementName + ".egg")
    Files.writeString(out, contextMovementProgram, StandardCharsets.UTF_8)
    val elapsedMs = (System.nanoTime() - started) / 1000000L
    println(s"wrote $out in ${elapsedMs}ms")
    out

  private def writeFrontierAntimirov(outDir: JPath): JPath =
    val started = System.nanoTime()
    val out = outDir.resolve(FrontierAntimirovName + ".egg")
    Files.writeString(out, frontierAntimirovProgram, StandardCharsets.UTF_8)
    val elapsedMs = (System.nanoTime() - started) / 1000000L
    println(s"wrote $out in ${elapsedMs}ms")
    out

  private def writeIterFixpoint(outDir: JPath): JPath =
    val started = System.nanoTime()
    val out = outDir.resolve(IterFixpointName + ".egg")
    Files.writeString(out, iterFixpointProgram, StandardCharsets.UTF_8)
    val elapsedMs = (System.nanoTime() - started) / 1000000L
    println(s"wrote $out in ${elapsedMs}ms")
    out

  private def writeRangeObservation(outDir: JPath): JPath =
    val started = System.nanoTime()
    val out = outDir.resolve(RangeObservationName + ".egg")
    Files.writeString(out, rangeObservationProgram, StandardCharsets.UTF_8)
    val elapsedMs = (System.nanoTime() - started) / 1000000L
    println(s"wrote $out in ${elapsedMs}ms")
    out

  private def writeRangeBorderChild(outDir: JPath): JPath =
    val started = System.nanoTime()
    val out = outDir.resolve(RangeBorderChildName + ".egg")
    Files.writeString(out, ZipperFocusedEggArtifacts.rangeBorderChildProgram, StandardCharsets.UTF_8)
    val elapsedMs = (System.nanoTime() - started) / 1000000L
    println(s"wrote $out in ${elapsedMs}ms")
    out

  private def writeRangeBorderOperational(outDir: JPath): JPath =
    val started = System.nanoTime()
    val out = outDir.resolve(RangeBorderOperationalName + ".egg")
    Files.writeString(out, ZipperFocusedEggArtifacts.rangeBorderOperationalProgram, StandardCharsets.UTF_8)
    val elapsedMs = (System.nanoTime() - started) / 1000000L
    println(s"wrote $out in ${elapsedMs}ms")
    out

  private def writeTailsIntersectionFrontier(outDir: JPath): JPath =
    val started = System.nanoTime()
    val out = outDir.resolve(TailsIntersectionFrontierName + ".egg")
    Files.writeString(out, ZipperFocusedEggArtifacts.tailsIntersectionFrontierProgram, StandardCharsets.UTF_8)
    val elapsedMs = (System.nanoTime() - started) / 1000000L
    println(s"wrote $out in ${elapsedMs}ms")
    out

  private def writeNegativeKey(outDir: JPath): JPath =
    val started = System.nanoTime()
    val out = outDir.resolve(NegativeKeyName + ".egg")
    Files.writeString(out, ZipperFocusedEggArtifacts.negativeKeyProgram, StandardCharsets.UTF_8)
    val elapsedMs = (System.nanoTime() - started) / 1000000L
    println(s"wrote $out in ${elapsedMs}ms")
    out

  private def contextMovementProgram: String = ZipperEggStaticPrograms.contextMovementProgram

  private def frontierAntimirovProgram: String = ZipperEggStaticPrograms.frontierAntimirovProgram

  private def iterFixpointProgram: String = ZipperEggStaticPrograms.iterFixpointProgram

  private def rangeObservationProgram: String = ZipperEggStaticPrograms.rangeObservationProgram

  def render(program: ZipperEggProgram, prelude: String): String =
    val name = program.example.name
    val id = eggId(name)
    val note =
      if program.example.note.isEmpty then ""
      else s"; ${program.example.note}\n"
    s"""$prelude
       |
       |; ---------------------------------------------------------------------------
       |; Generated by morkl.ZipperEggTranspiler.
       |; Example: $name
       |$note; Scala result path count: ${program.pathCount}
       |; Scala pre-write check: transpileZ(lowerFixpointCalls(expr)).materialize == evalTrie(expr).
       |
       |${indent(concreteItemDescentRules(program), 0)}
       |
       |${indent(operatorWitnessSection(id), 0)}
       |
       |(let $$${id}_scala_result
       |${indent(program.concreteSpaceEgg, 2)})
       |
       |(let $$${id}_scala_result_zipper
       |  (TrieZ $$${id}_scala_result))
       |
       |${indent(datalogIterWitnessSection(program, id, s"$$${id}_scala_result_zipper"), 0)}
       |
       |; Operational descent checks. These do not use materializes: each focus is
       |; reached by nested Descend operations over the concrete result trie, and
       |; is compared with the expected child trie at that focus. The separate
       |; zipper-descend.egg file models implementation-level zipper movement.
       |${indent(descentSection(id, s"$$${id}_scala_result_zipper", program.positiveDescentChecks, positive = true), 0)}
       |${indent(descentSection(id, s"$$${id}_scala_result_zipper", program.negativeDescentChecks, positive = false), 0)}
       |""".stripMargin

  private def descentPrelude(): String = ZipperEggStaticPrograms.descentPrelude()

  def zipper(z: SpaceZipper): String = z match
    case SpaceZipper.Trie(t) => s"(TrieZ ${space(t)})"
    case SpaceZipper.Memo(src) => s"(MemoZ ${zipper(src)})"
    case SpaceZipper.Union(left, right) => s"(UnionZ ${zipper(left)} ${zipper(right)})"
    case SpaceZipper.JoinAll(children) => joinAllZ(children.map(zipper))
    case SpaceZipper.Intersection(left, right) => s"(IntersectionZ ${zipper(left)} ${zipper(right)})"
    case SpaceZipper.MeetAll(children) => meetAllZ(children.map(zipper))
    case SpaceZipper.Subtraction(left, right) => s"(SubtractionZ ${zipper(left)} ${zipper(right)})"
    case SpaceZipper.Restriction(src, prefixes) => s"(RestrictionZ ${zipper(src)} ${zipper(prefixes)})"
    case SpaceZipper.Concat(left, right) => s"(ConcatZ ${zipper(left)} ${zipper(right)})"
    case SpaceZipper.Prefix(prefix, src) => s"(PrefixZipper ${path(prefix)} ${zipper(src)})"
    case SpaceZipper.NonEmpty(src) => s"(NonEmptyZ ${zipper(src)})"
    case SpaceZipper.TailsUnion(src) => s"(TailsUnionZ ${zipper(src)})"
    case SpaceZipper.TailsIntersection(src) => s"(TailsIntersectionZ ${zipper(src)})"
    case SpaceZipper.PrefixClosure(src, _) => s"(PrefixClosureZ ${zipper(src)})"
    case SpaceZipper.SuffixClosure(src) => s"(SuffixClosureZ ${zipper(src)})"
    case SpaceZipper.TailsClosure(src) => s"(TailsClosureZ ${zipper(src)})"
    case SpaceZipper.Head(src) => s"(HeadZ ${zipper(src)})"
    case SpaceZipper.Iteration(src, _, Some(template)) => s"(IterZ ${zipper(src)} ${iterTemplate(template)})"
    case z @ SpaceZipper.Iteration(_, _, None) => s"(TrieZ ${space(z.materialize)})"
    case SpaceZipper.Fixpoint(src, template) => s"(FixpointZ ${zipper(src)} ${iterTemplate(template)})"
    case SpaceZipper.Range(src, lo, hi) => s"""(RangeZ ${zipper(src)} "$lo" "$hi")"""
    case SpaceZipper.LastRange(src, count) => s"""(RangeZ ${zipper(src)} "-$count" "0")"""
    case SpaceZipper.DropLastRange(src, count) => s"""(RangeZ ${zipper(src)} "0" "-$count")"""
    // Higher-order fixpoint steps have no first-order egg constructor. Their
    // denotation was checked against evalTrie in build(), so export the exact
    // observed trie and keep all unrelated future zipper classes fail-loud.
    case deferred: SpaceZipper.DeferredFixpointFocus =>
      s"(TrieZ ${space(deferred.materialize)})"

  def structuralSpace(z: SpaceZipper): String = z match
    case SpaceZipper.Trie(t) => space(t)
    case SpaceZipper.Memo(src) => structuralSpace(src)
    case SpaceZipper.Union(left, right) => s"(Union ${structuralSpace(left)} ${structuralSpace(right)})"
    case SpaceZipper.JoinAll(children) => joinAll(children.map(structuralSpace))
    case SpaceZipper.Intersection(left, right) => s"(Intersection ${structuralSpace(left)} ${structuralSpace(right)})"
    case SpaceZipper.MeetAll(children) => meetAll(children.map(structuralSpace))
    case SpaceZipper.Subtraction(left, right) => s"(Subtraction ${structuralSpace(left)} ${structuralSpace(right)})"
    case SpaceZipper.Restriction(src, prefixes) => s"(Restriction ${structuralSpace(src)} ${structuralSpace(prefixes)})"
    case SpaceZipper.Concat(left, right) => s"(Product ${structuralSpace(left)} ${structuralSpace(right)})"
    case SpaceZipper.Prefix(prefix, src) => s"(Wrap ${path(prefix)} ${structuralSpace(src)})"
    case SpaceZipper.NonEmpty(src) => s"(NonEmpty ${structuralSpace(src)})"
    case SpaceZipper.TailsUnion(src) => s"(TailsUnion ${structuralSpace(src)})"
    case SpaceZipper.TailsIntersection(src) => s"(TailsIntersection ${structuralSpace(src)})"
    case SpaceZipper.PrefixClosure(src, _) => s"(PrefixClosure ${structuralSpace(src)})"
    case SpaceZipper.SuffixClosure(src) => s"(SuffixClosure ${structuralSpace(src)})"
    case SpaceZipper.TailsClosure(src) => s"(TailsClosure ${structuralSpace(src)})"
    case SpaceZipper.Head(src) => s"(Head ${structuralSpace(src)})"
    case z @ SpaceZipper.Iteration(_, _, _) => space(z.materialize)
    case z @ SpaceZipper.Fixpoint(_, _) => space(z.materialize)
    case SpaceZipper.Range(src, lo, hi) => s"""(Range ${structuralSpace(src)} "$lo" "$hi")"""
    case SpaceZipper.LastRange(src, count) => s"""(Range ${structuralSpace(src)} "-$count" "0")"""
    case SpaceZipper.DropLastRange(src, count) => s"""(Range ${structuralSpace(src)} "0" "-$count")"""
    case deferred: SpaceZipper.DeferredFixpointFocus => space(deferred.materialize)

  def space(t: TrieSpace): String =
    val paths = t.encodedPaths.sortWith((a, b) => TrieSpace.comparePaths(a, b) < 0)
    if paths.isEmpty then "(Empty)"
    else union(paths.map(p => s"(Singleton ${path(p)})"))

  def path(items: List[Int]): String =
    path(TrieSpace.decode(items))

  def path(pv: PathValue): String =
    pathItems(pv.items.map(_.show))

  private def iterTemplate(template: SpaceZipper.IterTemplateTag): String = template match
    case SpaceZipper.IterTemplateTag.Tail => "(TailTemplate)"
    case SpaceZipper.IterTemplateTag.Head => "(HeadTemplate)"
    case SpaceZipper.IterTemplateTag.Reconstruct => "(ReconstructTemplate)"
    case SpaceZipper.IterTemplateTag.PrefixedReconstruct(prefix) =>
      s"(PrefixedReconstructTemplate ${path(prefix)})"
    case SpaceZipper.IterTemplateTag.RangeTail(start, end) =>
      s"""(RangeTailTemplate "$start" "$end")"""
    case SpaceZipper.IterTemplateTag.RangeReconstruct(start, end) =>
      s"""(RangeReconstructTemplate "$start" "$end")"""
    case SpaceZipper.IterTemplateTag.PrefixedRangeReconstruct(prefix, start, end) =>
      s"""(PrefixedRangeReconstructTemplate ${path(prefix)} "$start" "$end")"""

  private def pathItems(items: List[String]): String = items match
    case Nil => "(Eps)"
    case head :: Nil => s"""(Item ${quote(head)})"""
    case head :: tail => s"""(Concat (Item ${quote(head)}) ${pathItems(tail)})"""

  private def union(xs: Vector[String]): String =
    xs.reduceLeft((a, b) => s"(Union $a $b)")

  private def joinAll(xs: Vector[String]): String = xs match
    case Vector() => "(Empty)"
    case Vector(one) => one
    case Vector(a, b) => s"(Union $a $b)"
    case Vector(a, b, c) => s"(JoinAll3 $a $b $c)"
    case Vector(a, b, rest*) => s"(JoinAll3 $a $b ${joinAll(rest.toVector)})"

  private def meetAll(xs: Vector[String]): String = xs match
    case Vector() => "(Empty)"
    case Vector(one) => one
    case Vector(a, b) => s"(Intersection $a $b)"
    case Vector(a, b, c) => s"(MeetAll3 $a $b $c)"
    case Vector(a, b, rest*) => s"(MeetAll3 $a $b ${meetAll(rest.toVector)})"

  private def joinAllZ(xs: Vector[String]): String = xs match
    case Vector() => "(EmptyZ)"
    case Vector(one) => one
    case Vector(a, b) => s"(UnionZ $a $b)"
    case Vector(a, b, c) => s"(JoinAllZ3 $a $b $c)"
    case Vector(a, b, rest*) => s"(JoinAllZ3 $a $b ${joinAllZ(rest.toVector)})"

  private def meetAllZ(xs: Vector[String]): String = xs match
    case Vector() => "(EmptyZ)"
    case Vector(one) => one
    case Vector(a, b) => s"(IntersectionZ $a $b)"
    case Vector(a, b, c) => s"(MeetAllZ3 $a $b $c)"
    case Vector(a, b, rest*) => s"(MeetAllZ3 $a $b ${meetAllZ(rest.toVector)})"

  private def indent(s: String, spaces: Int): String =
    val pad = " " * spaces
    s.linesIterator.map(pad + _).mkString("\n")

  private def quote(s: String): String =
    "\"" + s.flatMap {
      case '\\' => "\\\\"
      case '"' => "\\\""
      case '\n' => "\\n"
      case '\r' => "\\r"
      case '\t' => "\\t"
      case c => c.toString
    } + "\""

  private def concreteItemDescentRules(program: ZipperEggProgram): String =
    "; concrete item descent is handled by generic nonlinear rules in the prelude"

  private def operatorWitnessSection(id: String): String = ZipperEggStaticPrograms.operatorWitnessSection(id)

  private def datalogIterWitnessSection(program: ZipperEggProgram, id: String, root: String): String =
    if program.example.name != "datalog-semi-naive" then ""
    else
      val semiNaive = DatalogExample.semiNaiveTransitive
      val finalStateExpr = semiNaive.name(DatalogExample.semiNaiveInitial(Space.Literal(chainGraph(5))))
      val finalStateRc: PartialFunction[RoutinePtr, Routine] = { case semiNaive.name => semiNaive }
      val finalState = evalTrie(finalStateExpr)(using PathContext.emptyMap, TrieSpaceContext.emptyMap, finalStateRc)
      val stateName = "$" + id + "_semi_naive_final_state"
      val stateRoot = "$" + id + "_semi_naive_final_state_zipper"
      val completePathRoot = "$" + id + "_semi_naive_complete_path_projection"
      val iterRoot = "$" + id + "_semi_naive_iter_program"
      val iterHeads =
        program.positiveDescentChecks
          .flatMap(_.path.headOption)
          .distinct
          .sortBy(identity)
      val iterChildChecks =
        if iterHeads.isEmpty then ""
        else
          val letsAndQueries = iterHeads.map { head =>
            val childName = "$" + id + "_semi_naive_iter_child_" + eggId(head)
            s"""(let $childName
               |  (Child ${quote(head)} $iterRoot))
               |(iter-child-query $childName $completePathRoot (ReconstructTemplate) ${quote(head)})""".stripMargin
          }.mkString("\n")
          val assertions = iterHeads.map { head =>
            val childName = "$" + id + "_semi_naive_iter_child_" + eggId(head)
            s"""(check (iter-child-result $childName (Child ${quote(head)} $completePathRoot)))
               |(check (= $childName (Child ${quote(head)} $completePathRoot)))""".stripMargin
          }.mkString("\n")
          s"""$letsAndQueries
             |(run-schedule (saturate iter_child))
             |(run 16)
             |$assertions""".stripMargin
      val wholePathCheck =
        program.positiveDescentChecks
          .find(_.path == Vector("n0", "n5"))
          .orElse(program.positiveDescentChecks.filter(_.path.nonEmpty).sortBy(check => (-check.path.length, check.path.mkString("."))).headOption)
          .map { check =>
            val pathId = check.path.map(eggId).mkString("_")
            val focusName = "$" + id + "_semi_naive_iter_whole_path_" + pathId + "_focus"
            val sourceFocusName = "$" + id + "_semi_naive_projected_whole_path_" + pathId + "_focus"
            val missPath = check.path.dropRight(1) :+ "__semi_naive_absent_tail"
            val missName = "$" + id + "_semi_naive_iter_whole_path_" + pathId + "_miss_focus"
            s"""; Explicit end-to-end IterZ reconstruction probe over the longest chain path.
               |; This ties the semi-naive final complete/delta state projection to
               |; operational IterZ movement, rather than only to generic operator
               |; witnesses or a materialized result trie.
               |(let $focusName
               |  ${descendExpr(iterRoot, check.path)})
               |(let $sourceFocusName
               |  ${descendExpr(completePathRoot, check.path)})
               |(let $missName
               |  ${descendExpr(iterRoot, missPath)})
               |(run 64)
               |(check (= $focusName ${check.expectedFocusEgg})) ; accepted ${check.path.mkString(".")}
               |(check (= $focusName $sourceFocusName)) ; IterZ reconstructs the projected final-state path
               |(fail (check (= $missName (TrieZ (Singleton (Eps)))))) ; rejected ${missPath.mkString(".")}""".stripMargin
          }
          .getOrElse("; no whole-path IterZ check")
      s"""; Semi-naive datalog state-projection IterZ movement witness.
         |; This checks the final semi-naive complete/delta state, projects
         |; complete.path through UnwrapZ, then accepts every positive transitive
         |; path and rejects the sampled absent paths through
         |; IterZ(..., ReconstructTemplate).  The axiomatized arbitrary-data
         |; full-program schema check, including the zipper contract, is generated
         |; separately as semi_naive_datalog_full_program_structural_backend_equivalence.p;
         |; it assumes backend/source agreement per constructor and is not an
         |; independent implementation-equivalence proof.
         |(let $stateName
         |  ${space(finalState)})
         |(let $stateRoot
         |  (TrieZ $stateName))
         |(let $completePathRoot
         |  (UnwrapZ $stateRoot (Concat (Item "complete") (Item "path"))))
         |(let $iterRoot
         |  (IterZ $completePathRoot (ReconstructTemplate)))
         |$iterChildChecks
         |$wholePathCheck
         |${descentSection(id + "_semi_naive_iter", iterRoot, program.positiveDescentChecks, positive = true)}
         |${descentSection(id + "_semi_naive_iter_negative", iterRoot, program.negativeDescentChecks, positive = false)}""".stripMargin

  private def positiveDescentChecks(expected: TrieSpace): Vector[ZipperEggDescentCheck] =
    expected.encodedPaths
      .sortWith((a, b) => TrieSpace.comparePaths(a, b) < 0)
      .zipWithIndex
      .map { (items, idx) =>
        ZipperEggDescentCheck(
          s"pos_$idx",
          itemStrings(items),
          zipper(SpaceZipper.traversal(focus(expected, items)))
        )
      }

  private def negativeDescentChecks(name: String, expected: TrieSpace): Vector[ZipperEggDescentCheck] =
    val positives = expected.encodedPaths.sortWith((a, b) => TrieSpace.comparePaths(a, b) < 0)
    val absent = absentItem(name, positives)
    val absentId = TrieSpace.interner.intern(PathItem(absent))
    val candidates =
      (List(absentId) +:
        positives.flatMap { path =>
          val mutations = path.indices.map(i => path.updated(i, absentId)).toVector
          mutations :+ (path :+ absentId)
        }).distinct
    candidates
      .filterNot(expected.containsItems)
      .take(MaxNegativeDescentChecks)
      .zipWithIndex
      .map { (items, idx) =>
        ZipperEggDescentCheck(s"neg_$idx", itemStrings(items), "(EmptyZ)")
      }

  private def focus(space: TrieSpace, path: List[Int]): TrieSpace =
    path.foldLeft(space)((current, item) => current.children.getOrElse(item, TrieSpace.empty))

  private def itemStrings(items: List[Int]): Vector[String] =
    TrieSpace.decode(items).items.map(_.show).toVector

  private def absentItem(name: String, paths: Vector[List[Int]]): String =
    val used = paths.flatMap(itemStrings).toSet
    Iterator.from(0)
      .map(i => s"__zipper_absent_${eggId(name)}_$i")
      .find(candidate => !used(candidate))
      .get

  private def descentSection(id: String,
                             root: String,
                             checks: Vector[ZipperEggDescentCheck],
                             positive: Boolean): String =
    if checks.isEmpty then "; no descent checks"
    else
      val kind = if positive then "positive" else "negative"
      val maxPath = checks.iterator.map(_.path.length).maxOption.getOrElse(0)
      val rounds = (checks.length + maxPath + 4).max(64).min(192)
      val lets = checks.map { check =>
        val focusName = "$" + id + "_" + check.label + "_focus"
        s"""(let $focusName
           |  ${descendExpr(root, check.path)})""".stripMargin
      }.mkString("\n")
      val assertions = checks.map { check =>
        val focusName = "$" + id + "_" + check.label + "_focus"
        s"(check (= $focusName ${check.expectedFocusEgg})) ; $kind ${check.path.mkString(".")}"
      }.mkString("\n")
      val negativeAssertions =
        if positive then ""
        else
          "\n" + checks.map { check =>
            val focusName = "$" + id + "_" + check.label + "_focus"
            s"(fail (check (= $focusName (TrieZ (Singleton (Eps)))))) ; not accepted ${check.path.mkString(".")}"
          }.mkString("\n")
      s"""$lets
         |(run $rounds)
         |$assertions$negativeAssertions""".stripMargin

  private def descendExpr(root: String, path: Vector[String]): String =
    path.foldLeft(root)((focus, item) => s"(Descend ${quote(item)} $focus)")

  private def eggId(name: String): String =
    val cleaned = name.map {
      case c if c.isLetterOrDigit || c == '_' => c
      case _ => '_'
    }.mkString
    if cleaned.headOption.exists(_.isDigit) then "_" + cleaned else cleaned

  private def zipperDepth(z: SpaceZipper): Int = z match
    case SpaceZipper.Trie(_) => 1
    case SpaceZipper.Memo(src) => 1 + zipperDepth(src)
    case SpaceZipper.Union(left, right) => 1 + (zipperDepth(left) max zipperDepth(right))
    case SpaceZipper.JoinAll(children) => 1 + children.iterator.map(zipperDepth).maxOption.getOrElse(0)
    case SpaceZipper.Intersection(left, right) => 1 + (zipperDepth(left) max zipperDepth(right))
    case SpaceZipper.MeetAll(children) => 1 + children.iterator.map(zipperDepth).maxOption.getOrElse(0)
    case SpaceZipper.Subtraction(left, right) => 1 + (zipperDepth(left) max zipperDepth(right))
    case SpaceZipper.Restriction(src, prefixes) => 1 + (zipperDepth(src) max zipperDepth(prefixes))
    case SpaceZipper.Concat(left, right) => 1 + (zipperDepth(left) max zipperDepth(right))
    case SpaceZipper.Prefix(_, src) => 1 + zipperDepth(src)
    case SpaceZipper.NonEmpty(src) => 1 + zipperDepth(src)
    case SpaceZipper.TailsUnion(src) => 1 + zipperDepth(src)
    case SpaceZipper.TailsIntersection(src) => 1 + zipperDepth(src)
      case SpaceZipper.PrefixClosure(src, _) => 1 + zipperDepth(src)
      case SpaceZipper.SuffixClosure(src) => 1 + zipperDepth(src)
      case SpaceZipper.TailsClosure(src) => 1 + zipperDepth(src)
      case SpaceZipper.Head(src) => 1 + zipperDepth(src)
      case SpaceZipper.Iteration(src, _, _) => 1 + zipperDepth(src)
      case SpaceZipper.Fixpoint(src, _) => 1 + zipperDepth(src)
      case SpaceZipper.Range(src, _, _) => 1 + zipperDepth(src)
    case SpaceZipper.LastRange(src, _) => 1 + zipperDepth(src)
    case SpaceZipper.DropLastRange(src, _) => 1 + zipperDepth(src)
    case _: SpaceZipper.DeferredFixpointFocus => 1

class ZipperEggTranspilerTest extends FunSuite:
  override val munitTimeout: Duration = 2.minutes

  test("deferred exact fixpoints export only after checked materialization") {
    val example = ZipperEggTranspiler.examples.find(_.name == "datalog-semi-naive").get
    val program = ZipperEggTranspiler.build(example)
    assert(program.zipper.isInstanceOf[SpaceZipper.DeferredFixpointFocus])
    assertEquals(program.structuralSpaceEgg, program.concreteSpaceEgg)
    assert(ZipperEggTranspiler.zipper(program.zipper).startsWith("(TrieZ "))
  }

  test("Scala zipper examples transpile to independently runnable egg programs") {
    val outputs = ZipperEggTranspiler.writeAll()
    val expectedFiles = Set(
      "aunt-kg.egg",
      "puzzle-2x2-step.egg",
      "datalog-semi-naive.egg",
      "game-of-life-small.egg",
      "temperature-small.egg",
      "nqueens-4.egg",
      "context-movement.egg",
      "frontier-antimirov.egg",
      "iter-fixpoint.egg",
      "range-observation.egg",
      "range-border-child.egg",
      "range-border-operational.egg",
      "tails-intersection-frontier.egg",
      "negative-key.egg"
    )
    assertEquals(outputs.map(_.getFileName.toString).toSet, expectedFiles)
    outputs.foreach { path =>
      val cmd = Seq("egglog", path.toString)
      val out = new StringBuilder
      val code = cmd.!(ProcessLogger(line => out.append(line).append('\n'), line => out.append(line).append('\n')))
      assertEquals(code, 0, s"egglog failed for $path\n$out")
    }
    val datalogEgg = Files.readString(Paths.get("zipper-egg-tests/datalog-semi-naive.egg"), StandardCharsets.UTF_8)
    assert(datalogEgg.contains("_semi_naive_final_state"), "datalog egg witness should include the full final complete/delta state")
    assert(datalogEgg.contains("_semi_naive_complete_path_projection"), "datalog egg witness should project complete.path before IterZ traversal")
    assert(
      datalogEgg.contains("_semi_naive_iter_negative_neg_0_focus"),
      "datalog egg witness should reject sampled absent paths through IterZ, not only through the materialized result trie"
    )
    assert(
      datalogEgg.sliding("iter-child-query".length).count(_ == "iter-child-query") >= 5,
      "datalog egg witness should check local IterZ movement for each top-level transitive-closure head"
    )
    assert(
      datalogEgg.sliding("(check (= $datalog_semi_naive_semi_naive_iter_child_".length)
        .count(_ == "(check (= $datalog_semi_naive_semi_naive_iter_child_") >= 5,
      "datalog egg witness should check direct operational IterZ child movement, not only scheduled relation witnesses"
    )
    assert(
      datalogEgg.contains("_semi_naive_iter_whole_path_n0_n5_focus"),
      "datalog egg witness should include a named end-to-end IterZ acceptance probe for the longest chain path"
    )
    assert(
      datalogEgg.contains("__semi_naive_absent_tail"),
      "datalog egg witness should include a same-prefix IterZ rejection probe next to the accepted whole path"
    )
    assert(
      !datalogEgg.contains("(IterZ $datalog_semi_naive_scala_result_zipper (ReconstructTemplate))"),
      "datalog egg witness must not regress to IterZ over the already-projected result trie"
    )
    assert(
      datalogEgg.contains("semi_naive_datalog_full_program_structural_backend_equivalence.p"),
      "datalog egg witness should name the arbitrary-data structural zipper/backend schema artifact"
    )
    assert(!datalogEgg.contains("still not the full"), "datalog egg witness should not retain stale weak-proof wording")
    (Paths.get("zipper-descend.egg") +: outputs).foreach { path =>
      val text = Files.readString(path, StandardCharsets.UTF_8)
      val concreteClosureExpansion =
        text.linesIterator.exists { line =>
          line.contains("(rewrite") &&
            (line.contains("SuffixClosureOp (TrieZ") || line.contains("TailsClosureOp (TrieZ"))
        }
      assert(
        !concreteClosureExpansion,
        s"$path must not reintroduce concrete SuffixClosureOp(TrieZ ...) or TailsClosureOp(TrieZ ...) expansion rewrites"
      )
    }
    val modelOut = new StringBuilder
    val modelCode = Seq("egglog", "zipper-descend.egg").!(
      ProcessLogger(line => modelOut.append(line).append('\n'), line => modelOut.append(line).append('\n'))
    )
    assertEquals(modelCode, 0, s"egglog failed for zipper-descend.egg\n$modelOut")
  }

@main def generateZipperEggTests(names: String*): Unit =
  IllustrativeEggArtifacts.write().foreach(path => println(path.toString))
  val outputs = ZipperEggTranspiler.writeSelected(names.toSet)
  outputs.foreach(path => println(path.toString))
