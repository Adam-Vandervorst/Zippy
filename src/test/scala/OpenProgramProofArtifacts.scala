package morkl

import morkl.ProofArtifacts as PA
import morkl.Syntax.{*, given}

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path as JPath, Paths}
import java.security.MessageDigest
import scala.collection.mutable

case class OpenProgramCase(name: String,
                           routine: Routine,
                           defs: Vector[Routine] = Vector.empty,
                           alphabet: Vector[String] = Vector("a", "b"),
                           maxLen: Int = 3,
                           explicitUniverse: Option[Vector[PA.PathTuple]] = None,
                           relations: Set[String] = OpenProgramCase.AllRelations,
                           note: String = "")

object OpenProgramCase:
  val SpaceOptimized: String = "space_optimized_open"
  val RawGraphRoundTrip: String = "raw_graph_roundtrip_open"
  val OptimizedGraphRoundTrip: String = "optimized_graph_roundtrip_open"
  val AllRelations: Set[String] = Set(SpaceOptimized, RawGraphRoundTrip, OptimizedGraphRoundTrip)

case class OpenProgramRelation(caseName: String,
                               relation: String,
                               lhsLabel: String,
                               rhsLabel: String,
                               lhs: PA.SpaceExpr,
                               rhs: PA.SpaceExpr,
                               ctx: PA.Ctx,
                               note: String)

case class OpenProgramSkip(caseName: String, relation: String, reason: String)

object OpenProgramProofArtifacts:
  private val OutDir: JPath = Paths.get("proofs/open")
  private val Manifest: JPath = OutDir.resolve("proof_manifest.tsv")
  private val SlidingPuzzleWitnessNote =
    "Non-vacuity witnesses: bounded translated source/optimizer/graph relations retain TL.1.2.3 -R-> TR.1.2.3, TR.1.2.3 -L-> TL.1.2.3, TL.1.2.3 -D-> BL.2.1.3, and BL.2.1.3 -U-> TL.1.2.3."

  case class Artifact(kind: String, name: String, expected: String, artifact: JPath, note: String = "")

  def cases: Vector[OpenProgramCase] =
    val synthetic = Vector(
      open("union-open", Vector(SpaceMention("x"), SpaceMention("y")), S"x" \/ S"y",
        note = "Open union over arbitrary X/Y input spaces."),
      open("intersection-open", Vector(SpaceMention("x"), SpaceMention("y")), S"x" /\ S"y",
        note = "Open intersection over arbitrary X/Y input spaces."),
      open("subtraction-open", Vector(SpaceMention("x"), SpaceMention("y")), S"x" \ S"y",
        note = "Open subtraction over arbitrary X/Y input spaces."),
      open("restriction-open", Vector(SpaceMention("x"), SpaceMention("p")), S"x" <| S"p",
        note = "Open restriction by arbitrary prefix space."),
      open("raffination-open", Vector(SpaceMention("x"), SpaceMention("p")), S"x" \| S"p",
        note = "Open raffination by arbitrary prefix space."),
      open("composition-open", Vector(SpaceMention("x"), SpaceMention("y")), S"x" x S"y",
        note = "Open product/composition over arbitrary X/Y input spaces."),
      open("unwrap-dynamic-open", Vector(SpaceMention("x"), SpaceMention("p")), S"p".iterh(P"p", S"x"(P"p")),
        note = "Open dynamic unwrap with prefixes supplied by a symbolic space."),
      open("wrap-dynamic-open", Vector(SpaceMention("x"), SpaceMention("p")), S"p".iterh(P"p", P"p" x S"x"),
        note = "Open dynamic wrap with prefixes supplied by a symbolic space."),
      open("transform-pair-swap-open", Vector(SpaceMention("x")),
        Unification.T(S"x", "$left.$right", "$right.$left"),
        alphabet = Vector("a", "b"),
        maxLen = 2,
        note = "Open pure transform-pattern pair swap over arbitrary bounded input data; Space.Transform remains removed and this uses the MORKL Unification.T expansion."),
      open("tails-union-open", Vector(SpaceMention("x")), \/(S"x"),
        note = "Open tails-union over arbitrary input data."),
      open("tails-intersection-open", Vector(SpaceMention("x")), /\(S"x"),
        note = "Open tails-intersection over arbitrary input data."),
      open("prefix-closure-open", Vector(SpaceMention("x")), Space.PrefixClosure(S"x"),
        note = "Open prefix closure over arbitrary input data."),
      open("suffix-closure-open", Vector(SpaceMention("x")), Space.SuffixClosure(S"x"),
        note = "Open suffix closure over arbitrary input data."),
      open("tails-closure-open", Vector(SpaceMention("x")), Space.TailsClosure(S"x"),
        note = "Open tails closure over arbitrary input data."),
      open("range-first-open", Vector(SpaceMention("x")), Space.Range(S"x", 0, 1),
        note = "Open ordered trie Range first element over arbitrary input data."),
      open("range-last-open", Vector(SpaceMention("x")), Space.Range(S"x", -1, 0),
        note = "Open ordered trie Range last element over arbitrary input data."),
      open("range-drop-last-open", Vector(SpaceMention("x")), Space.Range(S"x", 0, -1),
        alphabet = Vector("a", "b"),
        maxLen = 3,
        note = "Open ordered trie Range drop-last slice over arbitrary input data."),
      open("range-full-sentinel-open", Vector(SpaceMention("x")), Space.Range(S"x", 0, 0),
        alphabet = Vector("a", "b"),
        maxLen = 3,
        note = "Open ordered trie Range 0-sentinel full slice over arbitrary input data."),
      open("range-negative-window-open", Vector(SpaceMention("x")), Space.Range(S"x", -2, -1),
        alphabet = Vector("a", "b"),
        maxLen = 3,
        note = "Open ordered trie Range negative-index middle window over arbitrary input data."),
      open("iteration-reconstruct-open", Vector(SpaceMention("x")), S"x".iter(P"h", S"tail", P"h" x S"tail"),
        note = "Open MORKL iteration reconstructs the headed part of an arbitrary input space."),
      open("iteration-head-tail-blend-open", Vector(SpaceMention("x"), SpaceMention("y")),
        S"x".iter(P"h", S"tail", (P"h" x S"y") \/ S"tail"),
        note = "Open MORKL iteration with both head and rest sensitivity."),
      open("iteration-range-tail-first-open", Vector(SpaceMention("x")),
        S"x".iter(P"h", S"tail", Space.Range(S"tail", 0, 1)),
        alphabet = Vector("a", "b"),
        maxLen = 3,
        note = "Open Iteration template that applies ordered first-range selection independently to each child tail."),
      open("iteration-range-reconstruct-drop-last-open", Vector(SpaceMention("x")),
        S"x".iter(P"h", S"tail", P"h" x Space.Range(S"tail", 0, -1)),
        alphabet = Vector("a", "b"),
        maxLen = 3,
        note = "Open Iteration template that reconstructs each head with a drop-last ordered tail slice."),
      open("fixpoint-open", Vector(SpaceMention("seed")), Space.Fixpoint(S"seed", SpaceMention("state"), S"state" \/ \/(S"state")),
        note = "Open finite-universe fixpoint over a monotone tails-union step."),
    )

    val auntBody =
      "Aunt" x (S"family"("siblingOfParent") /\ (S"people" x S"family"("female")))
    val aunt = OpenProgramCase(
      "aunt-open",
      Routine(RoutinePtr("aunt_open"), Vector.empty, Vector(SpaceMention("family"), SpaceMention("people")),
        auntBody),
      alphabet = Vector("Aunt", "siblingOfParent", "female", "a", "b"),
      maxLen = 1,
      note = "Pure open graph-query Aunt join over arbitrary shallow family/people spaces.",
    )

    val auntFull = OpenProgramCase(
      "aunt-full-open",
      Routine(RoutinePtr("aunt_full_open"), Vector.empty, Vector(SpaceMention("family"), SpaceMention("people")),
        R"aunts"(S"family", S"people")),
      defs = Vector(Routines.aunt_query_routine),
      alphabet = Vector("Aunt", "parent", "child", "female", "person", "a", "b"),
      maxLen = 3,
      note = "Full Aunt query routine over arbitrary bounded family/people spaces.",
    )

    val datalogFullNodes = Vector("a")
    val datalogState = SpaceMention("datalog_state")
    val datalogLast = Space.Mention(datalogState)
    val datalogFullStep =
      ("complete" x (datalogLast("complete") \/ datalogLast("delta"))) \/
        ("delta.path" x (
          (Unification.MQT(datalogLast, List("complete.edge.$x.$y"), "$x.$y") \/
            Unification.MQT(datalogLast, List("complete.path.$x.$y", "delta.path.$y.$z"), "$x.$z") \/
            Unification.MQT(datalogLast, List("delta.path.$x.$y", "complete.path.$y.$z"), "$x.$z") \/
            Unification.MQT(datalogLast, List("delta.path.$x.$y", "delta.path.$y.$z"), "$x.$z"))
            \ (datalogLast("complete.path") \/ datalogLast("delta.path"))))
    val datalogFullBody =
      Space.Fixpoint(DatalogExample.semiNaiveInitial(S"edges"), datalogState, datalogFullStep)("complete.path")
    val datalogFull = OpenProgramCase(
      "semi-naive-datalog-full-open",
      Routine(RoutinePtr("semi_naive_datalog_full_open"), Vector.empty, Vector(SpaceMention("edges")),
        datalogFullBody),
      alphabet = Vector("complete", "delta", "edge", "path") ++ datalogFullNodes,
      maxLen = 4,
      explicitUniverse = Some(datalogUniverse(datalogFullNodes)),
      note = "Full semi-naive transitive-closure routine over arbitrary bounded edge data on a shape-aware node universe.",
    )

    val datalogBody =
      ("complete" x (S"complete" \/ S"delta")) \/
        ("delta" x (S"candidate" \ (S"complete" \/ S"delta")))
    val datalog = OpenProgramCase(
      "semi-naive-datalog-open",
      Routine(RoutinePtr("semi_naive_datalog_open"), Vector.empty,
        Vector(SpaceMention("complete"), SpaceMention("delta"), SpaceMention("candidate")),
        datalogBody),
      alphabet = Vector("path", "complete", "delta", "a", "b"),
      maxLen = 3,
      note = "Open semi-naive Datalog complete/delta update skeleton over arbitrary bounded spaces; full transitive closure remains in cornerstone data equivalence.",
    )

    val golBody =
      "Cell" x ((S"field"("Cell") /\ Space.Range(S"neighbors", 2, 3)) \/ Space.Range(S"neighbors", 3, 4))
    val gol = OpenProgramCase(
      "gol-open",
      Routine(RoutinePtr("gol_open"), Vector.empty, Vector(SpaceMention("field"), SpaceMention("neighbors")), golBody),
      alphabet = Vector("Cell", "-1", "0", "1", "2"),
      maxLen = 1,
      note = "Open pure Game-of-Life rule skeleton over arbitrary shallow field/neighbor-count spaces; full helper-based nextStep remains in cornerstone data equivalence.",
    )

    val proofLife = proofLifeRoutines(0 to 1)
    val golFull = OpenProgramCase(
      "gol-full-open",
      Routine(RoutinePtr("gol_full_open"), Vector.empty, Vector(SpaceMention("field")),
        proofLife.last.name(S"field")),
      defs = proofLife,
      alphabet = Vector("Cell", "hit", "-1", "0", "1", "2"),
      maxLen = 3,
      explicitUniverse = Some(lifeUniverse(-1 to 2)),
      note = "Full pure Game-of-Life nextStep routine over arbitrary bounded field data, using the same neighbor/range-cardinality construction on a proof-sized coordinate window.",
    )

    val tempPrefixes =
      "cell" x
        Space.Literal(TemperatureExample.interval(0, 1, height = 2)) x
        Space.Literal(TemperatureExample.interval(0, 1, height = 2))
    val temperature = OpenProgramCase(
      "temperature-open",
      Routine(RoutinePtr("temperature_open"), Vector.empty, Vector(SpaceMention("world")),
        S"world" <| tempPrefixes),
      alphabet = Vector("cell", "0", "1"),
      maxLen = 2,
      note = "Spatial temperature prefix query over arbitrary bounded world data.",
    )

    val puzzle = OpenProgramCase(
      "sliding-puzzle-2x2-open",
      Routine(RoutinePtr("sliding_puzzle_2x2_open"), Vector.empty,
        Vector(SpaceMention("frontier"), SpaceMention("moves"), SpaceMention("seen")),
        ((S"frontier" x S"moves") \ S"seen")),
      alphabet = Vector("TL", "TR", "BL", "BR", "U", "D", "L", "R"),
      maxLen = 2,
      note = "Open sliding-puzzle frontier/update skeleton over arbitrary bounded frontier/move/seen spaces; full transition is covered by cornerstone data equivalence.",
    )

    val puzzleFull = OpenProgramCase(
      "sliding-puzzle-2x2-full-open",
      Routine(RoutinePtr("sliding_puzzle_2x2_full_open"), Vector.empty,
        Vector(SpaceMention("states")),
        SlidingPuzzleExample.step(2, S"states")),
      defs = SlidingPuzzleExample.routines(2).take(2),
      alphabet = Vector("TL", "TR", "BL", "BR", "U", "D", "L", "R", "_", "0", "1", "2", "3"),
      maxLen = 4,
      explicitUniverse = Some(slidingPuzzle2x2Universe),
      note = s"Full pure 2x2 sliding-puzzle step syntax over arbitrary inputs inside a focused path universe; this is not the complete 24-state transition relation, and move-table constants outside the bound encode as zero. $SlidingPuzzleWitnessNote",
    )

    val nqueens = OpenProgramCase(
      "nqueens-4-open",
      Routine(RoutinePtr("nqueens_4_open"), Vector.empty,
        Vector(SpaceMention("available"), SpaceMention("attacked"), SpaceMention("taken")),
        (S"available" \ S"attacked").iterh(P"q", P"q" x S"taken")),
      alphabet = Vector("1", "2", "3", "4"),
      maxLen = 2,
      note = "Open n-queens placement skeleton over arbitrary bounded available/attacked/taken spaces; full pure MORKL n-queens is covered by cornerstone data equivalence.",
    )

    synthetic ++ Vector(aunt, auntFull, datalog, datalogFull, gol, golFull, temperature, puzzle, puzzleFull, nqueens)

  private def open(name: String,
                   mentions: Vector[SpaceMention],
                   body: Space,
                   alphabet: Vector[String] = Vector("a", "b", "c"),
                   maxLen: Int = 3,
                   note: String = ""): OpenProgramCase =
    OpenProgramCase(name, Routine(RoutinePtr(name.replace('-', '_')), Vector.empty, mentions, body), alphabet = alphabet, maxLen = maxLen, note = note)

  private def tuple(items: String*): PA.PathTuple =
    items.toVector

  private def closeUniverse(paths: Iterable[PA.PathTuple]): Vector[PA.PathTuple] =
    val out = mutable.LinkedHashSet.empty[PA.PathTuple]
    out += Vector.empty
    for path <- paths do
      // Every emitter-side child/tail operation must remain inside the explicit
      // universe, including a tail of a prefix introduced by this closure.
      // All contiguous slices are exactly the prefix-and-suffix fixed point.
      for
        start <- 0 to path.length
        end <- start to path.length
      do out += path.slice(start, end)
    out.toVector.sortWith(comparePathTuples(_, _) < 0)

  private def datalogUniverse(nodes: Vector[String]): Vector[PA.PathTuple] =
    val paths = Vector.newBuilder[PA.PathTuple]
    for
      x <- nodes
      y <- nodes
    do
      paths += tuple("edge", x, y)
      paths += tuple("path", x, y)
      paths += tuple("complete", "edge", x, y)
      paths += tuple("complete", "path", x, y)
      paths += tuple("delta", "path", x, y)
      paths += tuple(x, y)
    closeUniverse(paths.result())

  private def proofLifeRoutines(sourceCoords: Range): Vector[Routine] =
    def relation(f: Int => Int): Space =
      s(sourceCoords.map(i => Syntax.parse(s"${i}.${f(i)}")): _*)
    val decr = relation(_ - 1)
    val ident = relation(identity)
    val succ = relation(_ + 1)
    def around(coord: morkl.Path): Space =
      decr(coord) \/ ident(coord) \/ succ(coord)
    def rankWitness(space: Space, rank: Int): Space =
      Space.Range(space, rank, rank + 1).iterh(P"_", ss"hit")
    def exactly(space: Space, count: Int): Space =
      rankWitness(space, count) \ rankWitness(space, count + 1)
    val neigh = R"proofNeigh"(P"coord") := {
      Space.Singleton(P"coord").iter(P"x", S"ys", S"ys".iterh(P"y",
        (around(P"x") x around(P"y")) \ Space.Singleton(P"x" x P"y")
      ))
    }
    val next = R"proofNextStep"(S"field") := "Cell" x ((
      S"field"("Cell").iter(P"x", S"ys", S"ys".iter(P"y", S"_",
        \/(exactly(R"proofNeigh"(P"x" x P"y") /\ S"field"("Cell"), 2) x Space.Singleton(P"x" x P"y"))))
      \/
      S"field"("Cell").iter(P"x", S"ys", S"ys".iter(P"y", S"_",
        R"proofNeigh"(P"x" x P"y"))).iter(P"x", S"ys", S"ys".iter(P"y", S"_",
        \/(exactly(R"proofNeigh"(P"x" x P"y") /\ S"field"("Cell"), 3) x Space.Singleton(P"x" x P"y"))))
    ): Space)
    Vector(neigh, next)

  private def lifeUniverse(coords: Range): Vector[PA.PathTuple] =
    val labels = coords.map(_.toString).toVector
    val paths = Vector.newBuilder[PA.PathTuple]
    paths += tuple("hit")
    for
      x <- labels
      y <- labels
    do
      paths += tuple(x, y)
      paths += tuple("Cell", x, y)
    closeUniverse(paths.result())

  private def slidingPuzzle2x2Universe: Vector[PA.PathTuple] =
    val locations = Vector("TL", "TR", "BL", "BR")
    val locIndex = locations.zipWithIndex.toMap
    val paths = Vector.newBuilder[PA.PathTuple]
    val seed = Vector(0, 1, 2, 3)
    val movedRight = Vector(1, 0, 2, 3)
    val movedDown = Vector(2, 1, 0, 3)
    for state <- Vector(seed, movedRight, movedDown) do
      val statePath = SlidingPuzzleExample.pathState(2, state).items.map(_.show).toVector
      paths += statePath
      paths += statePath.tail
      val blankLoc = statePath.head
      for loc <- locations do
        val tile = if loc == blankLoc then "_" else state(locIndex(loc)).toString
        paths += tuple(loc, tile)

    // Keep a complete transition and its inverse on each board axis instead of
    // the former Cartesian product of every move, location, and tile. Both the
    // move-map relation and the actual action.destination.tile assignment stage
    // are retained for every cell.
    val boardA = Vector("TL" -> "_", "TR" -> "1", "BL" -> "2", "BR" -> "3")
    val boardB = Vector("TL" -> "1", "TR" -> "_", "BL" -> "2", "BR" -> "3")
    val boardC = Vector("TL" -> "2", "TR" -> "1", "BL" -> "_", "BR" -> "3")
    val witnessMoves = Vector(
      ("TL", "R", boardA, Vector("TL" -> "TR", "TR" -> "TL", "BL" -> "BL", "BR" -> "BR")),
      ("TR", "L", boardB, Vector("TL" -> "TR", "TR" -> "TL", "BL" -> "BL", "BR" -> "BR")),
      ("TL", "D", boardA, Vector("TL" -> "BL", "BL" -> "TL", "TR" -> "TR", "BR" -> "BR")),
      ("BL", "U", boardC, Vector("TL" -> "BL", "BL" -> "TL", "TR" -> "TR", "BR" -> "BR")),
    )
    for (oldBlank, action, board, moveMap) <- witnessMoves do
      val moveByLocation = moveMap.toMap
      for (loc, tile) <- board do
        paths += tuple(action, moveByLocation(loc), tile)
      for (loc, dst) <- moveMap do
        paths += tuple(oldBlank, action, loc, dst)
        paths += tuple(loc, dst)
      paths += tuple(oldBlank, action)
    for loc <- locations do paths += tuple(loc, loc)
    closeUniverse(paths.result())

  private def validateSlidingPuzzleWitness(): Unit =
    val states = Vector(
      SlidingPuzzleExample.pathState(2, Vector(0, 1, 2, 3)),
      SlidingPuzzleExample.pathState(2, Vector(1, 0, 2, 3)),
      SlidingPuzzleExample.pathState(2, Vector(2, 1, 0, 3)),
    )
    val directedEdges = Vector(
      states(0) -> states(1),
      states(1) -> states(0),
      states(0) -> states(2),
      states(2) -> states(0),
    )
    for (source, target) <- directedEdges do
      val output = eval(SlidingPuzzleExample.step(2, Space.Literal(SpaceValue(source))))(using
        pc = PathContext.emptyMap,
        sc = SpaceContextMap(Map.empty),
        rc = SlidingPuzzleExample.context(2),
      )
      require(output.paths.contains(target),
        s"sliding-puzzle production witness ${source.show} -> ${target.show} disappeared: got ${output.pretty}")
    val universe = slidingPuzzle2x2Universe.toSet
    require(states.forall(path => universe.contains(pathTuple(path))),
      "sliding-puzzle full-open universe must retain all three production witness states")

  private def validateBoundedSlidingPuzzleRelations(relations: Vector[OpenProgramRelation]): Unit =
    val states = Vector(
      tuple("TL", "1", "2", "3"),
      tuple("TR", "1", "2", "3"),
      tuple("BL", "2", "1", "3"),
    )
    val directedEdges = Vector(states(0) -> states(1), states(1) -> states(0), states(0) -> states(2), states(2) -> states(0))
    val symbolic = relations.filter(relation => OpenProgramCase.AllRelations(relation.relation))
    require(symbolic.length == OpenProgramCase.AllRelations.size,
      s"sliding-puzzle full-open must emit all three symbolic relations, got ${relations.map(_.relation).mkString(", ")}")
    for
      relation <- symbolic
      (source, target) <- directedEdges
    do
      val variables = Map("S_states" -> Set(source))
      val left = PA.evaluate(relation.lhs, relation.ctx, variables)
      val right = PA.evaluate(relation.rhs, relation.ctx, variables)
      require(left == right,
        s"${relation.caseName}:${relation.relation} bounded witness mismatch for ${source.mkString(".")}: lhs=$left rhs=$right")
      require(left.contains(target),
        s"${relation.caseName}:${relation.relation} bounded witness ${source.mkString(".")} -> ${target.mkString(".")} was truncated: output=$left")

    val expectedWitnesses = Map(
      "bounded_witness_a_open" -> Set(states(1), states(2)),
      "bounded_witness_b_open" -> Set(states(0)),
      "bounded_witness_c_open" -> Set(states(0)),
    )
    for (name, expected) <- expectedWitnesses do
      val relation = relations.find(_.relation == name).getOrElse(
        throw IllegalArgumentException(s"sliding-puzzle full-open missing $name"))
      val left = PA.evaluate(relation.lhs, relation.ctx)
      val right = PA.evaluate(relation.rhs, relation.ctx)
      require(left == expected && right == expected,
        s"${relation.caseName}:$name must preserve its exact bounded output $expected, got lhs=$left rhs=$right")

  private def permutations[A](xs: Vector[A]): Vector[Vector[A]] =
    if xs.isEmpty then Vector(Vector.empty)
    else
      xs.indices.toVector.flatMap { i =>
        val x = xs(i)
        permutations(xs.patch(i, Nil, 1)).map(x +: _)
      }

  def writeAll(outDir: JPath = OutDir, manifest: JPath = Manifest): Vector[Artifact] =
    val smtDir = outDir.resolve("smt2")
    val vampireDir = outDir.resolve("vampire")
    Files.createDirectories(outDir)
    Files.createDirectories(smtDir)
    Files.createDirectories(vampireDir)
    Files.createDirectories(manifest.getParent)
    validateSlidingPuzzleWitness()

    val artifacts = Vector.newBuilder[Artifact]
    val skips = Vector.newBuilder[OpenProgramSkip]
    val relations = Vector.newBuilder[OpenProgramRelation]

    for c <- cases do
      println(s"generating open-program proof artifacts for ${c.name}")
      val built = build(c)
      if c.name == "sliding-puzzle-2x2-full-open" then
        validateBoundedSlidingPuzzleRelations(built._1)
      skips ++= built._2
      for relation <- built._1 do
        relations += relation
        val base = s"${safe(c.name)}_${safe(relation.relation)}"
        val smtPath = smtDir.resolve(base + ".smt2")
        Files.writeString(smtPath, renderSmt2(relation), StandardCharsets.UTF_8)
        artifacts += Artifact("z3", s"${c.name}:${relation.relation}", "unsat", smtPath, relation.note)

    for c <- fullProgramFolCases do
      println(s"generating axiomatized structural full-program schema check for ${c.name}")
      val expanded = expandedRoutine(c)
      val tptpPath = vampireDir.resolve(s"${safe(c.name)}_structural_backend_equivalence.p")
      Files.writeString(tptpPath, renderStructuralFol(c, expanded.body), StandardCharsets.UTF_8)
      artifacts += Artifact("vampire", s"${c.name}:structural_backend_equivalence", "Theorem", tptpPath,
        "Axiomatized structural FOL schema check: the generated program DAG is well formed and backend membership contracts are mutually consistent. Backend/source agreement is assumed per constructor, so this is not an independent implementation-equivalence proof.")

    val all = artifacts.result()
    val manifestText =
      ("kind\tname\texpected\tartifact\tnote" +:
        all.map(a => Vector(a.kind, a.name, a.expected, a.artifact.toString, a.note).map(manifestField).mkString("\t")))
        .mkString("\n") + "\n"
    Files.writeString(manifest, manifestText, StandardCharsets.UTF_8)
    Files.writeString(outDir.resolve("OPEN_PROGRAM_REPORT.md"), renderReport(relations.result(), skips.result()), StandardCharsets.UTF_8)
    all

  private def fullProgramFolCases: Vector[OpenProgramCase] =
    val datalogState = SpaceMention("datalog_state")
    val datalogLast = Space.Mention(datalogState)
    val datalogFullStep =
      ("complete" x (datalogLast("complete") \/ datalogLast("delta"))) \/
        ("delta.path" x (
          (Unification.MQT(datalogLast, List("complete.edge.$x.$y"), "$x.$y") \/
            Unification.MQT(datalogLast, List("complete.path.$x.$y", "delta.path.$y.$z"), "$x.$z") \/
            Unification.MQT(datalogLast, List("delta.path.$x.$y", "complete.path.$y.$z"), "$x.$z") \/
            Unification.MQT(datalogLast, List("delta.path.$x.$y", "delta.path.$y.$z"), "$x.$z"))
            \ (datalogLast("complete.path") \/ datalogLast("delta.path"))))
    val datalogFullBody =
      Space.Fixpoint(DatalogExample.semiNaiveInitial(S"edges"), datalogState, datalogFullStep)("complete.path")

    val tempPrefixes =
      "cell" x
        Space.Literal(TemperatureExample.interval(0, 1, height = 2)) x
        Space.Literal(TemperatureExample.interval(0, 1, height = 2))

    val (queens4, queens4Ctx) = NQueensExample.program(4)
    val queensDefs = NQueensExample.routines(4).filter(r => queens4Ctx.isDefinedAt(r.name))
    val puzzle24 =
      Space.Literal(slidingPuzzleAllStates(2))
    val tailState = SpaceMention("state")
    val tailFixpointBody =
      Space.Fixpoint(S"seed", tailState, S"state" \/ \/(S"state"))

    Vector(
      OpenProgramCase(
        "fixpoint-tail-full-program",
        Routine(RoutinePtr("fixpoint_tail_full_program"), Vector.empty, Vector(SpaceMention("seed")),
          tailFixpointBody),
        note = "Small axiomatized structural FOL schema for tail-template fixpoint lowering.",
      ),
      OpenProgramCase(
        "aunt-full-program",
        Routine(RoutinePtr("aunt_full_program"), Vector.empty, Vector(SpaceMention("family"), SpaceMention("people")),
          R"aunts"(S"family", S"people")),
        defs = Vector(Routines.aunt_query_routine),
        note = "Full Aunt query over arbitrary family/people data.",
      ),
      OpenProgramCase(
        "semi-naive-datalog-full-program",
        Routine(RoutinePtr("semi_naive_datalog_full_program"), Vector.empty, Vector(SpaceMention("edges")), datalogFullBody),
        note = "Full semi-naive transitive closure over arbitrary edge data.",
      ),
      OpenProgramCase(
        "gol-full-program",
        Routine(RoutinePtr("gol_full_program"), Vector.empty, Vector(SpaceMention("field")),
          R"nextStep"(S"field")),
        defs = Vector(LifeExample.neigh, LifeExample.nextStep),
        note = "Full Game-of-Life nextStep over arbitrary field data.",
      ),
      OpenProgramCase(
        "temperature-full-program",
        Routine(RoutinePtr("temperature_full_program"), Vector.empty, Vector(SpaceMention("world")),
          S"world" <| tempPrefixes),
        note = "Full temperature spatial prefix query over arbitrary world data.",
      ),
      OpenProgramCase(
        "sliding-puzzle-2x2-full-program",
        Routine(RoutinePtr("sliding_puzzle_2x2_full_program"), Vector.empty, Vector(SpaceMention("states")),
          SlidingPuzzleExample.step(2, S"states")),
        defs = SlidingPuzzleExample.routines(2).take(2),
        note = "Full pure 2x2 sliding-puzzle transition over arbitrary state-frontier data.",
      ),
      OpenProgramCase(
        "sliding-puzzle-2x2-24-state-step-full-program",
        Routine(RoutinePtr("sliding_puzzle_2x2_24_state_step_full_program"), Vector.empty, Vector.empty,
          SlidingPuzzleExample.step(2, puzzle24)),
        defs = SlidingPuzzleExample.routines(2).take(2),
        note = "Full pure 2x2 sliding-puzzle transition with the complete 24-state permutation space as input.",
      ),
      OpenProgramCase(
        "sliding-puzzle-4x4-full-program",
        Routine(RoutinePtr("sliding_puzzle_4x4_full_program"), Vector.empty, Vector(SpaceMention("states")),
          SlidingPuzzleExample.step(4, S"states")),
        defs = SlidingPuzzleExample.routines(4).take(2),
        note = "Full pure 15-puzzle (4x4) transition over arbitrary state-frontier data.",
      ),
      OpenProgramCase(
        "nqueens-4-full-program",
        queens4.copy(name = RoutinePtr("nqueens_4_full_program")),
        defs = queensDefs,
        note = "Full pure 4-queens program.",
      ),
      OpenProgramCase(
        "scc-full-program",
        SccCornerstone.sccRoutine,
        defs = SccCornerstone.defs,
        note = "Paper seedless divide-and-conquer SCC routine over arbitrary forward/backward edge relations and node sets; masked reachability is lowered to Fixpoint while the three shrinking recursive partitions remain explicit.",
      ),
    )

  private final class FolDagEmitter:
    private val bindings = mutable.ArrayBuffer.empty[(String, String)]
    private val cache = mutable.LinkedHashMap.empty[String, String]
    private val literalConstants = mutable.LinkedHashMap.empty[String, SpaceValue]
    private val pathConstants = mutable.LinkedHashMap.empty[String, PathValue]
    private var next = 0

    def emitSpace(s: Space): String =
      bind(spaceKey(s), spaceTerm(s))

    def definitionAxioms: String =
      bindings.zipWithIndex.map { case ((name, term), i) =>
        s"fof(full_program_term_$i, axiom, $name = $term)."
      }.mkString("\n")

    def constantAxioms: String =
      val pathAxioms =
        pathConstants.toVector.zipWithIndex.map { case ((digest, path), i) =>
          s"fof(path_constant_$i, axiom, ! [P] : (path_matches(P,path_lit(${atom(digest)})) <=> P = ${folPath(path)}))."
        }
      val literalAxioms =
        literalConstants.toVector.zipWithIndex.map { case ((digest, space), i) =>
          val disj =
            if space.paths.isEmpty then "$false"
            else space.paths.toVector.sortBy(_.show).map(path => s"P = ${folPath(path)}").mkString(" | ")
          s"fof(literal_constant_$i, axiom, ! [P] : (literal_mem(P,${atom(digest)}) <=> ($disj)))."
        }
      (pathAxioms ++ literalAxioms).mkString("\n")

    private def bind(key: String, term: => String): String =
      cache.getOrElseUpdate(key, {
        val name = s"fp_$next"
        next += 1
        bindings += name -> term
        name
      })

    private def spaceTerm(s: Space): String = s match
      case Space.Empty => "op_empty"
      case Space.Mention(sm) => s"op_input(${atom(sm.s)})"
      case Space.Call(r, refs, mentions) =>
        s"op_call(${atom(r.s)},${list(refs.map(pathTerm))},${list(mentions.map(emitSpace))})"
      case Space.Singleton(p) => s"op_singleton(${pathTerm(p)})"
      case Space.Literal(sv) =>
        val digest = spaceDigest(sv)
        literalConstants.getOrElseUpdate(digest, sv)
        s"op_literal(${atom(digest)})"
      case Space.Union(a, b) => s"op_union(${emitSpace(a)},${emitSpace(b)})"
      case Space.Intersection(a, b) => s"op_intersection(${emitSpace(a)},${emitSpace(b)})"
      case Space.Subtraction(a, b) => s"op_diff(${emitSpace(a)},${emitSpace(b)})"
      case Space.Restriction(a, b) => s"op_restriction(${emitSpace(a)},${emitSpace(b)})"
      case Space.Raffination(a, b) => s"op_raffination(${emitSpace(a)},${emitSpace(b)})"
      case Space.Composition(a, b) => s"op_product(${emitSpace(a)},${emitSpace(b)})"
      case Space.Iteration(src, symbol, rest, templates) =>
        s"op_iter(${emitSpace(src)},${atom(symbol.s)},${atom(rest.s)},${emitSpace(templates)})"
      case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
        s"op_fold(${emitSpace(src)},${pathTerm(initial)},${atom(acc.s)},${atom(symbol.s)},${atom(rest.s)},${emitSpace(templates)},${pathTerm(update)})"
      case Space.Fixpoint(initial, variable, step) if fixpointIdentityStep(variable, step) =>
        emitSpace(initial)
      case Space.Fixpoint(initial, variable, step) if fixpointTailClosureStep(variable, step) =>
        s"op_tails_closure(${emitSpace(initial)})"
      case Space.Fixpoint(initial, variable, step) =>
        s"op_fixpoint(${emitSpace(initial)},${atom(variable.s)},${emitSpace(step)})"
      case Space.Wrap(src, p) => s"op_wrap(${emitSpace(src)},${pathTerm(p)})"
      case Space.Unwrap(src, p) => s"op_unwrap(${emitSpace(src)},${pathTerm(p)})"
      case Space.TailsUnion(src) => s"op_tails_union(${emitSpace(src)})"
      case Space.TailsIntersection(src) => s"op_tails_intersection(${emitSpace(src)})"
      case Space.PrefixClosure(src) => s"op_prefix_closure(${emitSpace(src)})"
      case Space.SuffixClosure(src) => s"op_suffix_closure(${emitSpace(src)})"
      case Space.TailsClosure(src) => s"op_tails_closure(${emitSpace(src)})"
      case Space.GroundedPS(p, _) => s"op_grounded_ps(${pathTerm(p)})"
      case Space.GroundedSS(src, _) => s"op_grounded_ss(${emitSpace(src)})"
      case Space.Range(src, start, end) => s"op_range(${emitSpace(src)},${intTerm(start)},${intTerm(end)})"

    private def pathTerm(p: morkl.Path): String = p match
      case morkl.Path.Deref(pr) => s"path_ref(${atom(pr.s)})"
      case morkl.Path.Constant(pi) =>
        val digest = pathDigest(pi)
        pathConstants.getOrElseUpdate(digest, pi)
        s"path_lit(${atom(digest)})"
      case morkl.Path.Concat(l, r) => s"path_concat(${pathTerm(l)},${pathTerm(r)})"
      case morkl.Path.GroundedPP(p, _) => s"path_grounded_pp(${pathTerm(p)})"
      case morkl.Path.GroundedSP(s, _) => s"path_grounded_sp(${emitSpace(s)})"

    private def spaceKey(s: Space): String =
      s.show

    private def mentionOf(s: Space, variable: SpaceMention): Boolean = s match
      case Space.Mention(sm) => sm == variable || sm.s == variable.s
      case _ => false

    private def tailUnionOf(s: Space, variable: SpaceMention): Boolean = s match
      case Space.TailsUnion(src) => mentionOf(src, variable)
      case _ => false

    private def fixpointIdentityStep(variable: SpaceMention, step: Space): Boolean =
      mentionOf(step, variable)

    private def fixpointTailClosureStep(variable: SpaceMention, step: Space): Boolean = step match
      case Space.TailsUnion(src) => mentionOf(src, variable)
      case Space.Union(left, right) =>
        (mentionOf(left, variable) && tailUnionOf(right, variable)) ||
          (tailUnionOf(left, variable) && mentionOf(right, variable))
      case _ => false

    private def list(xs: Iterable[String]): String =
      xs.toVector.reverse.foldLeft("nil")((tail, item) => s"cons($item,$tail)")

  private def renderStructuralFol(c: OpenProgramCase, body: Space): String =
    val emitter = FolDagEmitter()
    val root = emitter.emitSpace(body)
    val constantAxioms = emitter.constantAxioms
    s"""% Generated by morkl.generateOpenProgramProofArtifacts
       |% ${c.name}: axiomatized structural full-program schema consistency
       |% ${c.note}
       |%
       |% This structural ATP tier emits the generated full MORKL program as a DAG
       |% of first-order terms and checks that it is well formed under the declared
       |% backend membership contracts. Source/backend agreement is axiomatized per
       |% constructor below; consequently the final theorem is a schema-consistency
       |% check, not an independent proof about the Scala implementations. Iter is modeled with
       |% an explicit binding environment; Range is modeled as source membership plus
       |% ordered-rank selection. The remaining hard operators are named explicitly
       |% as shared semantic predicates rather than hidden behind bounded enumeration.
       |% General Fixpoint is exposed as the union-saturating base-or-step equation
       |% over the structural environment; leastness/positivity remains a proof
       |% obligation for future lowering-specific lemmas rather than a runtime cap.
       |
       |${structuralFolPrelude}
       |
       |$constantAxioms
       |
       |${emitter.definitionAxioms}
       |
       |fof(program_root, axiom, program_root = $root).
       |
       |fof(conj, conjecture,
       |  ! [P] : (
       |    (source_mem(P,program_root) <=> optimized_source_mem(P,program_root)) &
       |    (source_mem(P,program_root) <=> trie_mem(P,program_root)) &
       |    (source_mem(P,program_root) <=> zipper_mem(P,program_root)) &
       |    (source_mem(P,program_root) <=> graph_mem(P,program_root))
       |  )
       |).
       |""".stripMargin

  private def structuralFolPrelude: String =
    val backends = Vector("source", "optimized_source", "trie", "zipper", "graph")
    val backendAxioms = backends.map(backendStructuralAxioms).mkString("\n")
    val equivalenceAxioms = backends.filterNot(_ == "source").map(backendEquivalenceAxioms).mkString("\n")
    s"""% Abstract path and input interpretation.
       |fof(path_ref_sem, axiom, ! [P,R] : (path_matches(P,path_ref(R)) <=> path_ref_mem(P,R))).
       |fof(path_concat_sem, axiom,
       |  ! [P,A,B] : (path_matches(P,path_concat(A,B)) <=>
       |    ? [Q,R] : (path_matches(Q,A) & path_matches(R,B) & p_append(Q,R,P)))).
       |fof(path_grounded_pp_sem, axiom, ! [P,Q] : (path_matches(P,path_grounded_pp(Q)) <=> grounded_path_path_sem(P,Q))).
       |fof(path_grounded_sp_sem, axiom, ! [P,S] : (path_matches(P,path_grounded_sp(S)) <=> grounded_space_path_sem(P,S))).
       |
       |fof(path_item_sem, axiom, ! [P,I] : (path_matches(P,path_item(I)) <=> P = cons(I,nil))).
       |fof(path_env_lit_sem, axiom, ! [P,X,Env] : (path_env_matches(P,path_lit(X),Env) <=> path_matches(P,path_lit(X)))).
       |fof(path_env_item_sem, axiom, ! [P,I,Env] : (path_env_matches(P,path_item(I),Env) <=> P = cons(I,nil))).
       |fof(path_env_concat_sem, axiom,
       |  ! [P,A,B,Env] : (path_env_matches(P,path_concat(A,B),Env) <=>
       |    ? [Q,R] : (path_env_matches(Q,A,Env) & path_env_matches(R,B,Env) & p_append(Q,R,P)))).
       |fof(path_env_grounded_pp_sem, axiom, ! [P,Q,Env] : (path_env_matches(P,path_grounded_pp(Q),Env) <=> grounded_path_path_env_sem(P,Q,Env))).
       |fof(path_env_grounded_sp_sem, axiom, ! [P,S,Env] : (path_env_matches(P,path_grounded_sp(S),Env) <=> grounded_space_path_env_sem(P,S,Env))).
       |
       |fof(path_lookup_hit, axiom,
       |  ! [P,R,Q,Outer] : (path_lookup_matches(P,R,env_path(R,Q,Outer)) <=> path_env_matches(P,Q,Outer))).
       |fof(path_lookup_miss_path, axiom,
       |  ! [P,R,Other,Q,Outer] : (R != Other => (path_lookup_matches(P,R,env_path(Other,Q,Outer)) <=> path_lookup_matches(P,R,Outer)))).
       |fof(path_lookup_skip_space, axiom,
       |  ! [P,R,Name,S,Outer] : (path_lookup_matches(P,R,env_space(Name,S,Outer)) <=> path_lookup_matches(P,R,Outer))).
       |fof(path_lookup_empty, axiom, ! [P,R] : (path_lookup_matches(P,R,env_empty) <=> path_ref_mem(P,R))).
       |fof(path_env_ref_sem, axiom, ! [P,R,Env] : (path_env_matches(P,path_ref(R),Env) <=> path_lookup_matches(P,R,Env))).
       |
       |% Range is order-sensitive.  The structural FOL layer exposes the exact
       |% shape of the implementation contract: membership in the source, a rank in
       |% that ordered source, normalized public bounds, and a half-open selected
       |% interval.  The rank/count/bounds relations are the remaining ordered-trie
       |% proof hooks; they are shared by all backends.
       |fof(range_select_rank, axiom,
       |  ! [P,A,Env,Start,End] : (range_select_env(P,A,Env,Start,End) <=>
       |    ? [K,N,Lo,Hi] : (
       |      range_rank_env(P,A,Env,K) &
       |      range_count_env(A,Env,N) &
       |      range_bounds(N,Start,End,Lo,Hi) &
       |      int_le(Lo,K) &
       |      int_lt(K,Hi)))).
       |fof(range_bounds_full_sentinel, axiom, ! [N] : range_bounds(N,n0,n0,n0,N)).
       |fof(range_bounds_empty_one_one, axiom, ! [N] : range_bounds(N,n1,n1,n0,n0)).
       |fof(range_bounds_functional, axiom,
       |  ! [N,Start,End,Lo1,Hi1,Lo2,Hi2] : (
       |    (range_bounds(N,Start,End,Lo1,Hi1) & range_bounds(N,Start,End,Lo2,Hi2)) =>
       |    (Lo1 = Lo2 & Hi1 = Hi2))).
       |fof(int_le_excludes_reverse_lt, axiom, ! [A,B] : (int_le(A,B) => ~int_lt(B,A))).
       |
       |% Shared semantic frontiers for operators whose full FOL expansion still
       |% needs grounded host functions, folds, or least-fixed-point theory. They
       |% are per-operator, so generated certificates show exactly where stronger
       |% lemmas remain to be added.
       |fof(call_backend_shared, axiom, ! [P,R,Refs,Args] : (
       |  source_mem(P,op_call(R,Refs,Args)) <=>
       |  optimized_source_mem(P,op_call(R,Refs,Args)))).
       |fof(call_trie_shared, axiom, ! [P,R,Refs,Args] : (
       |  source_mem(P,op_call(R,Refs,Args)) <=> trie_mem(P,op_call(R,Refs,Args)))).
       |fof(call_zipper_shared, axiom, ! [P,R,Refs,Args] : (
       |  source_mem(P,op_call(R,Refs,Args)) <=> zipper_mem(P,op_call(R,Refs,Args)))).
       |fof(call_graph_shared, axiom, ! [P,R,Refs,Args] : (
       |  source_mem(P,op_call(R,Refs,Args)) <=> graph_mem(P,op_call(R,Refs,Args)))).
       |
       |$backendAxioms
       |
       |% Per-constructor backend/source agreement axioms. They make the generated
       |% whole-program theorem a contract-composition consistency check; they are
       |% not independently derived implementation-equivalence lemmas.
       |$equivalenceAxioms
       |""".stripMargin

  private def backendStructuralAxioms(backend: String): String =
    val mem = s"${backend}_mem"
    val env = s"${backend}_env_mem"
    val lookup = s"${backend}_space_lookup_mem"
    def ax(name: String, formula: String): String =
      s"fof(${backend}_${name}, axiom,\n  $formula)."
    val root = Vector(
      ax("empty", s"! [P] : (~ $mem(P,op_empty))"),
      ax("input", s"! [P,X] : ($mem(P,op_input(X)) <=> input_mem(P,X))"),
      ax("literal", s"! [P,X] : ($mem(P,op_literal(X)) <=> literal_mem(P,X))"),
      ax("singleton", s"! [P,Q] : ($mem(P,op_singleton(Q)) <=> path_matches(P,Q))"),
      ax("union", s"! [P,A,B] : ($mem(P,op_union(A,B)) <=> ($mem(P,A) | $mem(P,B)))"),
      ax("intersection", s"! [P,A,B] : ($mem(P,op_intersection(A,B)) <=> ($mem(P,A) & $mem(P,B)))"),
      ax("diff", s"! [P,A,B] : ($mem(P,op_diff(A,B)) <=> ($mem(P,A) & ~ $mem(P,B)))"),
      ax("restriction", s"! [P,A,B] : ($mem(P,op_restriction(A,B)) <=> ($mem(P,A) & ? [Q] : ($mem(Q,B) & p_prefix(Q,P))))"),
      ax("raffination", s"! [P,A,B] : ($mem(P,op_raffination(A,B)) <=> ($mem(P,A) & ~ ? [Q] : ($mem(Q,B) & p_prefix(Q,P))))"),
      ax("product", s"! [P,A,B] : ($mem(P,op_product(A,B)) <=> ? [Q,R] : ($mem(Q,A) & $mem(R,B) & p_append(Q,R,P)))"),
      ax("wrap", s"! [P,A,Q] : ($mem(P,op_wrap(A,Q)) <=> ? [Prefix,Tail] : (path_matches(Prefix,Q) & $mem(Tail,A) & p_append(Prefix,Tail,P)))"),
      ax("unwrap", s"! [P,A,Q] : ($mem(P,op_unwrap(A,Q)) <=> ? [Prefix,Full] : (path_matches(Prefix,Q) & p_append(Prefix,P,Full) & $mem(Full,A)))"),
      ax("tails_union", s"! [P,A] : ($mem(P,op_tails_union(A)) <=> ? [I] : $mem(cons(I,P),A))"),
      ax("tails_intersection", s"! [P,A] : ($mem(P,op_tails_intersection(A)) <=> ((? [I,Q] : $mem(cons(I,Q),A)) & ! [I] : ((? [Q] : $mem(cons(I,Q),A)) => $mem(cons(I,P),A))))"),
      ax("prefix_closure", s"! [P,A] : ($mem(P,op_prefix_closure(A)) <=> (P != nil & ? [Q] : ($mem(Q,A) & p_prefix(P,Q))))"),
      ax("suffix_closure", s"! [P,A] : ($mem(P,op_suffix_closure(A)) <=> (P != nil & ? [Q] : ($mem(Q,A) & p_suffix(P,Q))))"),
      ax("tails_closure", s"! [P,A] : ($mem(P,op_tails_closure(A)) <=> (((P = nil) & ? [Q] : $mem(Q,A)) | (P != nil & ? [Q] : ($mem(Q,A) & p_suffix(P,Q)))))"),
      ax("iter", s"! [P,A,Sym,Rest,Body] : ($mem(P,op_iter(A,Sym,Rest,Body)) <=> $env(P,op_iter(A,Sym,Rest,Body),env_empty))"),
      ax("fold", s"! [P,A,Initial,Acc,Sym,Rest,Body,Update] : ($mem(P,op_fold(A,Initial,Acc,Sym,Rest,Body,Update)) <=> fold_sem(P,A,Initial,Acc,Sym,Rest,Body,Update))"),
      ax("fixpoint", s"! [P,A,Var,Step] : ($mem(P,op_fixpoint(A,Var,Step)) <=> $env(P,op_fixpoint(A,Var,Step),env_empty))"),
      ax("grounded_ps", s"! [P,Q] : ($mem(P,op_grounded_ps(Q)) <=> grounded_ps_sem(P,Q))"),
      ax("grounded_ss", s"! [P,A] : ($mem(P,op_grounded_ss(A)) <=> grounded_ss_sem(P,A))"),
      ax("range", s"! [P,A,Start,End] : ($mem(P,op_range(A,Start,End)) <=> $env(P,op_range(A,Start,End),env_empty))"),
    )
    val envAxioms = Vector(
      ax("space_lookup_hit", s"! [P,X,S,Outer] : ($lookup(P,X,env_space(X,S,Outer)) <=> $env(P,S,Outer))"),
      ax("space_lookup_miss_space", s"! [P,X,Other,S,Outer] : (X != Other => ($lookup(P,X,env_space(Other,S,Outer)) <=> $lookup(P,X,Outer)))"),
      ax("space_lookup_skip_path", s"! [P,X,R,Q,Outer] : ($lookup(P,X,env_path(R,Q,Outer)) <=> $lookup(P,X,Outer))"),
      ax("space_lookup_empty", s"! [P,X] : ($lookup(P,X,env_empty) <=> input_mem(P,X))"),
      ax("env_empty", s"! [P,Env] : (~ $env(P,op_empty,Env))"),
      ax("env_input", s"! [P,X,Env] : ($env(P,op_input(X),Env) <=> $lookup(P,X,Env))"),
      ax("env_literal", s"! [P,X,Env] : ($env(P,op_literal(X),Env) <=> literal_mem(P,X))"),
      ax("env_singleton", s"! [P,Q,Env] : ($env(P,op_singleton(Q),Env) <=> path_env_matches(P,Q,Env))"),
      ax("env_union", s"! [P,A,B,Env] : ($env(P,op_union(A,B),Env) <=> ($env(P,A,Env) | $env(P,B,Env)))"),
      ax("env_intersection", s"! [P,A,B,Env] : ($env(P,op_intersection(A,B),Env) <=> ($env(P,A,Env) & $env(P,B,Env)))"),
      ax("env_diff", s"! [P,A,B,Env] : ($env(P,op_diff(A,B),Env) <=> ($env(P,A,Env) & ~ $env(P,B,Env)))"),
      ax("env_restriction", s"! [P,A,B,Env] : ($env(P,op_restriction(A,B),Env) <=> ($env(P,A,Env) & ? [Q] : ($env(Q,B,Env) & p_prefix(Q,P))))"),
      ax("env_raffination", s"! [P,A,B,Env] : ($env(P,op_raffination(A,B),Env) <=> ($env(P,A,Env) & ~ ? [Q] : ($env(Q,B,Env) & p_prefix(Q,P))))"),
      ax("env_product", s"! [P,A,B,Env] : ($env(P,op_product(A,B),Env) <=> ? [Q,R] : ($env(Q,A,Env) & $env(R,B,Env) & p_append(Q,R,P)))"),
      ax("env_wrap", s"! [P,A,Q,Env] : ($env(P,op_wrap(A,Q),Env) <=> ? [Prefix,Tail] : (path_env_matches(Prefix,Q,Env) & $env(Tail,A,Env) & p_append(Prefix,Tail,P)))"),
      ax("env_unwrap", s"! [P,A,Q,Env] : ($env(P,op_unwrap(A,Q),Env) <=> ? [Prefix,Full] : (path_env_matches(Prefix,Q,Env) & p_append(Prefix,P,Full) & $env(Full,A,Env)))"),
      ax("env_tails_union", s"! [P,A,Env] : ($env(P,op_tails_union(A),Env) <=> ? [I] : $env(cons(I,P),A,Env))"),
      ax("env_tails_intersection", s"! [P,A,Env] : ($env(P,op_tails_intersection(A),Env) <=> ((? [I,Q] : $env(cons(I,Q),A,Env)) & ! [I] : ((? [Q] : $env(cons(I,Q),A,Env)) => $env(cons(I,P),A,Env))))"),
      ax("env_prefix_closure", s"! [P,A,Env] : ($env(P,op_prefix_closure(A),Env) <=> (P != nil & ? [Q] : ($env(Q,A,Env) & p_prefix(P,Q))))"),
      ax("env_suffix_closure", s"! [P,A,Env] : ($env(P,op_suffix_closure(A),Env) <=> (P != nil & ? [Q] : ($env(Q,A,Env) & p_suffix(P,Q))))"),
      ax("env_tails_closure", s"! [P,A,Env] : ($env(P,op_tails_closure(A),Env) <=> (((P = nil) & ? [Q] : $env(Q,A,Env)) | (P != nil & ? [Q] : ($env(Q,A,Env) & p_suffix(P,Q)))))"),
      ax("env_iter", s"! [P,A,Sym,Rest,Body,Env] : ($env(P,op_iter(A,Sym,Rest,Body),Env) <=> ? [I] : ((? [Q] : $env(cons(I,Q),A,Env)) & $env(P,Body,env_space(Rest,op_child_env(A,I,Env),env_path(Sym,path_item(I),Env)))))"),
      ax("env_child", s"! [P,A,I,Captured,Env] : ($env(P,op_child_env(A,I,Captured),Env) <=> $env(cons(I,P),A,Captured))"),
      ax("env_fold", s"! [P,A,Initial,Acc,Sym,Rest,Body,Update,Env] : ($env(P,op_fold(A,Initial,Acc,Sym,Rest,Body,Update),Env) <=> fold_env_sem(P,A,Initial,Acc,Sym,Rest,Body,Update,Env))"),
      ax("env_fixpoint", s"! [P,A,Var,Step,Env] : ($env(P,op_fixpoint(A,Var,Step),Env) <=> ($env(P,A,Env) | $env(P,Step,env_space(Var,op_fixpoint(A,Var,Step),Env))))"),
      ax("env_grounded_ps", s"! [P,Q,Env] : ($env(P,op_grounded_ps(Q),Env) <=> grounded_ps_env_sem(P,Q,Env))"),
      ax("env_grounded_ss", s"! [P,A,Env] : ($env(P,op_grounded_ss(A),Env) <=> grounded_ss_env_sem(P,A,Env))"),
      ax("env_range", s"! [P,A,Start,End,Env] : ($env(P,op_range(A,Start,End),Env) <=> ($env(P,A,Env) & range_select_env(P,A,Env,Start,End)))"),
    )
    (root ++ envAxioms).mkString("\n")

  private def backendEquivalenceAxioms(backend: String): String =
    val mem = s"${backend}_mem"
    def ax(name: String, args: String): String =
      s"fof(${backend}_${name}_source_equiv, axiom,\n  ! [$args] : (source_mem(P,${nameTerm(name)}) <=> $mem(P,${nameTerm(name)})))."
    val specs = Vector(
      "empty" -> "P",
      "input" -> "P,X",
      "literal" -> "P,X",
      "singleton" -> "P,Q",
      "union" -> "P,A,B",
      "intersection" -> "P,A,B",
      "diff" -> "P,A,B",
      "restriction" -> "P,A,B",
      "raffination" -> "P,A,B",
      "product" -> "P,A,B",
      "wrap" -> "P,A,Q",
      "unwrap" -> "P,A,Q",
      "tails_union" -> "P,A",
      "tails_intersection" -> "P,A",
      "prefix_closure" -> "P,A",
      "suffix_closure" -> "P,A",
      "tails_closure" -> "P,A",
      "iter" -> "P,A,Sym,Rest,Body",
      "fold" -> "P,A,Initial,Acc,Sym,Rest,Body,Update",
      "fixpoint" -> "P,A,Var,Step",
      "grounded_ps" -> "P,Q",
      "grounded_ss" -> "P,A",
      "range" -> "P,A,Start,End",
      "call" -> "P,R,Refs,Args",
    )
    specs.map(ax).mkString("\n")

  private def nameTerm(name: String): String = name match
    case "empty" => "op_empty"
    case "input" => "op_input(X)"
    case "literal" => "op_literal(X)"
    case "singleton" => "op_singleton(Q)"
    case "union" => "op_union(A,B)"
    case "intersection" => "op_intersection(A,B)"
    case "diff" => "op_diff(A,B)"
    case "restriction" => "op_restriction(A,B)"
    case "raffination" => "op_raffination(A,B)"
    case "product" => "op_product(A,B)"
    case "wrap" => "op_wrap(A,Q)"
    case "unwrap" => "op_unwrap(A,Q)"
    case "tails_union" => "op_tails_union(A)"
    case "tails_intersection" => "op_tails_intersection(A)"
    case "prefix_closure" => "op_prefix_closure(A)"
    case "suffix_closure" => "op_suffix_closure(A)"
    case "tails_closure" => "op_tails_closure(A)"
    case "iter" => "op_iter(A,Sym,Rest,Body)"
    case "fold" => "op_fold(A,Initial,Acc,Sym,Rest,Body,Update)"
    case "fixpoint" => "op_fixpoint(A,Var,Step)"
    case "grounded_ps" => "op_grounded_ps(Q)"
    case "grounded_ss" => "op_grounded_ss(A)"
    case "range" => "op_range(A,Start,End)"
    case "call" => "op_call(R,Refs,Args)"

  private def atom(value: String): String =
    val bytes = value.getBytes(StandardCharsets.UTF_8).map("%02x".format(_)).mkString
    "a" + bytes

  private def intTerm(value: Int): String =
    if value >= 0 then s"n$value" else s"m${-value}"

  private def pathDigest(path: PathValue): String =
    path.items.map(_.show).mkString(".")

  private def spaceDigest(space: SpaceValue): String =
    space.paths.toVector.sortBy(_.show).map(_.show).mkString("|")

  private def folPath(path: PathValue): String =
    path.items.reverseIterator.foldLeft("nil")((tail, item) => s"cons(${atom(item.show)},$tail)")

  private def slidingPuzzleAllStates(n: Int): SpaceValue =
    SpaceValue(permutations((0 until n * n).toVector).map(SlidingPuzzleExample.pathState(n, _)).toSet)

  def build(c: OpenProgramCase): (Vector[OpenProgramRelation], Vector[OpenProgramSkip]) =
    val relations = Vector.newBuilder[OpenProgramRelation]
    val skips = Vector.newBuilder[OpenProgramSkip]

    def attempt(relation: String, lhsLabel: String, rhsLabel: String, note: String)(lhs: => Space)(rhs: => Space): Unit =
      try
        val lhsSpace = lhs
        val rhsSpace = rhs
        val ctx = contextFor(c, lhsSpace, rhsSpace)
        relations += OpenProgramRelation(
          c.name,
          relation,
          lhsLabel,
          rhsLabel,
          translate(lhsSpace),
          translate(rhsSpace),
          ctx,
          Vector(note, c.note).filter(_.nonEmpty).mkString(" "),
        )
      catch
        case e: Throwable =>
          skips += OpenProgramSkip(c.name, relation, s"${e.getClass.getSimpleName}: ${Option(e.getMessage).getOrElse("")}")

    println(s"  expanding ${c.name}")
    val expanded = expandedRoutine(c)
    println(s"  expanded ${c.name}")
    def enabled(name: String): Boolean =
      val ok = c.relations(name)
      if !ok then skips += OpenProgramSkip(c.name, name, "disabled for this proof case; current structural source/graph bias would make this obligation too large")
      ok

    if enabled(OpenProgramCase.SpaceOptimized) then
      println(s"  ${c.name}: ${OpenProgramCase.SpaceOptimized}")
      attempt(OpenProgramCase.SpaceOptimized, "expanded_source", "source_optimizer", "Expanded source equals source optimizer for all bounded symbolic inputs.") {
        expanded.body
      } {
        inlineFully(Supercompiler.compile(c.routine, ctx = context(c), buildGraph = false).routine.body, context(c))
      }
    if enabled(OpenProgramCase.RawGraphRoundTrip) then
      println(s"  ${c.name}: ${OpenProgramCase.RawGraphRoundTrip}")
      attempt(OpenProgramCase.RawGraphRoundTrip, "expanded_source", "raw_graph_untranspile", "Expanded source equals raw graph transpile/untranspile for all bounded symbolic inputs.") {
        expanded.body
      } {
        graphRoundTrip(expanded, optimizeGraph = false)
      }
    if enabled(OpenProgramCase.OptimizedGraphRoundTrip) then
      println(s"  ${c.name}: ${OpenProgramCase.OptimizedGraphRoundTrip}")
      attempt(OpenProgramCase.OptimizedGraphRoundTrip, "expanded_source", "optimized_graph_untranspile", "Expanded source equals optimized graph transpile/untranspile for all bounded symbolic inputs.") {
        expanded.body
      } {
        graphRoundTrip(expanded, optimizeGraph = true)
      }

    if c.name == "sliding-puzzle-2x2-full-open" then
      val stateA = SlidingPuzzleExample.pathState(2, Vector(0, 1, 2, 3))
      val stateB = SlidingPuzzleExample.pathState(2, Vector(1, 0, 2, 3))
      val stateC = SlidingPuzzleExample.pathState(2, Vector(2, 1, 0, 3))
      val witnesses = Vector(
        ("bounded_witness_a_open", stateA, SpaceValue(stateB, stateC), "A=TL.1.2.3 has exact bounded output {TR.1.2.3,BL.2.1.3}; exercises R,D."),
        ("bounded_witness_b_open", stateB, SpaceValue(stateA), "B=TR.1.2.3 has exact bounded output {TL.1.2.3}; exercises L."),
        ("bounded_witness_c_open", stateC, SpaceValue(stateA), "C=BL.2.1.3 has exact bounded output {TL.1.2.3}; exercises U."),
      )
      for (name, input, expected, note) <- witnesses do
        val concrete = subs(expanded.body)(spost = {
          case Space.Mention(sm) if sm.s == "states" => Space.Literal(SpaceValue(input))
        })
        attempt(name, s"expanded_source(${input.show})", s"exact_expected(${expected.pretty})",
          s"Bounded translated non-vacuity certificate. $note")(concrete)(Space.Literal(expected))

    relations.result() -> skips.result()

  private case class TranslateEnv(pathVars: Map[PathRef, PA.SpaceExpr] = Map.empty,
                                  spaceVars: Map[SpaceMention, PA.SpaceExpr] = Map.empty)

  private def translationCacheTag(kind: String, syntax: Space, env: TranslateEnv): String =
    val md = MessageDigest.getInstance("SHA-256")
    val charBuffer = Array.ofDim[Byte](8192)
    def add(value: String): Unit =
      // Length-framed UTF-16 code units avoid allocating a second full byte
      // array for a potentially large Raw SMT term.
      md.update((value.length >>> 24).toByte)
      md.update((value.length >>> 16).toByte)
      md.update((value.length >>> 8).toByte)
      md.update(value.length.toByte)
      var offset = 0
      while offset < value.length do
        val chars = math.min(value.length - offset, charBuffer.length / 2)
        var i = 0
        while i < chars do
          val ch = value.charAt(offset + i)
          charBuffer(2 * i) = (ch.toInt >>> 8).toByte
          charBuffer(2 * i + 1) = ch.toByte
          i += 1
        md.update(charBuffer, 0, chars * 2)
        offset += chars

    def addBinding(expr: PA.SpaceExpr): Unit = expr match
      case PA.Var(name) =>
        add("binding-var")
        add(name)
      case PA.Raw(term, names) =>
        add("binding-raw")
        add(term)
        val orderedNames = names.toVector.sorted
        add(orderedNames.length.toString)
        orderedNames.foreach(add)
      case PA.Const(paths) =>
        add("binding-const")
        val ordered = paths.sortWith(comparePathTuples(_, _) < 0)
        add(ordered.length.toString)
        ordered.foreach { path =>
          add(path.length.toString)
          path.foreach(add)
        }
      case other =>
        throw IllegalArgumentException(
          s"open-proof binder environment contains unsupported ${other.getClass.getSimpleName}; expected a symbolic variable, raw binding, or singleton constant")

    def addPath(path: morkl.Path): Unit = path match
      case morkl.Path.Deref(ref) =>
        add("path-deref")
        add(ref.s)
      case morkl.Path.Constant(value) =>
        add("path-constant")
        add(value.items.length.toString)
        value.items.foreach(item => add(item.show))
      case morkl.Path.Concat(left, right) =>
        add("path-concat")
        addPath(left)
        addPath(right)
      case morkl.Path.GroundedPP(_, _) | morkl.Path.GroundedSP(_, _) =>
        throw UnsupportedOperationException("grounded path expression is not open-proof digestible")

    // Feed the syntax tree directly into the digest. Calling `Space.show` here
    // materialized the complete expanded puzzle program as one giant String;
    // that transient copy alone exhausted the documented 1.5 GiB generator
    // heap. The length-framed traversal is equally deterministic and keeps
    // peak memory proportional to recursion depth rather than output size.
    def addSpace(space: Space): Unit = space match
      case Space.Empty => add("space-empty")
      case Space.Call(routine, refs, mentions) =>
        add("space-call")
        add(routine.s)
        add(refs.length.toString)
        refs.foreach(addPath)
        add(mentions.length.toString)
        mentions.foreach(addSpace)
      case Space.Mention(mention) =>
        add("space-mention")
        add(mention.s)
      case Space.Singleton(path) =>
        add("space-singleton")
        addPath(path)
      case Space.Literal(value) =>
        add("space-literal")
        val paths = value.paths.toVector.map(pathTuple).sortWith(comparePathTuples(_, _) < 0)
        add(paths.length.toString)
        paths.foreach { path =>
          add(path.length.toString)
          path.foreach(add)
        }
      case Space.Union(left, right) =>
        add("space-union"); addSpace(left); addSpace(right)
      case Space.Intersection(left, right) =>
        add("space-intersection"); addSpace(left); addSpace(right)
      case Space.Subtraction(left, right) =>
        add("space-subtraction"); addSpace(left); addSpace(right)
      case Space.Restriction(left, right) =>
        add("space-restriction"); addSpace(left); addSpace(right)
      case Space.Raffination(left, right) =>
        add("space-raffination"); addSpace(left); addSpace(right)
      case Space.Composition(left, right) =>
        add("space-composition"); addSpace(left); addSpace(right)
      case Space.Iteration(source, symbol, rest, templates) =>
        add("space-iteration")
        addSpace(source)
        add(symbol.s)
        add(rest.s)
        addSpace(templates)
      case Space.Fold(_, _, _, _, _, _, _) =>
        throw UnsupportedOperationException("Fold is not open-proof digestible because it is not translatable")
      case Space.Fixpoint(initial, variable, step) =>
        add("space-fixpoint")
        addSpace(initial)
        add(variable.s)
        addSpace(step)
      case Space.Wrap(source, prefix) =>
        add("space-wrap"); addSpace(source); addPath(prefix)
      case Space.Unwrap(source, prefix) =>
        add("space-unwrap"); addSpace(source); addPath(prefix)
      case Space.TailsUnion(source) =>
        add("space-tails-union"); addSpace(source)
      case Space.TailsIntersection(source) =>
        add("space-tails-intersection"); addSpace(source)
      case Space.PrefixClosure(source) =>
        add("space-prefix-closure"); addSpace(source)
      case Space.SuffixClosure(source) =>
        add("space-suffix-closure"); addSpace(source)
      case Space.TailsClosure(source) =>
        add("space-tails-closure"); addSpace(source)
      case Space.Range(source, start, end) =>
        add("space-range"); add(start.toString); add(end.toString); addSpace(source)
      case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) =>
        throw UnsupportedOperationException("grounded space expression is not open-proof digestible")

    add("open-space-digest-v1")
    add(kind)
    addSpace(syntax)
    val pathBindings = env.pathVars.toVector.sortBy(_._1.s)
    add(pathBindings.length.toString)
    pathBindings.foreach { (name, value) =>
      add("path")
      add(name.s)
      addBinding(value)
    }
    val spaceBindings = env.spaceVars.toVector.sortBy(_._1.s)
    add(spaceBindings.length.toString)
    spaceBindings.foreach { (name, value) =>
      add("space")
      add(name.s)
      addBinding(value)
    }
    java.util.HexFormat.of().formatHex(md.digest())

  private def translate(s: Space): PA.SpaceExpr =
    translateSpace(s, TranslateEnv())

  private def translatePath(p: morkl.Path, env: TranslateEnv): PA.SpaceExpr = p match
    case morkl.Path.Deref(pr) =>
      env.pathVars.getOrElse(pr, PA.Var(s"P_${safe(pr.s)}"))
    case morkl.Path.Constant(pi) =>
      PA.Const(Vector(pathTuple(pi)))
    case morkl.Path.Concat(l, r) =>
      PA.Product(translatePath(l, env), translatePath(r, env))
    case morkl.Path.GroundedPP(_, _) | morkl.Path.GroundedSP(_, _) =>
      throw UnsupportedOperationException(s"grounded path expression is not open-proof translatable: ${p.show}")

  private def translateSpace(s: Space, env: TranslateEnv): PA.SpaceExpr = s match
    case Space.Empty => PA.Empty
    case Space.Call(r, _, _) =>
      throw UnsupportedOperationException(s"routine call ${r.s} survived expansion")
    case Space.Mention(sm) =>
      env.spaceVars.getOrElse(sm, PA.Var(s"S_${safe(sm.s)}"))
    case Space.Singleton(p) =>
      translatePath(p, env)
    case Space.Literal(sv) =>
      PA.Const(sv.paths.toVector.map(pathTuple).sortWith(comparePathTuples(_, _) < 0))
    case Space.Union(x, y) =>
      PA.Union(translateSpace(x, env), translateSpace(y, env))
    case Space.Intersection(x, y) =>
      PA.Intersection(translateSpace(x, env), translateSpace(y, env))
    case Space.Subtraction(x, y) =>
      PA.Diff(translateSpace(x, env), translateSpace(y, env))
    case Space.Restriction(x, prefixes) =>
      PA.Restriction(translateSpace(x, env), translateSpace(prefixes, env))
    case Space.Raffination(x, prefixes) =>
      PA.Raffination(translateSpace(x, env), translateSpace(prefixes, env))
    case Space.Composition(x, y) =>
      PA.Product(translateSpace(x, env), translateSpace(y, env))
    case Space.Iteration(src, symbol, rest, templates) =>
      val source = translateSpace(src, env)
      PA.Iter(
        source,
        (head, tail) => translateSpace(templates, env.copy(
          pathVars = env.pathVars + (symbol -> head),
          spaceVars = env.spaceVars + (rest -> tail),
        )),
        label = safe(symbol.s),
        cacheTag = Some(translationCacheTag("iter", templates, env)),
      )
    case Space.Fold(_, _, _, _, _, _, _) =>
      throw UnsupportedOperationException("Fold is not yet in the open-program bounded proof translator")
    case Space.Fixpoint(initial, variable, step) =>
      PA.FixpointExpr(
        translateSpace(initial, env),
        state => translateSpace(step, env.copy(spaceVars = env.spaceVars + (variable -> state))),
        label = safe(variable.s),
        cacheTag = Some(translationCacheTag("fix", step, env)),
      )
    case Space.Wrap(src, p) =>
      PA.Product(translatePath(p, env), translateSpace(src, env))
    case Space.Unwrap(src, p) =>
      PA.UnwrapBy(translateSpace(src, env), translatePath(p, env))
    case Space.TailsUnion(src) =>
      PA.TailsUnion(translateSpace(src, env))
    case Space.TailsIntersection(src) =>
      PA.TailsIntersection(translateSpace(src, env))
    case Space.PrefixClosure(src) =>
      PA.PrefixClosure(translateSpace(src, env))
    case Space.SuffixClosure(src) =>
      PA.SuffixClosure(translateSpace(src, env))
    case Space.TailsClosure(src) =>
      PA.TailsClosure(translateSpace(src, env))
    case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) =>
      throw UnsupportedOperationException(s"grounded space expression is not open-proof translatable: ${s.show}")
    case Space.Range(x, start, end) =>
      PA.Range(translateSpace(x, env), start, end)

  private def expandedRoutine(c: OpenProgramCase): Routine =
    val r = c.routine
    val fixpointCtx = new PartialFunction[RoutinePtr, Routine]:
      override def isDefinedAt(rp: RoutinePtr): Boolean = rp == r.name || context(c).isDefinedAt(rp)
      override def apply(rp: RoutinePtr): Routine = if rp == r.name then r else context(c)(rp)
    val inlineCtx = new PartialFunction[RoutinePtr, Routine]:
      override def isDefinedAt(rp: RoutinePtr): Boolean = rp != r.name && context(c).isDefinedAt(rp)
      override def apply(rp: RoutinePtr): Routine = context(c)(rp)
    val lowered = Supercompiler.lowerFixpointCalls(r.body, fixpointCtx)
    val inlined = inlineFully(lowered, inlineCtx)
    val refs = freePathRefs(inlined).toVector.sortBy(_.s)
    val mentions = freeSpaceMentions(inlined).toVector.sortBy(_.s)
    Routine(RoutinePtr(s"${r.name.s}_expanded"), refs, mentions, inlined)

  private def inlineFully(s: Space, ctx: PartialFunction[RoutinePtr, Routine], maxRounds: Int = 32): Space =
    var current = s
    var round = 0
    while round < maxRounds do
      val next = Lower.inline(using ctx)(current)
      if next == current then return current
      current = next
      round += 1
    current

  private def graphRoundTrip(r: Routine, optimizeGraph: Boolean): Space =
    val unsupported = Supercompiler.backendUnsupported(r.body)
    if unsupported.nonEmpty then
      throw UnsupportedOperationException(s"graph backend unsupported: ${unsupported.mkString(", ")}")
    val raw = transpile(r)
    val graph = if optimizeGraph then optimize(raw) else raw
    val stack = mutable.Stack(new Array[morkl.Path | Space | Null](graph.nodes.length))
    untranspile(graph, stack)
    stack.top.last.asInstanceOf[Space]

  private def context(c: OpenProgramCase): PartialFunction[RoutinePtr, Routine] =
    c.defs.map(r => r.name -> r).toMap.lift.unlift

  private def contextFor(c: OpenProgramCase, lhs: Space, rhs: Space): PA.Ctx =
    // An explicit universe is an intentional proof bound. Pulling every literal
    // from the full expanded syntax back into it defeated focusing (notably for
    // the puzzle move table) and recreated the enormous Cartesian encoding.
    // Constants outside the bound correctly encode as the empty bit-vector.
    val explicit = c.explicitUniverse.map(closeUniverse)
    val explicitAlphabet = explicit.toVector.flatten.flatten.distinct
    val alphabet = (c.alphabet ++ explicitAlphabet ++ constantItems(lhs).toVector.sorted ++ constantItems(rhs).toVector.sorted)
      .filter(_.nonEmpty)
      .distinct
    PA.Ctx(alphabet, c.maxLen, explicit)

  private def pathTuple(pv: PathValue): PA.PathTuple =
    pv.items.map(_.show).toVector

  private def constantItems(s: Space): Set[String] =
    val out = Set.newBuilder[String]
    def recp(p: morkl.Path): Unit = p match
      case morkl.Path.Deref(_) => ()
      case morkl.Path.Constant(pi) => pi.items.foreach(item => out += item.show)
      case morkl.Path.Concat(l, r) =>
        recp(l)
        recp(r)
      case morkl.Path.GroundedPP(p, _) => recp(p)
      case morkl.Path.GroundedSP(s, _) => recs(s)
    def recs(x: Space): Unit = x match
      case Space.Empty | Space.Mention(_) => ()
      case Space.Call(_, refs, mentions) =>
        refs.foreach(recp)
        mentions.foreach(recs)
      case Space.Singleton(p) => recp(p)
      case Space.Literal(sv) => sv.paths.foreach(_.items.foreach(item => out += item.show))
      case Space.Union(a, b) =>
        recs(a)
        recs(b)
      case Space.Intersection(a, b) =>
        recs(a)
        recs(b)
      case Space.Subtraction(a, b) =>
        recs(a)
        recs(b)
      case Space.Restriction(a, b) =>
        recs(a)
        recs(b)
      case Space.Raffination(a, b) =>
        recs(a)
        recs(b)
      case Space.Composition(a, b) =>
        recs(a)
        recs(b)
      case Space.Iteration(src, _, _, templates) =>
        recs(src)
        recs(templates)
      case Space.Fold(src, initial, _, _, _, templates, update) =>
        recs(src)
        recp(initial)
        recs(templates)
        recp(update)
      case Space.Fixpoint(initial, _, step) =>
        recs(initial)
        recs(step)
      case Space.Wrap(src, p) =>
        recs(src)
        recp(p)
      case Space.Unwrap(src, p) =>
        recs(src)
        recp(p)
      case Space.TailsUnion(src) =>
        recs(src)
      case Space.TailsIntersection(src) =>
        recs(src)
      case Space.PrefixClosure(src) =>
        recs(src)
      case Space.SuffixClosure(src) =>
        recs(src)
      case Space.TailsClosure(src) =>
        recs(src)
      case Space.GroundedSS(src, _) =>
        recs(src)
      case Space.Range(src, _, _) =>
        recs(src)
      case Space.GroundedPS(p, _) => recp(p)
    recs(s)
    out.result()

  private def constantPaths(s: Space): Set[PathValue] =
    val out = Set.newBuilder[PathValue]
    def recp(p: morkl.Path): Unit = p match
      case morkl.Path.Deref(_) => ()
      case morkl.Path.Constant(pi) => out += pi
      case morkl.Path.Concat(l, r) =>
        recp(l)
        recp(r)
      case morkl.Path.GroundedPP(p, _) => recp(p)
      case morkl.Path.GroundedSP(s, _) => recs(s)
    def recs(x: Space): Unit = x match
      case Space.Empty | Space.Mention(_) => ()
      case Space.Call(_, refs, mentions) =>
        refs.foreach(recp)
        mentions.foreach(recs)
      case Space.Singleton(p) => recp(p)
      case Space.Literal(sv) => sv.paths.foreach(out += _)
      case Space.Union(a, b) =>
        recs(a)
        recs(b)
      case Space.Intersection(a, b) =>
        recs(a)
        recs(b)
      case Space.Subtraction(a, b) =>
        recs(a)
        recs(b)
      case Space.Restriction(a, b) =>
        recs(a)
        recs(b)
      case Space.Raffination(a, b) =>
        recs(a)
        recs(b)
      case Space.Composition(a, b) =>
        recs(a)
        recs(b)
      case Space.Iteration(src, _, _, templates) =>
        recs(src)
        recs(templates)
      case Space.Fold(src, initial, _, _, _, templates, update) =>
        recs(src)
        recp(initial)
        recs(templates)
        recp(update)
      case Space.Fixpoint(initial, _, step) =>
        recs(initial)
        recs(step)
      case Space.Wrap(src, p) =>
        recs(src)
        recp(p)
      case Space.Unwrap(src, p) =>
        recs(src)
        recp(p)
      case Space.TailsUnion(src) =>
        recs(src)
      case Space.TailsIntersection(src) =>
        recs(src)
      case Space.PrefixClosure(src) =>
        recs(src)
      case Space.SuffixClosure(src) =>
        recs(src)
      case Space.TailsClosure(src) =>
        recs(src)
      case Space.GroundedSS(src, _) =>
        recs(src)
      case Space.Range(src, _, _) =>
        recs(src)
      case Space.GroundedPS(p, _) => recp(p)
    recs(s)
    out.result()

  private def freeSpaceMentions(s: Space): Set[SpaceMention] =
    val out = Set.newBuilder[SpaceMention]
    def recp(p: morkl.Path, boundP: Set[PathRef], boundS: Set[SpaceMention]): Unit = p match
      case morkl.Path.Deref(_) | morkl.Path.Constant(_) => ()
      case morkl.Path.Concat(l, r) =>
        recp(l, boundP, boundS)
        recp(r, boundP, boundS)
      case morkl.Path.GroundedPP(p, _) => recp(p, boundP, boundS)
      case morkl.Path.GroundedSP(s, _) => recs(s, boundP, boundS)
    def recs(x: Space, boundP: Set[PathRef], boundS: Set[SpaceMention]): Unit = x match
      case Space.Empty | Space.Literal(_) => ()
      case Space.Mention(sm) =>
        if !boundS(sm) then out += sm
      case Space.Call(_, refs, mentions) =>
        refs.foreach(recp(_, boundP, boundS))
        mentions.foreach(recs(_, boundP, boundS))
      case Space.Singleton(p) => recp(p, boundP, boundS)
      case Space.Union(a, b) =>
        recs(a, boundP, boundS)
        recs(b, boundP, boundS)
      case Space.Intersection(a, b) =>
        recs(a, boundP, boundS)
        recs(b, boundP, boundS)
      case Space.Subtraction(a, b) =>
        recs(a, boundP, boundS)
        recs(b, boundP, boundS)
      case Space.Restriction(a, b) =>
        recs(a, boundP, boundS)
        recs(b, boundP, boundS)
      case Space.Raffination(a, b) =>
        recs(a, boundP, boundS)
        recs(b, boundP, boundS)
      case Space.Composition(a, b) =>
        recs(a, boundP, boundS)
        recs(b, boundP, boundS)
      case Space.Iteration(src, symbol, rest, templates) =>
        recs(src, boundP, boundS)
        recs(templates, boundP + symbol, boundS + rest)
      case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
        recs(src, boundP, boundS)
        recp(initial, boundP, boundS)
        recs(templates, boundP + acc + symbol, boundS + rest)
        recp(update, boundP + acc + symbol, boundS + rest)
      case Space.Fixpoint(initial, variable, step) =>
        recs(initial, boundP, boundS)
        recs(step, boundP, boundS + variable)
      case Space.Wrap(src, p) =>
        recs(src, boundP, boundS)
        recp(p, boundP, boundS)
      case Space.Unwrap(src, p) =>
        recs(src, boundP, boundS)
        recp(p, boundP, boundS)
      case Space.TailsUnion(src) =>
        recs(src, boundP, boundS)
      case Space.TailsIntersection(src) =>
        recs(src, boundP, boundS)
      case Space.PrefixClosure(src) =>
        recs(src, boundP, boundS)
      case Space.SuffixClosure(src) =>
        recs(src, boundP, boundS)
      case Space.TailsClosure(src) =>
        recs(src, boundP, boundS)
      case Space.GroundedSS(src, _) =>
        recs(src, boundP, boundS)
      case Space.Range(src, _, _) =>
        recs(src, boundP, boundS)
      case Space.GroundedPS(p, _) => recp(p, boundP, boundS)
    recs(s, Set.empty, Set.empty)
    out.result()

  private def freePathRefs(s: Space): Set[PathRef] =
    val out = Set.newBuilder[PathRef]
    def recp(p: morkl.Path, boundP: Set[PathRef], boundS: Set[SpaceMention]): Unit = p match
      case morkl.Path.Deref(pr) =>
        if !boundP(pr) then out += pr
      case morkl.Path.Constant(_) => ()
      case morkl.Path.Concat(l, r) =>
        recp(l, boundP, boundS)
        recp(r, boundP, boundS)
      case morkl.Path.GroundedPP(p, _) => recp(p, boundP, boundS)
      case morkl.Path.GroundedSP(s, _) => recs(s, boundP, boundS)
    def recs(x: Space, boundP: Set[PathRef], boundS: Set[SpaceMention]): Unit = x match
      case Space.Empty | Space.Mention(_) | Space.Literal(_) => ()
      case Space.Call(_, refs, mentions) =>
        refs.foreach(recp(_, boundP, boundS))
        mentions.foreach(recs(_, boundP, boundS))
      case Space.Singleton(p) => recp(p, boundP, boundS)
      case Space.Union(a, b) =>
        recs(a, boundP, boundS)
        recs(b, boundP, boundS)
      case Space.Intersection(a, b) =>
        recs(a, boundP, boundS)
        recs(b, boundP, boundS)
      case Space.Subtraction(a, b) =>
        recs(a, boundP, boundS)
        recs(b, boundP, boundS)
      case Space.Restriction(a, b) =>
        recs(a, boundP, boundS)
        recs(b, boundP, boundS)
      case Space.Raffination(a, b) =>
        recs(a, boundP, boundS)
        recs(b, boundP, boundS)
      case Space.Composition(a, b) =>
        recs(a, boundP, boundS)
        recs(b, boundP, boundS)
      case Space.Iteration(src, symbol, rest, templates) =>
        recs(src, boundP, boundS)
        recs(templates, boundP + symbol, boundS + rest)
      case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
        recs(src, boundP, boundS)
        recp(initial, boundP, boundS)
        recs(templates, boundP + acc + symbol, boundS + rest)
        recp(update, boundP + acc + symbol, boundS + rest)
      case Space.Fixpoint(initial, variable, step) =>
        recs(initial, boundP, boundS)
        recs(step, boundP, boundS + variable)
      case Space.Wrap(src, p) =>
        recs(src, boundP, boundS)
        recp(p, boundP, boundS)
      case Space.Unwrap(src, p) =>
        recs(src, boundP, boundS)
        recp(p, boundP, boundS)
      case Space.TailsUnion(src) =>
        recs(src, boundP, boundS)
      case Space.TailsIntersection(src) =>
        recs(src, boundP, boundS)
      case Space.PrefixClosure(src) =>
        recs(src, boundP, boundS)
      case Space.SuffixClosure(src) =>
        recs(src, boundP, boundS)
      case Space.TailsClosure(src) =>
        recs(src, boundP, boundS)
      case Space.GroundedSS(src, _) =>
        recs(src, boundP, boundS)
      case Space.Range(src, _, _) =>
        recs(src, boundP, boundS)
      case Space.GroundedPS(p, _) => recp(p, boundP, boundS)
    recs(s, Set.empty, Set.empty)
    out.result()

  private def renderSmt2(relation: OpenProgramRelation): String =
    PA.Law(
      s"${relation.caseName}:${relation.relation}",
      relation.lhs,
      relation.rhs,
      note = relation.note,
    ).smt2(relation.ctx)

  private def renderReport(relations: Vector[OpenProgramRelation], skips: Vector[OpenProgramSkip]): String =
    val lines = Vector.newBuilder[String]
    lines += "# Open Program Proof Report"
    lines += ""
    lines += s"Generated Z3 obligations: ${relations.length}"
    lines += s"Generated structural FOL obligations: ${fullProgramFolCases.length}"
    lines += s"Skipped relations: ${skips.length}"
    lines += "Structural FOL obligations are axiomatized program-DAG/schema consistency checks; per-constructor backend/source agreement is assumed, not independently proved. Executable Scala parity and bounded symbolic SMT provide the independent backend evidence."
    lines += ""
    lines += "## Generated"
    lines += ""
    lines += "| Program | Relation | Alphabet | Max Len | Width | Note |"
    lines += "| --- | --- | --- | --- | --- | --- |"
    for r <- relations do
      lines += s"| `${r.caseName}` | `${r.relation}` | `${r.ctx.alphabet.mkString(",")}` | `${r.ctx.maxLen}` | `${r.ctx.width}` | ${escapeMd(r.note)} |"
    if skips.nonEmpty then
      lines += ""
      lines += "## Skipped"
      lines += ""
      lines += "| Program | Relation | Reason |"
      lines += "| --- | --- | --- |"
      for s <- skips do
        lines += s"| `${s.caseName}` | `${s.relation}` | ${escapeMd(s.reason)} |"
    lines.result().mkString("\n") + "\n"

  private def comparePathTuples(left: PA.PathTuple, right: PA.PathTuple): Int =
    val n = math.min(left.length, right.length)
    var i = 0
    while i < n do
      val c = left(i).compareTo(right(i))
      if c != 0 then return c
      i += 1
    left.length.compareTo(right.length)

  private def safe(s: String): String =
    val chars = s.map(ch => if ch.isLetterOrDigit then ch else '_')
    val out = if chars.nonEmpty then chars else "x"
    if out.head.isDigit then "v_" + out else out

  private def manifestField(s: String): String =
    if s.isEmpty then "-" else tsvEscape(s)

  private def tsvEscape(s: String): String =
    s.replace("\\", "\\\\").replace("\t", "\\t").replace("\n", "\\n")

  private def escapeMd(s: String): String =
    s.replace("|", "\\|").replace("\n", " ")

object generateOpenProgramProofArtifacts:
  def main(args: Array[String]): Unit =
    val opts = parseArgs(args.toVector)
    val artifacts = OpenProgramProofArtifacts.writeAll(
      Paths.get(opts.getOrElse("out-dir", "proofs/open")),
      Paths.get(opts.getOrElse("manifest", "proofs/open/proof_manifest.tsv")),
    )
    println(s"wrote ${artifacts.count(_.kind == "z3")} open-program SMT2 artifacts")

  private def parseArgs(args: Vector[String]): Map[String, String] =
    var i = 0
    val out = Map.newBuilder[String, String]
    while i < args.length do
      val key = args(i)
      require(key.startsWith("--"), s"Expected --key, got: $key")
      require(i + 1 < args.length, s"Missing value for $key")
      out += key.drop(2) -> args(i + 1)
      i += 2
    out.result()
