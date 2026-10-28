package morkl

import morkl.Syntax.{*, given}

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path as JPath, Paths}
import java.security.MessageDigest
import scala.collection.mutable

case class CornerstoneProofCase(name: String,
                                expr: Space,
                                sc: SpaceContextMap = SpaceContextMap(Map.empty),
                                defs: Vector[Routine] = Vector.empty,
                                note: String = ""):
  val tc: TrieSpaceContextMap = TrieSpaceContext.fromReference(sc)
  val rc: PartialFunction[RoutinePtr, Routine] = mod(defs*)

case class CornerstoneProofResult(example: String,
                                  relation: String,
                                  lhsLabel: String,
                                  rhsLabel: String,
                                  lhs: SpaceValue,
                                  rhs: SpaceValue,
                                  note: String)

object CornerstoneProofArtifacts:
  private val OutDir: JPath = Paths.get("proofs/examples")
  private val Manifest: JPath = OutDir.resolve("proof_manifest.tsv")

  case class Artifact(kind: String, name: String, expected: String, artifact: JPath, note: String = "")

  def cases: Vector[CornerstoneProofCase] =
    val aunt = CornerstoneProofCase(
      "aunt",
      R"aunts"(S"family", S"people"),
      AuntQuery.context,
      Vector(Routines.aunt_query_routine),
      "Aunt graph query over the committed tiny family graph.",
    )

    val datalogEdges = SpaceValue((0 until 6).map(i => Syntax.parse(s"edge.n$i.n${i + 1}")).toSet)
    val semiNaive = DatalogExample.semiNaiveTransitive
    val datalog = CornerstoneProofCase(
      "semi-naive-datalog",
      semiNaive.name(DatalogExample.semiNaiveInitial(Space.Literal(datalogEdges)))("complete.path"),
      defs = Vector(semiNaive),
      note = "Semi-naive transitive closure over a six-edge chain.",
    )

    val lifeField = SpaceValue(
      "Cell.0.0",
      "Cell.0.1",
      "Cell.1.0",
    )
    val gol = CornerstoneProofCase(
      "gol",
      R"nextStep"(Space.Literal(lifeField)),
      defs = Vector(LifeExample.neigh, LifeExample.nextStep),
      note = "Pure Game-of-Life step using the MORKL neighbor and Range cardinality encoding.",
    )

    val puzzle = CornerstoneProofCase(
      "15-puzzle",
      SlidingPuzzleExample.step(4, Space.Literal(SlidingPuzzleExample.solved(4))),
      defs = SlidingPuzzleExample.routines(4).take(2),
      note = "One legal 15-puzzle frontier expansion from the solved 4x4 state.",
    )

    val tempWorld = SpaceValue(
      "cell.0.0.C",
      "cell.0.1.M",
      "cell.1.0.H",
      "cell.1.1.M",
    )
    val tempPrefixes =
      "cell" x
        Space.Literal(TemperatureExample.interval(0, 1, height = 2)) x
        Space.Literal(TemperatureExample.interval(0, 1, height = 2))
    val temperature = CornerstoneProofCase(
      "temperature",
      Space.Literal(tempWorld) <| tempPrefixes,
      note = "Small prefix-coded spatial temperature slice shaped like the NOAA query.",
    )

    val (queens4, queens4Ctx) = NQueensExample.program(4)
    val queensDefs = NQueensExample.routines(4).filter(r => queens4Ctx.isDefinedAt(r.name))
    val nqueens = CornerstoneProofCase(
      "nqueens",
      queens4.body,
      defs = queensDefs,
      note = "Pure MORKL 4-queens search; the benchmark suite scales this definition higher.",
    )

    val scc = CornerstoneProofCase(
      "scc",
      SccCornerstone.body,
      defs = SccCornerstone.defs,
      note = "Representative/member pairs from the paper's seedless divide-and-conquer SCC program.",
    )

    Vector(aunt, datalog, gol, puzzle, temperature, nqueens, scc)

  def writeAll(outDir: JPath = OutDir, manifest: JPath = Manifest): Vector[Artifact] =
    Files.createDirectories(outDir)
    Files.createDirectories(manifest.getParent)

    val checked = cases.map { c =>
      println(s"checking cornerstone backend parity for ${c.name}")
      c -> build(c)
    }
    // These are executable Scala backend checks, not solver certificates.
    // The previous TPTP/egg files defined both compared outputs as the same
    // precomputed literal, so they could not detect a backend error. Symbolic
    // bounded SMT and structural full-program FOL obligations are emitted by
    // OpenProgramProofArtifacts instead.
    Files.writeString(manifest, "kind\tname\texpected\tartifact\tnote\n", StandardCharsets.UTF_8)
    Files.writeString(outDir.resolve("CORNERSTONE_PARITY_REPORT.md"), renderReport(checked), StandardCharsets.UTF_8)
    Vector.empty

  def build(c: CornerstoneProofCase): Vector[CornerstoneProofResult] =
    given PathContext = PathContext.emptyMap
    given SpaceContext = c.sc
    given TrieSpaceContext = c.tc
    given PartialFunction[RoutinePtr, Routine] = c.rc

    val reference = eval(c.expr)
    val trie = evalTrie(c.expr).toSpaceValue
    requireEqual(c.name, "trie-vs-reference", trie, reference)

    val optimizedRoutine =
      Routine(RoutinePtr(s"${c.name}_source"), Vector.empty, c.sc.m.keys.toVector.sortBy(_.s), c.expr)
        .optimized(using c.rc)
    val sourceOptimized = evalTrie(optimizedRoutine.body).toSpaceValue
    requireEqual(c.name, "space-optimized", sourceOptimized, trie)

    val zipperBody = Supercompiler.lowerFixpointCalls(c.expr, c.rc)
    val zipper = transpileZ(zipperBody)(using PathContext.emptyMap, ZipperSpaceContext.fromTrie(c.tc), c.rc).materialize.toSpaceValue
    requireEqual(c.name, "zipper-vs-space", zipper, trie)

    val graph = execTGraph(c).toSpaceValue
    requireEqual(c.name, "graph-execT-vs-space", graph, trie)

    Vector(
      CornerstoneProofResult(c.name, "trie_vs_reference", "trie_eval", "reference_eval", trie, reference,
        "Trie evaluator output equals reference set evaluator output."),
      CornerstoneProofResult(c.name, "space_optimized", "source_optimized", "source_original", sourceOptimized, trie,
        "Default source optimizer output equals original Space/term output."),
      CornerstoneProofResult(c.name, "zipper_vs_space", "zipper_materialized", "space_eval_trie", zipper, trie,
        "Scala zipper program materialization equals eager Space/Trie evaluation."),
      CornerstoneProofResult(c.name, "graph_execT_vs_space", "graph_execT", "space_eval_trie", graph, trie,
        "Scala operation graph execT output equals eager Space/Trie evaluation."),
    )

  private def execTGraph(c: CornerstoneProofCase): TrieSpace =
    val mentions = c.sc.m.keys.toVector.sortBy(_.s)
    val defs = c.defs.map(r => r.name -> r).toMap
    val compiled = Supercompiler.compile(Routine(RoutinePtr(s"${c.name}_graph"), Vector.empty, mentions, c.expr), ctx = defs.lift.unlift)
    val top = compiled.graph.getOrElse(throw RuntimeException(s"${c.name}: graph compilation did not produce execT code"))
    val index = compileCallIndex(top, defs)
    val stack = mutable.Stack(new Array[List[Int] | TrieSpace | Null](top.nodes.length))
    for (sm, i) <- mentions.zipWithIndex do stack.top(i) = c.tc.resolve(sm)
    execT(top, stack, index)
    stack.top.last.asInstanceOf[TrieSpace]

  private def compileCallIndex(top: RecursiveOpGraph, defs: Map[RoutinePtr, Routine]): PartialFunction[String, RecursiveOpGraph] =
    val byName = defs.map((rp, routine) => rp.s -> routine)
    val compiled = mutable.Map.empty[String, RecursiveOpGraph]
    val worklist = mutable.Queue.from(graphCalls(top).filter(byName.contains))
    while worklist.nonEmpty do
      val name = worklist.dequeue()
      if !compiled.contains(name) then
        val compiledRoutine = Supercompiler.compile(byName(name), ctx = defs.lift.unlift)
        val graph = compiledRoutine.graph.getOrElse(throw RuntimeException(s"callee $name did not produce execT code"))
        compiled(name) = graph
        worklist.enqueueAll(graphCalls(graph).filter(byName.contains).filterNot(compiled.contains))
    val reachable = graphCalls(top) ++ compiled.valuesIterator.flatMap(graphCalls)
    val missing = reachable.filterNot(compiled.contains)
    require(missing.isEmpty, s"missing graph callee(s): ${missing.toVector.sorted.mkString(", ")}")
    val callGraph = compiled.view.mapValues(g => graphCalls(g).filter(compiled.contains)).toMap
    def cyclic(name: String, visiting: Set[String], visited: Set[String]): Boolean =
      if visiting(name) then true
      else if visited(name) then false
      else callGraph.getOrElse(name, Set.empty).exists(cyclic(_, visiting + name, visited + name))
    val recursive = compiled.keysIterator.filter(cyclic(_, Set.empty, Set.empty)).toVector.sorted
    val unsafe = recursive.filterNot(name =>
      Supercompiler.wellFoundedPartitionRecursion(byName(name), defs.lift.unlift)
    )
    require(unsafe.isEmpty, s"recursive Call not lowered or certified well-founded: ${unsafe.mkString(", ")}")
    compiled.toMap.lift.unlift

  private def graphCalls(g: RecursiveOpGraph): Set[String] =
    g.nodes.toVector.flatMap {
      case Left(Node("Call", constant, _, _)) => Vector(constant)
      case Left(_) => Vector.empty
      case Right(sg) => graphCalls(sg).toVector
    }.toSet

  private def requireEqual(example: String, relation: String, lhs: SpaceValue, rhs: SpaceValue): Unit =
    require(lhs == rhs, s"$example $relation mismatch:\nlhs=${lhs.pretty}\nrhs=${rhs.pretty}")

  private def renderReport(checked: Vector[(CornerstoneProofCase, Vector[CornerstoneProofResult])]): String =
    val rows = checked.map { (c, results) =>
      val output = results.head.lhs
      val relations = results.map(_.relation).mkString(", ")
      s"| `${c.name}` | `${output.paths.size}` | `${outputDigest(output)}` | $relations |"
    }
    (Vector(
      "# Cornerstone Backend Parity Report",
      "",
      "Status: PASS",
      "",
      "This report records executable Scala differential checks. It is not a solver proof: generation fails unless reference, trie, optimized source, zipper, and operation-graph results agree. Counterexample-sensitive symbolic SMT and axiomatized structural-FOL schema checks live under `proofs/open/`; the latter assume backend/source agreement per constructor and are not independent implementation-equivalence proofs.",
      "",
      "| Example | Result paths | Result digest | Checked relations |",
      "| --- | ---: | --- | --- |",
    ) ++ rows).mkString("\n") + "\n"

  private def outputDigest(space: SpaceValue): String =
    val md = MessageDigest.getInstance("SHA-256")
    val bytes = space.paths.toVector.sortBy(_.show).map(_.show).mkString("\n").getBytes(StandardCharsets.UTF_8)
    md.digest(bytes).take(12).map("%02x".format(_)).mkString

@main def generateCornerstoneProofArtifacts(args: String*): Unit =
  val opts = parseArgs(args.toVector)
  val outDir = Paths.get(opts.getOrElse("out-dir", "proofs/examples"))
  val manifest = Paths.get(opts.getOrElse("manifest", outDir.resolve("proof_manifest.tsv").toString))
  val spatialReport = Paths.get(opts.getOrElse(
    "spatial-report",
    CornerstoneSpatialReport.DefaultOutput.toString,
  ))
  CornerstoneProofArtifacts.writeAll(outDir, manifest)
  CornerstoneSpatialReport.write(spatialReport)
  println(s"checked ${CornerstoneProofArtifacts.cases.length} cornerstone programs across four backend relations; wrote no closed-output solver tautologies; wrote spatial report to $spatialReport")

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
