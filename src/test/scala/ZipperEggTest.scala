package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** Transpile the fundamental example programs from the Scala [[SpaceZipper]] (via [[transpileZ]]) into
 *  egglog `Z` terms ([[ZipperEgg.eggOf]]), and CHECK the two zipper abstractions COINCIDE — PURELY BY
 *  DESCENT, never materialising the result.  For every member path of `execZ`'s result you can descend to
 *  it (focus `Term` = T); for every boundary non-member you cannot (`Term` = F / the descent dead-ends).
 *  For the virtual cursors the `Descend` rules move locally through ∪/∩/\ — no operand is ever built.
 *
 *  Each example is written as a standalone program under `zipper-egg-tests/<name>.egg` (it `(include`s
 *  the shared `prelude.egg`), so it can be run independently:  `cd zipper-egg-tests && egglog aunt-kg.egg`.
 *  When the `egglog` binary is present the test also runs each file and asserts it exits 0 (all checks
 *  pass); otherwise it still writes the files and verifies the Scala side. */
class ZipperEggTest extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(10, "min")

  val noRc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
  val noPc: PathContext = PathContextMap(Map.empty)
  def pv(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)

  val dir = new java.io.File(Loaders.repoRoot, "zipper-egg-tests")
  val eggBin: Option[String] = Tools.egglog.path      // $EGGLOG -> PATH -> conventional locations

  /** Write `<name>.egg`, run egglog on it (if installed) and assert exit 0. */
  def runEgg(name: String, content: String): Unit =
    dir.mkdirs()
    val f = new java.io.File(dir, s"$name.egg")
    val w = new java.io.FileWriter(f); try w.write(content) finally w.close()
    eggBin match
      case Some(bin) =>
        val out = new StringBuilder
        val log = scala.sys.process.ProcessLogger(out.append(_).append('\n'), out.append(_).append('\n'))
        val exit = scala.sys.process.Process(Seq(bin, s"$name.egg"), dir).!(log)
        assertEquals(exit, 0, s"egglog rejected $name.egg:\n${out.toString.linesIterator.filterNot(_.contains("should start")).toList.takeRight(12).mkString("\n")}")
      case None => Loaders.note(s"[zipper-egg] ${Tools.egglog.missing}; wrote $name.egg (not executed)")

  /** DESCENT coincidence (movement spec): members reachable, non-members not — never materialised. */
  def emit(name: String, title: String, z: SpaceZipper, result: ITrie): Unit =
    runEgg(name, ZipperEgg.coincidenceProgram("(include \"prelude.egg\")", title, z, result))

  /** IMPLEMENTATION coincidence: egglog runs the modelled recursive set-ops and must compute Scala's trie. */
  def emitImpl(name: String, title: String, z: SpaceZipper, result: ITrie): Unit =
    runEgg(s"$name-impl", ZipperEgg.implCoincidenceProgram("(include \"impl-prelude.egg\")", title, z, result))

  /** A SpaceZipper for `s` under the given trie context, plus the trie it materialises to (= execZ). */
  def zipAndResult(s: Space, ic: Map[SpaceMention, ITrie] = Map.empty,
                   rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): (SpaceZipper, ITrie) =
    val z = transpileZ(s)(using noPc, ic, rc)
    (z, SpaceZipper.materialize(z))

  // ============================================================================================
  // Fundamental examples (control-flow heavy ⇒ the zipper is a concrete Lit/Prefix cursor).  egg
  // descends the cursor to confirm exactly the result's members are reachable and nothing else.
  // ============================================================================================

  test("datalog semi-naive (transitive closure) — zipper transpiles & coincides in egg") {
    val edges = sv(pv("0", "1"), pv("1", "2"), pv("2", "3"))                 // a 4-node chain
    val (ttop, residual) = lowerCalls(Routines.transitive_routine, Syntax.mod(Routines.transitive_routine))
    assert(residual.isEmpty)
    val (z, result) = zipAndResult(ttop, ic = Map(SpaceMention("edges") -> ITrie.fromSpaceValue(edges)))
    assertEquals(result.size, 6)                                            // TC of a 4-chain = C(4,2) = 6 pairs
    emit("datalog-tc", "datalog semi-naive transitive closure over a 4-node chain (TC = 6 pairs)", z, result)
    emitImpl("datalog-tc", "datalog TC: recursive trie set-ops compute the same closure", z, result)
  }

  test("aunt-kg (knowledge-graph query) — zipper transpiles & coincides in egg") {
    val fam = AuntQuery.context.resolve(SpaceMention("family"))
    val ppl = AuntQuery.context.resolve(SpaceMention("people"))
    val ic = Map(SpaceMention("family") -> ITrie.fromSpaceValue(fam), SpaceMention("people") -> ITrie.fromSpaceValue(ppl))
    val (z, result) = zipAndResult(Routines.aunt_query_routine.body, ic = ic)
    assert(result.nonEmpty, "expected some aunts in the Tolkien-style genealogy")
    emit("aunt-kg", "aunt query over the in-repo genealogy (Wrap \"Aunt\" over the iterated set-algebra)", z, result)
    emitImpl("aunt-kg", "aunt query: recursive trie ops compute the same aunts", z, result)
  }

  test("puzzle 2x2 (sliding-tile reachable states) — zipper transpiles & coincides in egg") {
    val p = Sliding.puzzle(2, 2)
    val (z, result) = zipAndResult(p.entry, rc = p.defs)
    assertEquals(result.size, 12)                                           // 4!/2 reachable states
    emit("puzzle-2x2", "sliding-tile 2x2 full reachable state space (12 states) via the explore fixpoint", z, result)
    emitImpl("puzzle-2x2", "puzzle 2x2: recursive trie ops compute the same reachable states", z, result)
  }

  // ============================================================================================
  // Local set-algebra examples (the zipper stays VIRTUAL: Union/Intersection of cursors).  Here the
  // Descend rules genuinely MOVE through the fused ∪/∩ — a member descent reduces to (Eps) and a
  // non-member descent to (Empty) without ever building either operand.  This is the real point.
  // ============================================================================================

  test("selective (A∪B)∩C — virtual zipper transpiles & coincides in egg") {
    val expr = Intersection(Union(Literal(sv(pv("1"), pv("2"))), Literal(sv(pv("2"), pv("3")))), Literal(sv(pv("1"))))
    val (z, result) = zipAndResult(expr)
    assertEquals(result.toSpaceValue, sv(pv("1")))                          // ({1,2}∪{2,3})∩{1} = {1}
    assert(z.isInstanceOf[SpaceZipper.Intersection], "expected a virtual Intersection cursor")
    emit("selective-intersection", "selective (A∪B)∩C over small literals — a virtual fused cursor", z, result)
    emitImpl("selective-intersection", "selective (A∪B)∩C: egg runs the recursive ∪ then ∩", z, result)
  }

  test("three-way A∩B∩C — virtual zipper transpiles & coincides in egg") {
    val expr = Intersection(Intersection(Literal(sv(pv("1"), pv("2"), pv("3"))), Literal(sv(pv("2"), pv("3"), pv("4")))),
                            Literal(sv(pv("2"), pv("3"), pv("5"))))
    val (z, result) = zipAndResult(expr)
    assertEquals(result.toSpaceValue, sv(pv("2"), pv("3")))                 // {1,2,3}∩{2,3,4}∩{2,3,5} = {2,3}
    emit("three-way-intersection", "three-way A∩B∩C over small literals — nested virtual Intersection cursors", z, result)
    emitImpl("three-way-intersection", "three-way A∩B∩C: egg runs nested recursive ∩", z, result)
  }

  // ============================================================================================
  // The datalog workload through the VIRTUAL algebra (not pre-evaluated): the semi-naive TC
  // fixpoint unrolled to its convergence depth, each step a virtual Iter/JoinBody/\/∪ expression
  // over the edge literal — egg's movement rules walk it; nothing is materialised in the spec.
  // ============================================================================================
  test("datalog semi-naive TC — VIRTUAL: unrolled Iter/JoinBody expression coincides by movement") {
    val edges = sv(pv("0", "1"), pv("1", "2"), pv("2", "3"))
    val e = ITrie.fromSpaceValue(edges)
    val eTerm = ZipperEgg.eggOfTrie(e)
    // Scala-side reference: the semi-naive loop over ITrie (independent of the egg encoding)
    def step(delta: ITrie): ITrie =
      ITrie.joinAll(delta.children.iterator.map((h, t) =>
        ITrie.wrap(List(h), ITrie.tailsUnion(ITrie.restriction(e, t)))).toSeq)
    var all = e; var delta = e; var rounds = 0
    while delta.nonEmpty do { val d2 = ITrie.subtraction(step(delta), all); all = ITrie.union(all, d2); delta = d2; rounds += 1 }
    assertEquals(all.size, 6)                                               // TC of the 4-chain
    // the SAME unrolling as a virtual egg expression: allᵢ₊₁ = allᵢ ∪ (Iter deltaᵢ (JoinBody e) \ allᵢ)
    var allT = eTerm; var deltaT = eTerm
    for _ <- 1 to rounds do
      val stepT = s"(Iter $deltaT (JoinBody $eTerm))"
      deltaT = s"(Subtraction $stepT $allT)"
      allT = s"(Union $allT $deltaT)"
    val keys = ZipperEgg.keysOf(SpaceZipper.traversal(e))
    runEgg("datalog-tc-virtual", ZipperEgg.coincidenceProgramRaw("(include \"prelude.egg\")",
      s"semi-naive TC over a 4-chain, UNROLLED as a virtual Iter/JoinBody expression ($rounds rounds) — " +
      "egg walks the datalog workload through the virtual algebra", allT, keys, all))
  }

  // ============================================================================================
  // Per-operation: transpile each operator over small literals and confirm egglog's RECURSIVE
  // IMPLEMENTATION (TrU/TrI/TrS/TrC/TrR/TrW/TrTU/TrTI) computes exactly the Scala result.
  // ============================================================================================
  test("each operator's implementation coincides (transpiled, run recursively in egg)") {
    val A = Literal(sv(pv("1"), pv("2")));   val B = Literal(sv(pv("2"), pv("3")))
    val X = Literal(sv(pv("1", "2"), pv("3"))); val P = Literal(sv(pv("1")))   // {1.2,3} and prefix {1}
    val cases: Seq[(String, Space)] = Seq(
      "op-union"        -> Union(A, B),
      "op-intersection" -> Intersection(A, B),
      "op-subtraction"  -> Subtraction(A, B),
      "op-composition"  -> Composition(Literal(sv(pv("1"))), Literal(sv(pv("2")))),
      "op-restriction"  -> Restriction(X, P),
      "op-raffination"  -> Raffination(X, P),
      "op-wrap"         -> Wrap(Literal(sv(pv("2"))), Path.Constant(pv("1"))),
      "op-tailsunion"   -> TailsUnion(Literal(sv(pv("1", "2"), pv("3", "4")))),
      "op-tailsinter"   -> TailsIntersection(Literal(sv(pv("1", "2"), pv("4", "2")))))
    for (name, expr) <- cases do
      val (z, result) = zipAndResult(expr)
      assertEquals(result, evalI(expr), s"$name: zipper materialize != evalI")   // Scala self-consistency
      emitImpl(name, s"$name: recursive trie implementation in egg = Scala", z, result)
  }
end ZipperEggTest
