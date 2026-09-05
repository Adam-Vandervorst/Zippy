package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** Randomized property tests — the strongest guard on the optimizer (push_out + optimize_sharing)
 *  and the executors.  Over hundreds of randomly-generated programs we assert that transpile+execT
 *  and transpile+optimize+execT both agree with the reference `eval`, and that the interpreters
 *  (evalT, evalI) agree too.  A failure prints the seed and the program for exact reproduction. */
class OptimizerProperties extends FunSuite:
  import Space.*

  private val mentionNames = Vector("a", "b", "c")
  private val syms = Vector("p", "q", "r")

  private def pathItem(rng: scala.util.Random): PathItem = syms(rng.nextInt(syms.length))
  private def randPath(rng: scala.util.Random): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(pathItem(rng)))
  private def randLiteral(rng: scala.util.Random): SpaceValue =
    SpaceValue((0 to rng.nextInt(4)).map(_ => randPath(rng)).toSet)

  /** A random Space in the op-graph-supported, non-recursive, non-grounded fragment.  `vars` are the
   *  space variables in scope (mentions at the top, plus iteration `rest`s); `pvars` the path vars
   *  (iteration heads).  Bounded by `depth`. */
  private def randSpace(depth: Int, vars: Vector[String], pvars: Vector[String], rng: scala.util.Random): Space =
    def leaf(): Space = rng.nextInt(5) match
      case 0 => Space.Empty
      case 1 => Space.Literal(randLiteral(rng))
      case 2 if vars.nonEmpty => Space.Mention(SpaceMention(vars(rng.nextInt(vars.length))))
      case 3 if pvars.nonEmpty => Space.Singleton(Path.Deref(PathRef(pvars(rng.nextInt(pvars.length))).known(1)))
      case _ => Space.Singleton(Path.Constant(randPath(rng)))
    if depth <= 0 then leaf()
    else
      def sub() = randSpace(depth - 1, vars, pvars, rng)
      rng.nextInt(15) match
        case 0 => Space.Union(sub(), sub())
        case 1 => Space.Intersection(sub(), sub())
        case 2 => Space.Subtraction(sub(), sub())
        case 3 => Space.Restriction(sub(), sub())
        case 4 => Space.Raffination(sub(), sub())
        case 5 => Space.Composition(sub(), sub())
        case 6 => Space.Wrap(sub(), Path.Constant(randPath(rng)))
        case 7 => Space.Unwrap(sub(), Path.Constant(randPath(rng)))
        case 8 => Space.TailsUnion(sub())
        case 9 => Space.TailsIntersection(sub())
        case 10 => { val lo = rng.nextInt(3); Space.Range(sub(), lo, lo + 1 + rng.nextInt(3)) }
        case 11 => Space.Range(sub(), 0, 1 + rng.nextInt(3))   // [0,hi) windows too
        case _ =>                                   // an iteration introduces a head + rest binder
          val h = s"h${rng.nextInt(1000)}"; val t = s"t${rng.nextInt(1000)}"
          Space.Iteration(sub(), PathRef(h).known(1), SpaceMention(t),
            randSpace(depth - 1, vars :+ t, pvars :+ h, rng))

  test("property: transpile+execT and transpile+optimize+execT preserve eval (300 random programs)") {
    var checked = 0
    for seed <- 0 until 300 do
      val rng = new scala.util.Random(seed.toLong * 0x9E3779B1L)
      val prog = randSpace(3, mentionNames, Vector.empty, rng)
      val binds = mentionNames.map(m => SpaceMention(m) -> randLiteral(rng)).toMap
      val sc = SpaceContextMap(binds)
      val ic = binds.map((m, v) => m -> ITrie.fromSpaceValue(v))
      val ref = eval(prog)(using sc = sc)
      // interpreters agree
      assertEquals(evalI(prog)(using ic = ic).toSpaceValue, ref, s"evalI seed=$seed: ${prog.show}")
      assertEquals(evalT(prog)(using tc = binds.map((m, v) => m -> Trie.fromSpaceValue(v))).toSpaceValue, ref, s"evalT seed=$seed: ${prog.show}")
      // op-graph: transpile, then execT raw and execT(optimize) both match, and stay well-formed
      val main = Routine(RoutinePtr("main"), Vector.empty, mentionNames.map(SpaceMention(_)), prog)
      val g = transpile(main)
      val mtrie = binds.map((m, v) => m.s -> ITrie.fromSpaceValue(v))
      assertEquals(runGraphT(g, mentions = mtrie).toSpaceValue, ref, s"execT seed=$seed: ${prog.show}")
      val go = optimize(g)
      assert(wellFormed(go), s"optimize ill-formed seed=$seed: ${prog.show}")
      assertEquals(runGraphT(go, mentions = mtrie).toSpaceValue, ref, s"execT(optimize) seed=$seed: ${prog.show}")
      checked += 1
    assertEquals(checked, 300)
  }

  // independent transitive-closure reference for the random-graph Fixpoint property
  private def refClosure(es: Set[(Int, Int)]): Set[(Int, Int)] =
    var s = es; var grew = true
    while grew do { val a = for (x, y) <- s; (c, d) <- s if y == c yield (x, d); val n = s ++ a; grew = n.size != s.size; s = n }
    s

  test("property: Space.Fixpoint transitive closure == reference over 60 random graphs") {
    val next = Routines.transitive_routine.body match
      case Space.Union(_, Space.Call(_, _, Vector(n))) => n
      case other => fail(s"unexpected transitive body: ${other.show}")
    for seed <- 0 until 60 do
      val rng = new scala.util.Random(seed.toLong * 0x85EBCA77L + 1)
      val n = 2 + rng.nextInt(5)
      val es = (0 to rng.nextInt(n * 2)).map(_ => (rng.nextInt(n), rng.nextInt(n))).toSet
      val edges = SpaceValue(es.map((x, y) => PathValue(List(x.toString, y.toString))))
      val fix: Space = Space.Fixpoint(Literal(edges), SpaceMention("edges"), next)
      val g = optimize(transpile(R"tc"() := fix))
      val got = runGraphT(g).toSpaceValue.paths.map(p => (p.items(0).toInt, p.items(1).toInt))
      assertEquals(got, refClosure(es), s"fixpoint closure seed=$seed edges=$es")
  }
end OptimizerProperties

/** Audit of grounded (host-function) usage.  Grounded nodes are opaque to the algebra and the
 *  op-graph backend; the guiding examples should use them only where genuinely unavoidable.  This
 *  test pins the audit: interval/temperature and the relational/recursive examples are PURE (zero
 *  grounded nodes), and Game of Life is now pure too — its B3/S23 neighbour arithmetic is precomputed
 *  into number relations and its live-neighbour counting uses the ordered-slice `Range`. */
class GroundedAudit extends FunSuite:
  import Space.*

  /** Any grounded node (space- or path-level), recursively. */
  def usesGrounded(s: Space): Boolean = s match
    case _: Space.GroundedSS | _: Space.GroundedPS => true
    case Space.Call(_, refs, ms) => refs.exists(groundedP) || ms.exists(usesGrounded)
    case Space.Singleton(p) => groundedP(p)
    case Space.Union(a, b) => usesGrounded(a) || usesGrounded(b)
    case Space.Intersection(a, b) => usesGrounded(a) || usesGrounded(b)
    case Space.Subtraction(a, b) => usesGrounded(a) || usesGrounded(b)
    case Space.Restriction(a, b) => usesGrounded(a) || usesGrounded(b)
    case Space.Raffination(a, b) => usesGrounded(a) || usesGrounded(b)
    case Space.Composition(a, b) => usesGrounded(a) || usesGrounded(b)
    case Space.Iteration(src, _, _, b) => usesGrounded(src) || usesGrounded(b)
    case Space.Fixpoint(i, _, b) => usesGrounded(i) || usesGrounded(b)
    case Space.Fold(src, i, _, _, _, b, u) => usesGrounded(src) || groundedP(i) || usesGrounded(b) || groundedP(u)
    case Space.Wrap(src, p) => usesGrounded(src) || groundedP(p)
    case Space.Unwrap(src, p) => usesGrounded(src) || groundedP(p)
    case Space.TailsUnion(src) => usesGrounded(src)
    case Space.TailsIntersection(src) => usesGrounded(src)
    case Space.Range(a, _, _) => usesGrounded(a)
    case Space.Empty | Space.Mention(_) | Space.Literal(_) => false
  def groundedP(p: Path): Boolean = p match
    case _: Path.GroundedPP | _: Path.GroundedSP => true
    case Path.Concat(l, r) => groundedP(l) || groundedP(r)
    case Path.Deref(_) | Path.Constant(_) => false

  test("audit: interval/temperature are pure (no grounded nodes)") {
    // temperature: prefix-interval spatial range + temperature-band restriction over literals
    val world = Literal(SpaceValue("0.0.VW", "0.1.C", "1.0.N"))
    val tempQ = Union(Restriction(world, Literal(NOAA.interval(0, 1, 2))), Restriction(world, ss"VW"))
    assert(!usesGrounded(tempQ), "temperature query must be pure")
    // interval is data built in Scala (no grounded MORKL op), used inside a Literal
    assert(NOAA.interval(3, 12, 6).paths.nonEmpty)
    assert(!usesGrounded(Literal(NOAA.interval(3, 12, 6))), "interval literal must be pure")
  }

  test("audit: the relational/recursive examples are pure") {
    assert(!usesGrounded(Routines.aunt_query_routine.body), "aunt must be pure")
    assert(!usesGrounded(Routines.transitive_routine.body), "datalog/transitive must be pure")
    assert(!usesGrounded(Routines.reachable_routine.body), "reachable must be pure")
    assert(!usesGrounded(NQueens.board(5).program), "pure n-queens must be pure")
    assert(!usesGrounded(Sliding.puzzle(3, 3).expandStep(S"frontier")), "pure sliding must be pure")
  }

  test("audit: Game of Life is now pure (precomputed number relations + Range counting)") {
    val rules = GoL.rulesFor(Set((0, 0), (5, 5)))
    assert(!usesGrounded(rules.defs(RoutinePtr("neigh")).body), "GoL neigh is pure (number relations + Unwrap)")
    assert(!usesGrounded(rules.defs(RoutinePtr("nextStep")).body), "GoL nextStep is pure (ordered-slice Range)")
    // the independent reference `GoL.step` is plain Scala used only for correctness checks
    assertEquals(GoL.step(Set((0, 0), (0, 1), (0, 2))), Set((-1, 1), (0, 1), (1, 1)))  // blinker flips
  }
end GroundedAudit
