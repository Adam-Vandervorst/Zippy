package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** Path-LENGTH bounds must be SOUND — `∀ p ∈ eval(s): lo ≤ |p| ≤ hi` — at both tiers
 *  ([[Lower.lenBounds]] baseline; [[LenZ3]] refinement), with the z3 tier never looser than the
 *  baseline (dominance).  The corpus test is the soundness gate; the motivating example pins the
 *  disjunctive reasoning the interval baseline cannot do. */
class LenBoundsCheck extends FunSuite:
  import Space.*
  import Lower.LenBounds
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  val INF = LenBounds.INF
  def pathOf(n: Int, item: String = "a"): PathValue = PathValue(List.fill(n)(item))
  def lit(ps: PathValue*): Space = Space.Literal(SpaceValue(ps.toSet))
  def lens(v: SpaceValue): Set[Long] = v.paths.map(_.items.length.toLong)

  def checkSound(s: Space, b: LenBounds, name: String)(using pc: PathContext = PathContextMap(Map.empty),
                                                       sc: SpaceContext = SpaceContextMap(Map.empty)): Unit =
    for l <- lens(eval(s)) do
      assert(b.lo <= l && l <= b.hi, s"$name: path length $l outside [${b.lo}, ${b.hi}] for ${s.show}")

  // ---- the motivating example -----------------------------------------------------------------
  //   ((({len 10} ∪ {len 20–30}) ∩ {len 15}) ∪ {ε}) x {len 2, len 3 · len 3}
  // The meet's length sets ({10, 25} vs {15}) are disjoint, so it is EMPTY; the left factor is
  // exactly {ε} and the composition's lengths are exactly those of the right factor: [2, 6].
  // Interval hulls cannot see this ({10,25} hulls to [10,25] ∋ 15): the baseline says [2, 21].
  val right = Space.Union(
    Space.Singleton(Path.Constant(pathOf(2, "x"))),
    Space.Singleton(Path.Concat(Path.Constant(pathOf(3, "u")), Path.Constant(pathOf(3, "v")))))

  def example(mid: Space): Space =
    Space.Composition(
      Space.Union(
        Space.Intersection(Space.Union(lit(pathOf(10)), mid), lit(pathOf(15))),
        lit(PathValue(Nil))),
      right)

  test("example (closed): baseline [2, 21]; z3 pins the length-disjoint meet empty -> [2, 6]") {
    val prog = example(lit(pathOf(25)))                      // 25 ∈ [20, 30]
    assertEquals(lens(eval(prog)), Set(2L, 6L))              // ground truth
    val b = Lower.lenBounds(prog)
    assertEquals(b, LenBounds(2, 21))                        // hull: meet [15,15]; ∪ε [0,15]; +[2,6]
    checkSound(prog, b, "example-closed")
    assume(LenZ3.available, "z3 not on PATH")
    val (zb, st) = LenZ3.boundsWithStatus(prog)
    assertEquals(st, SizeZ3.Status.Solved)
    assertEquals((zb.lo, zb.hi), (2L, 6L))
  }

  test("example (open): a free length-25 path variable still forces [2, 6] by pure length reasoning") {
    // {Deref v25} is not closed (no ground fold possible) — z3 must use the length disjunction
    val prog = example(Space.Singleton(Path.Deref(PathRef("v25").known(25))))
    assertEquals(Lower.lenBounds(prog), LenBounds(2, 21))
    assume(LenZ3.available, "z3 not on PATH")
    val (zb, st) = LenZ3.boundsWithStatus(prog)
    assertEquals(st, SizeZ3.Status.Solved)
    assertEquals((zb.lo, zb.hi), (2L, 6L))
    // and the bounds hold on an actual binding of v25
    checkSound(prog, zb, "example-open")(using PathContextMap(Map(PathRef("v25") -> pathOf(25, "q"))))
  }

  // ---- transfer functions on the tricky cases ---------------------------------------------------
  test("transfer functions: wrap shift, unwrap, tails, restriction, iteration, composition-empty") {
    val ab = lit(pathOf(1), pathOf(3))                             // lengths {1, 3}
    assertEquals(Lower.lenBounds(ab), LenBounds(1, 3))
    // wrap shifts by the prefix length; unwrap shifts back down
    val w = Space.Wrap(ab, Path.Constant(pathOf(2, "k")))
    assertEquals(Lower.lenBounds(w), LenBounds(3, 5))
    assertEquals(Lower.lenBounds(Space.Unwrap(w, Path.Constant(pathOf(2, "k")))), LenBounds(1, 3))
    // tails drop exactly one head item; an ε-only source has no tails (empty marker)
    assertEquals(Lower.lenBounds(Space.TailsUnion(ab)), LenBounds(0, 2))
    assert(Lower.lenBounds(Space.TailsUnion(lit(PathValue(Nil)))).isEmpty)
    // restriction: kept paths have a prefix in the right operand
    assertEquals(Lower.lenBounds(Space.Restriction(S"u", lit(pathOf(4)))).lo, 4L)
    // iteration: lengths come from the body; rest is refined to tail lengths of the source
    val it = ab.iter(P"h", S"t", Space.Composition(Space.Singleton(P"h"), S"t"))
    val ib = Lower.lenBounds(it)
    checkSound(it, ib, "iter")
    assertEquals(ib, LenBounds(1, 3))                              // 1 (head) + [0, 2] (tail)
    // composition with a provably empty side is empty
    assert(Lower.lenBounds(Space.Composition(ab, Space.Empty)).isEmpty)
    // a length-hinted free path variable is exact
    assertEquals(Lower.lenBounds(Space.Singleton(Path.Deref(PathRef("v").known(7)))), LenBounds(7, 7))
  }

  // ---- random programs: bounds never violated ---------------------------------------------------
  test("soundness over the corpus: every path length inside both tiers' bounds; z3 dominates baseline") {
    val f = new java.io.File(Loaders.repoRoot, "corpus_1000.ser")
    assert(f.exists, "corpus not found — run morkl.ProgramExpressivity first")
    val recs = locally {
      val ois = new java.io.ObjectInputStream(new java.io.FileInputStream(f))
      try ois.readObject().asInstanceOf[Vector[FuzzRec]] finally ois.close()
    }
    val rng = new java.util.Random(20260805)
    val A = SpaceFuzzer.alphabet
    def randPath(): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
    def randSV(): SpaceValue = SpaceValue((0 until rng.nextInt(6)).map(_ => randPath()).toSet)
    val sNames = (0 until 3).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until 3).map(j => PathRef("p" + j)).toVector

    var checked = 0
    for r <- recs; _ <- 0 until 5 do
      val svs = Vector.fill(3)(randSV()); val pvs = Vector.fill(3)(randPath())
      val closed = subs(r.prog)(
        spre = { case Space.Mention(m) if sNames.contains(m) => Space.Literal(svs(sNames.indexOf(m))) },
        ppre = { case Path.Deref(pr) if pNames.contains(pr) => Path.Constant(pvs(pNames.indexOf(pr))) })
      val ls = lens(eval(closed))
      val cb = Lower.lenBounds(closed)                       // closed bounds
      val ob = Lower.lenBounds(r.prog)                       // open bounds must also contain
      for l <- ls do
        assert(cb.lo <= l && l <= cb.hi, s"closed: length $l outside [${cb.lo}, ${cb.hi}] for ${closed.show}")
        assert(ob.lo <= l && l <= ob.hi, s"open: length $l outside [${ob.lo}, ${ob.hi}] for ${r.prog.show}")
      checked += 1
    println(s"LEN-BOUNDS: $checked closed corpus instances, all path lengths inside both intervals")

    assume(LenZ3.available, "z3 not on PATH")
    var solved = 0; var tighter = 0; var zchecked = 0
    val limits = collection.mutable.Map.empty[String, Int]
    for (r, pi) <- recs.take(200).zipWithIndex do
      val ob = Lower.lenBounds(r.prog)
      val (zb, st) = LenZ3.boundsWithStatus(r.prog, timeoutSec = 5)
      st match
        case SizeZ3.Status.Solved =>
          solved += 1
          assert(zb.lo >= ob.lo && zb.hi <= ob.hi, s"#$pi: z3 [${zb.lo}, ${zb.hi}] looser than baseline [${ob.lo}, ${ob.hi}]")
          if zb.lo > ob.lo || zb.hi < ob.hi then tighter += 1
          for _ <- 0 until 5 do
            val pc = PathContextMap(pNames.map(_ -> randPath()).toMap)
            val sc = SpaceContextMap(sNames.map(_ -> randSV()).toMap)
            for l <- lens(eval(r.prog)(using pc, sc)) do
              assert(zb.lo <= l && l <= zb.hi, s"#$pi: z3 unsound — length $l outside [${zb.lo}, ${zb.hi}] for ${r.prog.show}")
            zchecked += 1
        case other => limits.updateWith(other.toString.takeWhile(_ != '(')) (c => Some(c.getOrElse(0) + 1))
    println(s"LEN-Z3: 200 programs — solved $solved (strictly tighter than baseline on $tighter), " +
      s"$zchecked random-input soundness checks; limits: ${if limits.isEmpty then "none" else limits.mkString(", ")}")
    assert(solved > 0, "z3 solved nothing — encoding broken?")
  }
end LenBoundsCheck
