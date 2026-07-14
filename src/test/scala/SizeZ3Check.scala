package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** The z3-backed size bounds ([[SizeZ3.bounds]]) must DOMINATE the baseline — an interval
 *  contained in [[Lower.sizeBounds]]'s, on every program of the same sets the baseline was
 *  measured on (the suite programs and the 1000-program corpus) — and remain SOUND
 *  (`lo ≤ |eval| ≤ hi`) everywhere.  Plus the two motivating relational shapes. */
class SizeZ3Check extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  val INF = Lower.SizeBounds.INF
  def fmt(b: Lower.SizeBounds): String = s"[${b.lo}, ${if b.hi == INF then "inf" else b.hi}]"

  /** dominance + interval sanity; returns the pair (baseline, z3) */
  def dominated(s: Space, name: String): (Lower.SizeBounds, Lower.SizeBounds) =
    val base = Lower.sizeBounds(s)
    val z = SizeZ3.bounds(s)
    assert(z.lo >= base.lo && z.hi <= base.hi && z.loHeaded >= base.loHeaded,
      s"$name: z3 ${fmt(z)} not within baseline ${fmt(base)} for ${s.show}")
    assert(z.lo <= z.hi && z.loHeaded <= z.lo, s"$name: malformed ${fmt(z)}")
    (base, z)

  def soundOn(s: Space, z: Lower.SizeBounds, name: String)(using sc: SpaceContext = SpaceContextMap(Map.empty)): Unit =
    val v = eval(s)
    val n = v.paths.size.toLong
    assert(z.lo <= n && n <= z.hi, s"$name: |eval|=$n outside z3 ${fmt(z)} for ${s.show}")
    assert(z.loHeaded <= v.paths.count(_.items.nonEmpty), s"$name: headed bound unsound")

  test("motivating: x ∪ (x ∩ y) — the shared-x over-estimate closes to exact") {
    assume(SizeZ3.available, "z3 not on PATH")
    val x = Space.Literal(SpaceValue("a", "b", "c"))
    val u = x \/ (x /\ S"y")
    val (base, z) = dominated(u, "x∪(x∩y)")
    assertEquals((z.lo, z.hi), (3L, 3L), s"expected exact [3,3], got ${fmt(z)} (baseline ${fmt(base)})")
    assert(base.hi > 3, s"baseline should be the loose [3,6], got ${fmt(base)}")   // the win is real
    for ysv <- Seq(SpaceValue(), SpaceValue("a"), SpaceValue("a", "z.z")) do
      soundOn(u, z, "x∪(x∩y)")(using SpaceContextMap(Map(SpaceMention("y") -> ysv)))
  }

  test("motivating: x ∖ (x ∩ (x ∩ x)) — the shared-x under-estimate closes to exact ∅") {
    assume(SizeZ3.available, "z3 not on PATH")
    val x: Space = S"x"
    val d = x \ (x /\ (x /\ x))
    val (base, z) = dominated(d, "x∖(x∩(x∩x))")
    assertEquals((z.lo, z.hi), (0L, 0L), s"expected exact [0,0], got ${fmt(z)} (baseline ${fmt(base)})")
    assert(base.hi == INF, "baseline is vacuous here — the z3 tier must not be")
    for xsv <- Seq(SpaceValue(), SpaceValue("a", "b")) do
      soundOn(d, z, "x∖(x∩(x∩x))")(using SpaceContextMap(Map(SpaceMention("x") -> xsv)))
  }

  test("suite programs: z3 dominates the baseline and stays sound") {
    assume(SizeZ3.available, "z3 not on PATH")
    val fam = AuntQuery.context.m(SpaceMention("family"))
    val edges = SpaceValue("a.b", "b.c", "c.d", "z.z")
    def lit(sv: SpaceValue): Space = Space.Literal(sv)
    def bindS(body: Space, m: Map[String, SpaceValue]): Space =
      subs(body)(spre = { case Space.Mention(sm) if m.contains(sm.s) => lit(m(sm.s)) })
    val progs: Seq[(String, Space)] = Seq(
      "aunt-query" -> bindS(Routines.aunt_query_routine.body, Map("family" -> fam, "people" -> SpaceValue("Jim", "Pam"))),
      "child-index" -> bindS(Routines.child_routine.body, Map("family" -> fam)),
      "or-else-empty" -> bindS(Routines.or_else_routine.body, Map("e" -> SpaceValue(), "backup" -> edges)),
      "or-else-nonempty" -> bindS(Routines.or_else_routine.body, Map("e" -> SpaceValue("x.1"), "backup" -> edges)),
      "restr-raff-partition" -> (lit(edges) <| s("a", "b")) .\/(Space.Raffination(lit(edges), s("a", "b"))),
      "product-union" -> (lit(SpaceValue("q.a", "q.b")).iter(P"px", S"ptx",
        lit(SpaceValue("r.c")).iter(P"py", S"pty", Singleton("cux" x P"px") \/ Singleton("cux" x P"py")))))
    var improved = 0
    for (name, p) <- progs do
      val (base, z) = dominated(p, name)
      soundOn(p, z, name)
      if z.lo > base.lo || z.hi < base.hi then improved += 1
      println(f"  z3-suite $name%-22s base=${fmt(base)}%-16s z3=${fmt(z)}")
    println(s"  z3-suite improved on $improved/${progs.size}")
    // the partition program must be EXACT: |x<|y| + |x\|y| = |x| = 4
    val (_, zp) = dominated(progs.collectFirst { case ("restr-raff-partition", p) => p }.get, "partition")
    assertEquals((zp.lo, zp.hi), (4L, 4L), "restriction/raffination partition must pin |x| exactly")
  }

  test("corpus (1000 programs, open + closed): dominance + soundness + improvement stats") {
    assume(SizeZ3.available, "z3 not on PATH")
    val f = new java.io.File(Loaders.repoRoot, "corpus_1000.ser")
    assert(f.exists, "corpus not found — run the corpus test first")
    val recs = locally {
      val ois = new java.io.ObjectInputStream(new java.io.FileInputStream(f))
      try ois.readObject().asInstanceOf[Vector[FuzzRec]] finally ois.close()
    }
    val rng = new java.util.Random(777)
    val A = SpaceFuzzer.alphabet
    def randPath(): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
    def randSV(): SpaceValue = SpaceValue((0 until rng.nextInt(6)).map(_ => randPath()).toSet)
    val sNames = (0 until 3).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until 3).map(j => PathRef("p" + j)).toVector
    var openTightLo = 0; var openTightHi = 0; var closedTight = 0; var fallbacks = 0
    var checked = 0
    for r <- recs do
      val (baseO, zO) = dominated(r.prog, s"open#$checked")
      if zO == baseO then fallbacks += 1
      if zO.lo > baseO.lo then openTightLo += 1
      if zO.hi < baseO.hi then openTightHi += 1
      val svs = Vector.fill(3)(randSV()); val pvs = Vector.fill(3)(randPath())
      val closed = subs(r.prog)(
        spre = { case Space.Mention(m) if sNames.contains(m) => Space.Literal(svs(sNames.indexOf(m))) },
        ppre = { case Path.Deref(pr) if pNames.contains(pr) => Path.Constant(pvs(pNames.indexOf(pr))) })
      val n = eval(closed).paths.size.toLong
      // the OPEN bounds must contain every instantiation's size
      assert(zO.lo <= n && n <= zO.hi, s"open z3 bounds ${fmt(zO)} exclude |eval|=$n for ${r.prog.show}")
      val (baseC, zC) = dominated(closed, s"closed#$checked")
      assert(zC.lo <= n && n <= zC.hi, s"closed z3 bounds ${fmt(zC)} exclude |eval|=$n")
      if zC.lo > baseC.lo || zC.hi < baseC.hi then closedTight += 1
      checked += 1
    println(s"Z3-BOUNDS (corpus): $checked programs; open tighter-lo $openTightLo, tighter-hi $openTightHi;" +
      s" closed tighter $closedTight; identical-to-baseline $fallbacks — all dominated, all sound")
  }
end SizeZ3Check
