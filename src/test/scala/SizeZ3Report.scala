package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** FULL DISTRIBUTION report for the z3-backed size bounds, side by side with the syntactic
 *  baseline, on the SAME sets as the baseline report: the suite's named programs and all 1000
 *  corpus programs — each program's OPEN bounds evaluated against 100 random inputs.  Soundness
 *  and dominance are asserted on every measurement; scope/solver limits are REPORTED as such
 *  (those programs appear in the limits section, not silently folded into the z3 columns). */
class SizeZ3Report extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  val INF = Lower.SizeBounds.INF
  def fmt(b: Lower.SizeBounds): String = s"[${b.lo}, ${if b.hi == INF then "inf" else b.hi}]"

  final class Dist:
    val hiSlack = collection.mutable.ArrayBuffer.empty[Long]   // hi − n, finite his only
    val loSlack = collection.mutable.ArrayBuffer.empty[Long]   // n − lo
    var unbounded = 0; var exactHi = 0; var exactLo = 0; var vacuousLo = 0; var bothExact = 0; var m = 0
    def add(b: Lower.SizeBounds, n: Long): Unit =
      m += 1
      if b.hi == INF then unbounded += 1
      else { hiSlack += b.hi - n; if b.hi == n then exactHi += 1 }
      loSlack += n - b.lo
      if b.lo == n then exactLo += 1
      if b.lo == 0 && n > 0 then vacuousLo += 1
      if b.lo == n && b.hi == n then bothExact += 1
    def pct(xs: collection.mutable.ArrayBuffer[Long], p: Double): Long =
      if xs.isEmpty then 0 else { val v = xs.toVector.sorted; v((p * (v.size - 1)).toInt) }
    def show(label: String): String =
      f"""  $label%-9s measurements=$m
  $label%-9s upper: exact $exactHi (${100.0 * exactHi / (m max 1)}%.1f%%), unbounded $unbounded (${100.0 * unbounded / (m max 1)}%.1f%%); slack(fin) p50=${pct(hiSlack, .5)} p90=${pct(hiSlack, .9)} p99=${pct(hiSlack, .99)} max=${hiSlack.maxOption.getOrElse(0L)}
  $label%-9s lower: exact $exactLo (${100.0 * exactLo / (m max 1)}%.1f%%), vacuous $vacuousLo (${100.0 * vacuousLo / (m max 1)}%.1f%%); slack p50=${pct(loSlack, .5)} p90=${pct(loSlack, .9)} p99=${pct(loSlack, .99)} max=${loSlack.maxOption.getOrElse(0L)}
  $label%-9s both-exact $bothExact (${100.0 * bothExact / (m max 1)}%.1f%%)"""

  val sNames = (0 until 3).map(i => SpaceMention("s" + i)).toVector
  val pNames = (0 until 3).map(j => PathRef("p" + j)).toVector

  def treeNodes(sp: Space): Int = 1 + (sp match
    case Space.Union(a, b) => treeNodes(a) + treeNodes(b)
    case Space.Intersection(a, b) => treeNodes(a) + treeNodes(b)
    case Space.Subtraction(a, b) => treeNodes(a) + treeNodes(b)
    case Space.Restriction(a, b) => treeNodes(a) + treeNodes(b)
    case Space.Raffination(a, b) => treeNodes(a) + treeNodes(b)
    case Space.Composition(a, b) => treeNodes(a) + treeNodes(b)
    case Space.Wrap(a, _) => treeNodes(a)
    case Space.Unwrap(a, _) => treeNodes(a)
    case Space.TailsUnion(a) => treeNodes(a)
    case Space.TailsIntersection(a) => treeNodes(a)
    case Space.Range(a, _, _) => treeNodes(a)
    case Space.Iteration(src, _, _, b) => treeNodes(src) + treeNodes(b)
    case Space.Fold(src, _, _, _, _, b, _) => treeNodes(src) + treeNodes(b)
    case Space.Fixpoint(init, _, b) => treeNodes(init) + treeNodes(b)
    case _ => 0)
  def dagNodes(sp: Space): Int =
    val seen = collection.mutable.Set.empty[Space]
    def go(x: Space): Unit = if seen.add(x) then x match
      case Space.Union(a, b) => go(a); go(b)
      case Space.Intersection(a, b) => go(a); go(b)
      case Space.Subtraction(a, b) => go(a); go(b)
      case Space.Restriction(a, b) => go(a); go(b)
      case Space.Raffination(a, b) => go(a); go(b)
      case Space.Composition(a, b) => go(a); go(b)
      case Space.Wrap(a, _) => go(a)
      case Space.Unwrap(a, _) => go(a)
      case Space.TailsUnion(a) => go(a)
      case Space.TailsIntersection(a) => go(a)
      case Space.Range(a, _, _) => go(a)
      case Space.Iteration(src, _, _, b) => go(src); go(b)
      case Space.Fold(src, _, _, _, _, b, _) => go(src); go(b)
      case Space.Fixpoint(init, _, b) => go(init); go(b)
      case _ => ()
    go(sp); seen.size

  def runDistribution(label: String, progs: Vector[Space]): Unit =
    val rng = new java.util.Random(101010)
    val A = SpaceFuzzer.alphabet
    def randPath(): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
    def randSV(): SpaceValue = SpaceValue((0 until rng.nextInt(6)).map(_ => randPath()).toSet)
    val M = 100
    final case class Env(pc: PathContext, sc: SpaceContext)
    val envs = Array.fill(M)(Env(
      PathContextMap(pNames.map(_ -> randPath()).toMap),
      SpaceContextMap(sNames.map(_ -> randSV()).toMap)))

    val dBase = Dist(); val dZ3 = Dist()
    var solved = 0
    val limits = collection.mutable.Map.empty[String, Int]
    val limitExamples = collection.mutable.Buffer.empty[String]
    var tighterHi = 0; var tighterLo = 0
    var shared = 0
    val bucketTot = collection.mutable.Map.empty[String, Int]
    val bucketWin = collection.mutable.Map.empty[String, Int]
    def bucket(sz: Int): String = if sz < 20 then "  <20" else if sz < 40 then "20-39" else if sz < 80 then "40-79" else " >=80"
    val worst = collection.mutable.ArrayBuffer.empty[(Long, String)]   // (z3 hi-slack, desc) per program
    var t0 = System.nanoTime()
    for (prog, pi) <- progs.zipWithIndex do
      if dagNodes(prog) < treeNodes(prog) then shared += 1
      val base = Lower.sizeBounds(prog)
      val (zb, status) = SizeZ3.boundsWithStatus(prog, timeoutSec = 5)
      val isSolved = status == SizeZ3.Status.Solved
      status match
        case SizeZ3.Status.Solved => solved += 1
        case SizeZ3.Status.ScopeLimited(reason) =>
          limits.updateWith(reason.replaceAll("'[^']*'", "'*'"))(c => Some(c.getOrElse(0) + 1))
          if limitExamples.size < 3 then limitExamples += s"#$pi: $reason"
        case SizeZ3.Status.SolverFailed(d) => limits.updateWith(s"solver: $d")(c => Some(c.getOrElse(0) + 1))
        case SizeZ3.Status.NoSolver => limits.updateWith("no solver")(c => Some(c.getOrElse(0) + 1))
      if isSolved then
        assert(zb.lo >= base.lo && zb.hi <= base.hi, s"#$pi: z3 ${fmt(zb)} outside baseline ${fmt(base)}")
        if zb.hi < base.hi then tighterHi += 1
        if zb.lo > base.lo then tighterLo += 1
        val bk = bucket(treeNodes(prog))
        bucketTot.updateWith(bk)(c => Some(c.getOrElse(0) + 1))
        if zb.hi < base.hi || zb.lo > base.lo then bucketWin.updateWith(bk)(c => Some(c.getOrElse(0) + 1))
      var worstSlack = -1L
      for e <- envs do
        val n = eval(prog)(using e.pc, e.sc).paths.size.toLong
        assert(base.lo <= n && n <= base.hi, s"#$pi: baseline unsound ${fmt(base)} vs $n")
        dBase.add(base, n)
        if isSolved then
          assert(zb.lo <= n && n <= zb.hi, s"#$pi: z3 unsound ${fmt(zb)} vs $n for ${prog.show}")
          dZ3.add(zb, n)
          if zb.hi != INF then worstSlack = worstSlack max (zb.hi - n)
      if worstSlack >= 0 then worst += ((worstSlack, f"#$pi z3=${fmt(zb)} base=${fmt(base)}"))
    val secs = (System.nanoTime() - t0) / 1e9
    println(f"Z3-REPORT ($label): ${progs.size} programs x $M inputs, ${secs}%.0fs; shared-subterm programs $shared/${progs.size}")
    println(s"  scope: solved $solved/${progs.size}; limits: " +
      (if limits.isEmpty then "none" else limits.toList.sortBy(-_._2).map((k, v) => s"$k=$v").mkString(", ")))
    limitExamples.foreach(x => println(s"    e.g. $x"))
    println(dBase.show("baseline"))
    println(dZ3.show("z3"))
    println(s"  z3 strictly tighter than baseline (per program, of $solved solved): upper $tighterHi, lower $tighterLo")
    println("  tighter-by-size: " + bucketTot.toList.sorted.map((k, t) => s"$k: ${bucketWin.getOrElse(k, 0)}/$t").mkString("  "))
    println("  least tight z3 UPPER (finite, per program):")
    worst.sortBy(-_._1).take(3).foreach((sl, d) => println(s"    slack=$sl  $d"))

  test("corpus: 1000 programs x 100 inputs — baseline vs z3 distributions + limits in scope") {
    assume(SizeZ3.available, "z3 not on PATH")
    val f = new java.io.File(Loaders.repoRoot, "corpus_1000.ser")
    assert(f.exists, "corpus not found — run the corpus test first")
    val recs = locally {
      val ois = new java.io.ObjectInputStream(new java.io.FileInputStream(f))
      try ois.readObject().asInstanceOf[Vector[FuzzRec]] finally ois.close()
    }
    runDistribution("corpus, independent draws", recs.map(_.prog))
  }

  test("pooled DEEP fuzzer: 1000 programs (depth 5) x 100 inputs") {
    assume(SizeZ3.available, "z3 not on PATH")
    given rng: java.util.Random = new java.util.Random(0xBEEF)
    val canary = SpaceContextMap(sNames.map(_ -> SpaceValue("a", "b.c", "d")).toMap)
    val canaryP = PathContextMap(pNames.map(_ -> PathValue(List("a"))).toMap)
    def tractable(p: Space): Boolean =
      try eval(p)(using canaryP, canary).paths.size <= 2000 catch case _: Throwable => false
    val progs = Vector.newBuilder[Space]
    var kept = 0; var attempts = 0
    while kept < 1000 && attempts < 20000 do
      attempts += 1
      val arg = SpaceFuzzer.argDist.sample
      val nS = 1 + rng.nextInt(3); val nP = rng.nextInt(3)
      val p = SpaceFuzzer.genProg(arg, 5, sargs = sNames.take(nS), pargs = pNames.take(nP), poolShare = 4).sample
      if treeNodes(p) >= 15 && tractable(p) then { progs += p; kept += 1 }
    println(s"  deep-gen: kept $kept/$attempts sampled (>=15 nodes, canary-tractable)")
    runDistribution("pooled deep, depth 5", progs.result())
  }

  test("pooled fuzzer: 1000 programs x 100 inputs — subterms drawn from a pool") {
    assume(SizeZ3.available, "z3 not on PATH")
    given rng: java.util.Random = new java.util.Random(0xC0FFEE)
    val progs = Vector.fill(1000) {
      val arg = SpaceFuzzer.argDist.sample
      val nS = 1 + rng.nextInt(3); val nP = rng.nextInt(3)
      SpaceFuzzer.genProg(arg, 3, sargs = sNames.take(nS), pargs = pNames.take(nP)).sample
    }
    runDistribution("pooled draws", progs)
  }

  test("suite programs: baseline vs z3 table (with status)") {
    assume(SizeZ3.available, "z3 not on PATH")
    val fam = AuntQuery.context.m(SpaceMention("family"))
    val edges = SpaceValue("a.b", "b.c", "c.d", "z.z")
    val xs = SpaceValue("x.1", "x.2", "y.3")
    def lit(sv: SpaceValue): Space = Space.Literal(sv)
    def bindS(body: Space, m: Map[String, SpaceValue]): Space =
      subs(body)(spre = { case Space.Mention(sm) if m.contains(sm.s) => lit(m(sm.s)) })
    def join(r: Space, s: Space): Space = r.iter(P"n", S"nbs", P"n" x \/(s <| S"nbs"))
    def invert(r: Space): Space = r.iter(P"b", S"as", S"as".iter(P"a", S"_", Singleton(P"a" x P"b")))
    val cells = NOAA.file.map(f => NOAA.load(f.getPath)).getOrElse(Vector.empty)
    val progs = collection.mutable.Buffer[(String, Space, PartialFunction[RoutinePtr, Routine])](
      ("aunt-query(family, 2 people)", bindS(Routines.aunt_query_routine.body, Map("family" -> fam, "people" -> SpaceValue("Jim", "Pam"))), PartialFunction.empty),
      ("child-index(family)", bindS(Routines.child_routine.body, Map("family" -> fam)), PartialFunction.empty),
      ("union-iter(xs, ys)", bindS(Routines.union_iter_routine.body, Map("xs" -> xs, "ys" -> edges)), PartialFunction.empty),
      ("or-else(e = {}, backup)", bindS(Routines.or_else_routine.body, Map("e" -> SpaceValue(), "backup" -> edges)), PartialFunction.empty),
      ("or-else(e nonempty, backup)", bindS(Routines.or_else_routine.body, Map("e" -> xs, "backup" -> edges)), PartialFunction.empty),
      ("datalog-join(edges, edges)", join(lit(edges), lit(edges)), PartialFunction.empty),
      ("datalog-invert(edges)", invert(lit(edges)), PartialFunction.empty),
      ("unification-Q(sequences)", Unification.U(lit(Unification.context.m(SpaceMention("sequences"))), "$x.c.$x", Unification.W(_, "$x.c.$x", _)), PartialFunction.empty),
      ("restr-raff-partition(edges)", (lit(edges) <| s("a", "b")) \/ Space.Raffination(lit(edges), s("a", "b")), PartialFunction.empty))
    for n <- Seq(4, 5) do
      val b = NQueens.board(n)
      progs += ((s"n-queens(n=$n, aoe inlined)", (R"main"() := b.program).optimized(using b.defs).body, b.defs))
    if cells.nonEmpty then
      progs += (("noaa-spatial(lat 8..19)", lit(NOAA.worldBin(cells)) <| lit(NOAA.interval(8, 19, 6)), PartialFunction.empty))
      progs += (("noaa-temp-band(W)", lit(NOAA.worldTemp(cells)) <| s("W"), PartialFunction.empty))
    progs += (("transitive(chain-4) [recursive]", Space.Call(RoutinePtr("transitive"), Vector(), Vector(lit(edges))), Syntax.mod(Routines.transitive_routine)))

    println("Z3-REPORT (suite):")
    var improved = 0; var limited = 0
    for (name, p, rc) <- progs do
      val base = Lower.sizeBounds(p)
      val (zb, status) = SizeZ3.boundsWithStatus(p, timeoutSec = 5)
      val n = eval(p)(using rc = rc).paths.size.toLong
      assert(base.lo <= n && n <= base.hi, s"$name: baseline unsound")
      val statusStr = status match
        case SizeZ3.Status.Solved =>
          assert(zb.lo <= n && n <= zb.hi, s"$name: z3 unsound ${fmt(zb)} vs $n")
          assert(zb.lo >= base.lo && zb.hi <= base.hi, s"$name: not dominated")
          if zb.lo > base.lo || zb.hi < base.hi then { improved += 1; "solved+" } else "solved"
        case SizeZ3.Status.ScopeLimited(r) => limited += 1; s"LIMIT: $r"
        case SizeZ3.Status.SolverFailed(d) => limited += 1; s"FAILED: $d"
        case SizeZ3.Status.NoSolver => "no solver"
      println(f"  $name%-30s n=$n%-6d base=${fmt(base)}%-14s z3=${fmt(zb)}%-14s $statusStr")
    println(s"  suite: improved $improved, scope/solver-limited $limited of ${progs.size}")
  }
end SizeZ3Report
