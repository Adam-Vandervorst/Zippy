package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** TIGHTNESS REPORT for the abstract result-size analysis: run [[Lower.sizeBounds]] over the test
 *  suite's named programs (closed with their canonical data) AND all 1000 fuzzed corpus programs
 *  (closed with random data), assert soundness everywhere, and REPORT how tight the intervals are —
 *  the least tight cases and the distribution of over-/under-estimates.  Tightness is measured,
 *  not asserted: `[0, ∞)` on a recursive entry is sound and expected, not a failure. */
class SizeBoundsReport extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(15, "min")

  val INF = Lower.SizeBounds.INF
  final case class Row(name: String, n: Long, lo: Long, hi: Long):
    def loSlack: Long = n - lo
    def hiSlack: Long = if hi == INF then INF else hi - n
    def show: String =
      val hiS = if hi == INF then "inf" else hi.toString
      val hsS = if hi == INF then "inf" else (hi - n).toString
      f"$name%-34s n=$n%-7d [lo=$lo%-6d hi=$hiS%-8s]  under=$loSlack%-6d over=$hsS%s"

  def measure(name: String, s: Space, rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Row =
    val b = Lower.sizeBounds(s)
    val v = eval(s)(using rc = rc)
    val n = v.paths.size.toLong
    val nH = v.paths.count(_.items.nonEmpty).toLong
    assert(b.lo <= n && n <= b.hi, s"UNSOUND on $name: |eval|=$n outside [${b.lo}, ${b.hi}]")
    assert(b.loHeaded <= nH, s"UNSOUND on $name: headed=$nH below ${b.loHeaded}")
    Row(name, n, b.lo, b.hi)

  def lit(sv: SpaceValue): Space = Space.Literal(sv)
  def bindS(body: Space, m: Map[String, SpaceValue]): Space =
    subs(body)(spre = { case Space.Mention(sm) if m.contains(sm.s) => lit(m(sm.s)) })

  test("test-suite programs: sound; per-program tightness table") {
    val fam = AuntQuery.context.m(SpaceMention("family"))
    val edges = SpaceValue("a.b", "b.c", "c.d", "z.z")
    val xs = SpaceValue("x.1", "x.2", "y.3")
    val rows = collection.mutable.ArrayBuffer.empty[Row]

    // --- closed, non-recursive algebra ---
    rows += measure("aunt-query(family, 2 people)",
      bindS(Routines.aunt_query_routine.body, Map("family" -> fam, "people" -> SpaceValue("Jim", "Pam"))))
    rows += measure("child-index(family)", bindS(Routines.child_routine.body, Map("family" -> fam)))
    rows += measure("union-iter(xs, ys)",
      bindS(Routines.union_iter_routine.body, Map("xs" -> xs, "ys" -> edges)))
    rows += measure("or-else(e = {}, backup)",
      bindS(Routines.or_else_routine.body, Map("e" -> SpaceValue(), "backup" -> edges)))
    rows += measure("or-else(e nonempty, backup)",
      bindS(Routines.or_else_routine.body, Map("e" -> xs, "backup" -> edges)))
    def join(r: Space, s: Space): Space = r.iter(P"n", S"nbs", P"n" x \/(s <| S"nbs"))
    def invert(r: Space): Space = r.iter(P"b", S"as", S"as".iter(P"a", S"_", Singleton(P"a" x P"b")))
    rows += measure("datalog-join(edges, edges)", join(lit(edges), lit(edges)))
    rows += measure("datalog-invert(edges)", invert(lit(edges)))
    rows += measure("unification-Q(sequences, $x.c.$x)",
      Unification.U(lit(Unification.context.m(SpaceMention("sequences"))), "$x.c.$x",
        Unification.W(_, "$x.c.$x", _)))

    // --- inlined (non-recursive routines folded away by optimized()) ---
    for n <- Seq(4, 5, 6) do
      val b = NQueens.board(n)
      val body = (R"main"() := b.program).optimized(using b.defs).body
      rows += measure(s"n-queens(n=$n, aoe inlined)", body, b.defs)
    val rules = GoL.Rules(0, 7)
    val glider = SpaceValue(Set((1,0),(2,1),(0,2),(1,2),(2,2)).map((x,y) => Syntax.parse(s"Cell.$x.$y")))
    val golBody = (R"main"() := Space.Call(RoutinePtr("nextStep"), Vector(), Vector(lit(glider)))).optimized(using rules.defs).body
    rows += measure("gol-nextStep(glider, 8x8)", golBody, rules.defs)

    // --- NOAA spatial/temperature queries (2592-cell fixture) ---
    val cells = NOAA.file.map(f => NOAA.load(f.getPath)).getOrElse(Vector.empty)
    if cells.nonEmpty then
      rows += measure("noaa-spatial(lat 8..19)", lit(NOAA.worldBin(cells)) <| lit(NOAA.interval(8, 19, 6)))
      rows += measure("noaa-temp-band(W)", lit(NOAA.worldTemp(cells)) <| s("W"))

    // --- recursive entries: bounds are vacuous by design (Call/Fixpoint widen) ---
    rows += measure("transitive(chain-4)  [recursive]",
      Space.Call(RoutinePtr("transitive"), Vector(), Vector(lit(edges))), Syntax.mod(Routines.transitive_routine))
    val p22 = Sliding.puzzle(2, 2)
    rows += measure("sliding-2x2 entry    [recursive]", p22.entry, p22.defs)

    println("SIZE-TIGHTNESS (suite):")
    rows.foreach(r => println("  " + r.show))
    val finite = rows.filter(_.hi != INF)
    val worstOver = finite.maxByOption(_.hiSlack)
    val worstUnder = rows.maxByOption(_.loSlack)
    println(s"  -- least tight upper (finite): ${worstOver.map(_.show).getOrElse("-")}")
    println(s"  -- least tight lower         : ${worstUnder.map(_.show).getOrElse("-")}")
    println(s"  -- vacuous [0,inf) rows      : ${rows.count(r => r.hi == INF && r.lo == 0)} (recursive entries)")
  }

  test("corpus (1000 programs x 5 closed instances): sound; over/under-estimate distribution") {
    val recs = Corpus.load()
    val rng = new java.util.Random(20260713)
    val A = SpaceFuzzer.alphabet
    def randPath(): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
    def randSV(): SpaceValue = SpaceValue((0 until rng.nextInt(6)).map(_ => randPath()).toSet)
    val sNames = (0 until 3).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until 3).map(j => PathRef("p" + j)).toVector

    val rows = collection.mutable.ArrayBuffer.empty[(Row, String)]
    for r <- recs; k <- 0 until 5 do
      val svs = Vector.fill(3)(randSV()); val pvs = Vector.fill(3)(randPath())
      val closed = subs(r.prog)(
        spre = { case Space.Mention(m) if sNames.contains(m) => lit(svs(sNames.indexOf(m))) },
        ppre = { case Path.Deref(pr) if pNames.contains(pr) => Path.Constant(pvs(pNames.indexOf(pr))) })
      rows += ((measure(s"corpus#${rows.size / 5}/$k", closed), closed.show))

    val n = rows.size
    def pct(xs: Vector[Long], p: Double): Long = if xs.isEmpty then 0 else xs((p * (xs.size - 1)).toInt)
    val hiFinite = rows.filter(_._1.hi != INF)
    val hiSlacks = hiFinite.map(_._1.hiSlack).toVector.sorted
    val loSlacks = rows.map(_._1.loSlack).toVector.sorted
    def bucketize(v: Long, exactLbl: String): String =
      if v == 0 then exactLbl else if v <= 2 then "+1..2" else if v <= 8 then "+3..8" else if v <= 32 then "+9..32" else ">32"
    val hiBuckets = hiFinite.groupBy(r => bucketize(r._1.hiSlack, "exact")).view.mapValues(_.size).toMap
    val loBuckets = rows.groupBy(r => bucketize(r._1.loSlack, "exact")).view.mapValues(_.size).toMap

    println(s"SIZE-TIGHTNESS (corpus): $n closed instances, all sound")
    println(f"  upper: exact ${hiBuckets.getOrElse("exact", 0)}, finite ${hiFinite.size}, unbounded(inf) ${n - hiFinite.size}")
    println(s"  upper-slack (hi - n) over finite: p50=${pct(hiSlacks, .5)} p90=${pct(hiSlacks, .9)} p99=${pct(hiSlacks, .99)} max=${hiSlacks.lastOption.getOrElse(0L)}")
    println(s"  upper buckets: ${hiBuckets.toList.sortBy(_._1).map((k, v) => s"$k=$v").mkString("  ")}")
    println(f"  lower: exact ${loBuckets.getOrElse("exact", 0)}, vacuous(lo=0,n>0) ${rows.count(r => r._1.lo == 0 && r._1.n > 0)}")
    println(s"  lower-slack (n - lo): p50=${pct(loSlacks, .5)} p90=${pct(loSlacks, .9)} p99=${pct(loSlacks, .99)} max=${loSlacks.lastOption.getOrElse(0L)}")
    println(s"  lower buckets: ${loBuckets.toList.sortBy(_._1).map((k, v) => s"$k=$v").mkString("  ")}")
    println(s"  both-exact instances: ${rows.count(r => r._1.loSlack == 0 && r._1.hiSlack == 0)}")
    def clip(s: String): String = { val one = s.replaceAll("\\s+", " "); if one.length > 110 then one.take(110) + "…" else one }
    println("  least tight UPPER (finite):")
    hiFinite.sortBy(-_._1.hiSlack).take(3).foreach((r, sh) => println(s"    ${r.show}\n      ${clip(sh)}"))
    println("  least tight LOWER:")
    rows.sortBy(-_._1.loSlack).take(3).foreach((r, sh) => println(s"    ${r.show}\n      ${clip(sh)}"))
  }
end SizeBoundsReport
