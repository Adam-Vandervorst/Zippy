package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions
import scala.io.Source

/** Tag for heavy/integration tests (full 3x3 puzzle state space, large n-queens). They still
 *  run by default; filter them with munit's `--exclude-tags Slow`
 *  (`sbt 'testOnly * -- --exclude-tags=Slow'`). */
object SlowTag:
  val Slow = new munit.Tag("Slow")

/** Loaders that turn external datasets into MORKL spaces (sets of dotted paths).
 *  Path resolution is portable: a candidate list is tried in order (env override, repo-relative,
 *  known local locations) and the first existing file wins; callers supply a deterministic
 *  fallback so the suite runs in a fresh checkout with no external data. */
object Loaders:
  /** Nearest ancestor directory containing build.sbt (the repo root), from the run cwd. */
  lazy val repoRoot: java.io.File =
    var d = new java.io.File(".").getCanonicalFile
    while d != null && !new java.io.File(d, "build.sbt").exists do d = d.getParentFile
    if d != null then d else new java.io.File(".").getCanonicalFile

  /** First existing path among candidates (absolute or repo-root-relative). */
  def resolve(candidates: String*): Option[java.io.File] =
    candidates.iterator.map { c =>
      val f = new java.io.File(c)
      if f.isAbsolute then f else new java.io.File(repoRoot, c)
    }.find(_.exists)

  def fileOpt(path: String): Option[Vector[String]] = resolve(path).map(readLines)
  def readLines(f: java.io.File): Vector[String] =
    val s = Source.fromFile(f); try s.getLines().toVector finally s.close()

  /** Optional progress note, gated behind -Dsc.verbose=true so the default suite stays clean. */
  def note(msg: => String): Unit = if sys.props.get("sc.verbose").contains("true") then System.out.println(msg)

  // ---- lot.metta genealogy -> family/people spaces -------------------------
  private val Parent = """\(parent\s+"([^"]+)"\s+"([^"]+)"\)""".r
  private val Female = """\(female\s+"([^"]+)"\)""".r
  private val Male   = """\(male\s+"([^"]+)"\)""".r
  private val HasName = """\(hasName\s+"([^"]+)"\s+"([^"]+)"\)""".r

  case class Family(family: SpaceValue, people: SpaceValue, names: Map[String, String])

  def mettaFamily(path: String): Option[Family] = fileOpt(path).map { lines =>
    val ps = collection.mutable.Set.empty[PathValue]
    val ids = collection.mutable.LinkedHashSet.empty[String]
    val names = collection.mutable.Map.empty[String, String]
    def sym(items: String*): PathValue = PathValue(items.toList)
    for l <- lines do l.trim match
      case Parent(p, c) => ps += sym("parent", p, c); ps += sym("child", c, p); ids += p; ids += c
      case Female(x)    => ps += sym("female", x); ids += x
      case Male(x)      => ps += sym("male", x);   ids += x
      case HasName(i,n) => names(i) = n
      case _ => ()
    for i <- ids do ps += sym("person", i)
    Family(SpaceValue(ps.toSet), SpaceValue(ids.map(i => sym(i)).toSet), names.toMap)
  }

  // ---- Conway RLE -> live cell set -----------------------------------------
  private val RleHeader = """x\s*=\s*(\d+).*y\s*=\s*(\d+).*""".r
  def parseRLE(path: String): Option[(Set[(Int, Int)], Int, Int)] = fileOpt(path).map { lines =>
    val content = lines.filterNot(_.startsWith("#"))
    val (w, h) = content.headOption.map(_.trim) match
      case Some(RleHeader(x, y)) => (x.toInt, y.toInt)
      case _ => (0, 0)
    val body = content.drop(1).mkString("")
    val live = collection.mutable.Set.empty[(Int, Int)]
    var x = 0; var y = 0; var count = 0
    for ch <- body do ch match
      case d if d.isDigit => count = count * 10 + (d - '0')
      case 'b' | 'B' => x += math.max(count, 1); count = 0
      case 'o' | 'O' => val n = math.max(count, 1); for _ <- 0 until n do { live += ((x, y)); x += 1 }; count = 0
      case '$' => y += math.max(count, 1); x = 0; count = 0
      case '!' => ()
      case _ => ()
    (live.toSet, w, h)
  }

  // ---- carac datalog DSL: parse `edge("a", "b") :- ()` base facts of a given relation ----
  def caracEdges(relation: String, candidates: String*): Option[Vector[(String, String)]] =
    val fact = (s"""\\b$relation\\("([^"]+)",\\s*"([^"]+)"\\)\\s*:-\\s*\\(\\)""").r
    resolve(candidates*).map { f =>
      readLines(f).flatMap(l => fact.findFirstMatchIn(l).map(m => m.group(1) -> m.group(2)))
    }.filter(_.nonEmpty)
end Loaders

/** Guiding example 1: graph query (Aunt) over the lot.metta genealogy. */
class ExAuntMetta extends FunSuite:
  import Space.*

  // portable resolution: env override, repo-relative, then known local checkout
  val lotCandidates = Seq(sys.props.getOrElse("lot.metta", "lot.metta"), "lot.metta",
                          sys.env.getOrElse("ZIPPY_DATA", "data") + "/lot.metta")
  /** Real lot.metta if present, else the in-repo AuntQuery fixture (so the suite runs anywhere). */
  val fam: Loaders.Family =
    Loaders.resolve(lotCandidates*).flatMap(f => Loaders.mettaFamily(f.getPath)).getOrElse(
      Loaders.Family(AuntQuery.context.resolve(SpaceMention("family")),
                     AuntQuery.context.resolve(SpaceMention("people")), Map.empty))

  test("aunt query: SC residual eval-agrees with original (family static, lot.metta or fixture)") {
        val defs = Syntax.mod(Routines.aunt_query_routine)
        // Partial evaluation: family baked in as a literal, `people` left dynamic.
        val call = Space.Call(RoutinePtr("aunts"), Vector(), Vector(Space.Literal(fam.family), Space.Mention(SpaceMention("people"))))
        val res = SC.supercompile(call, defs)
        val sc = SpaceContextMap(Map(SpaceMention("people") -> fam.people))
        val got  = eval(res.top)(using PathContextMap(Map.empty), sc, res.env)
        val orig = eval(call)(using PathContextMap(Map.empty), sc, defs)
        assertEquals(got, orig)
        assert(got.paths.nonEmpty, "expected some aunts in the Tolkien genealogy")
        // residual should have dropped the `family` parameter (specialized away)
        val entryRoutine = res.routines(res.top.asInstanceOf[Space.Call].r)
        assert(!entryRoutine.mentions.exists(_.s == "family"),
               s"family should be specialized away; params=${entryRoutine.mentions}")
        // show a few resolved aunt->niece/nephew name pairs
        val pairs = got.paths.toVector.take(5).map { p =>
          val a = p.items(1)
          val n = p.items(2)
          s"${fam.names.getOrElse(a, a)} is aunt of ${fam.names.getOrElse(n, n)}"
        }
        Loaders.note(s"[aunt/metta] ${got.paths.size} aunt-pairs; e.g.\n  ${pairs.mkString("\n  ")}")
  }

  test("lot.metta relation counts (verified when the real file is present)") {
    val f = Loaders.resolve(lotCandidates*)
    assume(f.isDefined, "lot.metta not present in this checkout")
    val real = Loaders.mettaFamily(f.get.getPath).get
    def heads(rel: String) = real.family.paths.count(_.items.headOption.contains(rel))
    assertEquals(heads("parent"), 117); assertEquals(heads("child"), 117)
    assertEquals(heads("female"), 40);  assertEquals(heads("male"), 46)
    assertEquals(real.people.paths.size, 101) // distinct ids appearing in parent/female/male facts
  }
end ExAuntMetta

/** Guiding example 2: semi-naive datalog (transitive closure) incl. the carac graphs. */
class ExDatalog extends FunSuite:
  import Space.*

  // carac edge sets: parsed from the carac repo's Scala DSL fixtures when present, else the
  // same fact sets inline (so the suite is portable). Relation names follow carac (`e`/`edge`).
  def caracOr(rel: String, fixture: Vector[(String, String)], graph: String): Vector[(String, String)] =
    Loaders.caracEdges(rel, sys.props.getOrElse("carac", "carac") + s"/src/test/scala/test/graphs/$graph.scala",
      System.getProperty("user.home") + s"/carac/src/test/scala/test/graphs/$graph.scala").getOrElse(fixture)
  val recursivePath = caracOr("e",    Vector("a"->"b", "b"->"c", "c"->"d"), "RecursivePath")
  val acyclic       = caracOr("edge", Vector("a"->"a", "a"->"b", "b"->"c", "c"->"d"), "Acyclic")
  val topSort       = caracOr("edge", Vector("A"->"B","A"->"D","A"->"E","B"->"C","C"->"D","C"->"E","D"->"E",
                             "E"->"F","F"->"G","F"->"H","F"->"I","G"->"J","H"->"K","I"->"L",
                             "J"->"M","K"->"M","L"->"M"), "TopSort")

  def edgeSpace(es: Vector[(String, String)]): SpaceValue =
    SpaceValue(es.map((a, b) => PathValue(List(a, b))).toSet)

  /** Independent reference: transitive closure by fixpoint over string pairs. */
  def refTC(es: Vector[(String, String)]): Set[(String, String)] =
    var s = es.toSet; var grown = true
    while grown do
      val add = for (a, b) <- s; (c, d) <- s if b == c yield (a, d)
      val ns = s ++ add; grown = ns.size != s.size; s = ns
    s
  def toPairs(sv: SpaceValue): Set[(String, String)] =
    sv.paths.map(p => (p.items(0), p.items(1)))

  // naive: doubling fixpoint (Routines.transitive_routine)
  // semi-naive: maintain (all, delta); only join the frontier delta with edges.
  val seminaive = R"sn_tc"(S"edges", S"all", S"delta") :=
    S"all" \/ R"sn_tc"(S"edges",
      S"all" \/ (S"delta".iter(P"n", S"nbs", P"n" x \/(S"edges" <| S"nbs")) \ S"all"),
      S"delta".iter(P"n", S"nbs", P"n" x \/(S"edges" <| S"nbs")) \ S"all")

  def snEntry(edges: SpaceValue): Space =
    Space.Call(RoutinePtr("sn_tc"), Vector(), Vector(Space.Literal(edges), Space.Literal(edges), Space.Literal(edges)))

  for (name, es) <- Vector("RecursivePath" -> recursivePath, "Acyclic" -> acyclic, "TopSort" -> topSort) do
    test(s"datalog TC on carac/$name: naive == semi-naive == reference; SC sound") {
      val edges = edgeSpace(es)
      val reference = refTC(es)
      // naive via plain eval
      val naiveDefs = Syntax.mod(Routines.transitive_routine)
      val naive = eval(Space.Call(RoutinePtr("transitive"), Vector(), Vector(Space.Literal(edges))))(using rc = naiveDefs)
      assertEquals(toPairs(naive), reference, s"naive TC mismatch on $name")
      // semi-naive via plain eval
      val snDefs = Syntax.mod(seminaive)
      val sn = eval(snEntry(edges))(using rc = snDefs)
      assertEquals(toPairs(sn), reference, s"semi-naive TC mismatch on $name")
      // supercompile semi-naive (static graph) -> residual must agree
      val res = SC.supercompile(snEntry(edges), snDefs)
      val got = eval(res.top)(using PathContextMap(Map.empty), SpaceContextMap(Map.empty), res.env)
      assertEquals(toPairs(got), reference, s"SC residual TC mismatch on $name")
      Loaders.note(s"[datalog/$name] |E|=${es.size} |TC|=${reference.size}  SC nodes=${res.routines.size}")
    }

  test("generic semi-naive TC: SC residual reproduces (edges dynamic, sound)") {
    val snDefs = Syntax.mod(seminaive)
    val res = SC.supercompile(seminaive, snDefs)
    val edges = edgeSpace(recursivePath)
    val sc = SpaceContextMap(Map(SpaceMention("edges") -> edges, SpaceMention("all") -> edges, SpaceMention("delta") -> edges))
    val got  = eval(res.top)(using PathContextMap(Map.empty), sc, res.env)
    val orig = eval(seminaive.body)(using PathContextMap(Map.empty), sc, snDefs)
    assertEquals(got, orig)
    assertEquals(toPairs(got), refTC(recursivePath))
  }
end ExDatalog

/** Game of Life in the MORKL set algebra (B3/S23), reproduced from the `gol` test so we can run
 *  it on loaded data and supercompile it.  This is now a PURE program (no grounded host functions):
 *
 *   - the neighbour arithmetic `coord + offset` for offsets {-1, 0, 1} is precomputed (in Scala,
 *     cf. NQueens' `add`/`sub`/`upto`) into three 1-D number relations over the coordinate window
 *     `lo..hi`: `succ = {n.(n+1)}`, `decr = {n.(n-1)}`, `idr = {n.n}`.  Applying a relation to a
 *     number `n` is an `Unwrap`: `succ(P"n")` strips the prefix `n` and yields the single tail
 *     `{n+1}` (and the *empty* set at the window edge, which harmlessly clips a neighbour that
 *     would leave the window — hence [[windowFor]] pads the field by 2 so no real count is lost).
 *     `neigh(x, y)` is then the union over the 9 offset pairs of `relX(x) x relY(y)`, minus self.
 *   - the live-neighbour count test uses the ordered-slice [[Space.Range]] as a cardinality
 *     predicate: `Range(s, k, k+1)` is the element at sorted index `k-1`, so it is non-empty iff
 *     `|s| >= k`.  "Exactly k live neighbours" is then `(>=k) \ (>=k+1)` (see [[Rules.exactly]]),
 *     gated onto the cell itself with `.tee(Singleton(x.y))`.
 *
 *  Because the window is finite, [[Rules]] is parameterised by it; [[rulesFor]] derives a padded
 *  window from a cell set.  [[step]] remains a plain-Scala reference for correctness checks. */
object GoL:
  import Space.*

  /** The MORKL routines `neigh`/`nextStep` over a fixed integer coordinate window `lo..hi`. */
  class Rules(lo: Int, hi: Int):
    /** {n.f(n)} over the window, keeping only pairs whose image also stays inside it */
    private def numberRel(f: Int => Int): Space =
      s((lo to hi).collect { case n if f(n) >= lo && f(n) <= hi => Syntax.parse(s"$n.${f(n)}") }.toSeq*)
    val succ: Space = numberRel(_ + 1)   // offset +1
    val decr: Space = numberRel(_ - 1)   // offset -1
    val idr:  Space = numberRel(identity) // offset  0
    private val rel: Map[Int, Space] = Map(-1 -> decr, 0 -> idr, 1 -> succ)

    /** "Exactly k elements of `count`, gated onto `cell`", via the ordered-slice boundary test:
     *  `Range(count, k, k+1)` is non-empty iff `|count| >= k`, so exactly-k = `(>=k) \ (>=k+1)`. */
    private def exactly(k: Int, count: Space, cell: Space): Space =
      (Range(count, k, k + 1).tee(cell)) \ (Range(count, k + 1, k + 2).tee(cell))

    val defs: PartialFunction[RoutinePtr, Routine] =
      case RoutinePtr("neigh") => R"neigh"(P"x", P"y") := {
        // the 9 offset images: cross-product of the per-axis relation applied to x and to y; drop self
        val offsets = Seq(-1, 0, 1)
        (for dx <- offsets; dy <- offsets yield rel(dx)(P"x") x rel(dy)(P"y")).reduce(_ \/ _) \ (sP"x" x sP"y")
      }
      case RoutinePtr("nextStep") => R"nextStep"(S"field") := "Cell" x ((
        // survive: a live cell with exactly 2 live neighbours
        S"field"("Cell").iter(P"x", S"ys", S"ys".iter(P"y", S"_",
          exactly(2, R"neigh"(P"x", P"y") /\ S"field"("Cell"), Singleton(P"x" x P"y"))))
        \/
        // survive-on-3 / birth: any neighbour-of-a-live-cell with exactly 3 live neighbours
        S"field"("Cell").iter(P"x", S"ys", S"ys".iter(P"y", S"_",
          R"neigh"(P"x", P"y"))).iter(P"x", S"ys", S"ys".iter(P"y", S"_",
          exactly(3, R"neigh"(P"x", P"y") /\ S"field"("Cell"), Singleton(P"x" x P"y"))))
      ): Space)

  /** Padded coordinate window for a cell set: ±2 so neighbour relations never clip a real count
   *  (a cell's count needs its 8 neighbours in-window, and arm 2 counts neighbours-of-neighbours). */
  def windowFor(live: Set[(Int, Int)]): (Int, Int) =
    val cs = live.flatMap((x, y) => Seq(x, y))
    if cs.isEmpty then (0, 0) else (cs.min - 2, cs.max + 2)
  def rulesFor(live: Set[(Int, Int)]): Rules = { val (lo, hi) = windowFor(live); new Rules(lo, hi) }

  def field(cells: Set[(Int, Int)]): SpaceValue =
    SpaceValue(cells.map((x, y) => PathValue(List("Cell", x.toString, y.toString))))
  def cells(sv: SpaceValue): Set[(Int, Int)] =
    sv.paths.collect { case PathValue("Cell"::x::y::Nil) => (x.toInt, y.toInt) }
  /** Independent reference: one B3/S23 step on the infinite plane. */
  def step(live: Set[(Int, Int)]): Set[(Int, Int)] =
    val counts = collection.mutable.Map.empty[(Int, Int), Int]
    for (x, y) <- live; dx <- -1 to 1; dy <- -1 to 1 if dx != 0 || dy != 0 do
      val k = (x + dx, y + dy); counts(k) = counts.getOrElse(k, 0) + 1
    counts.iterator.collect { case (c, n) if n == 3 || (n == 2 && live(c)) => c }.toSet
  def steps(live: Set[(Int, Int)], k: Int): Set[(Int, Int)] = (0 until k).foldLeft(live)((s, _) => step(s))
end GoL

class ExGameOfLife extends FunSuite:
  import Space.*

  val fredFile = Loaders.resolve(sys.props.getOrElse("fred.rle", "fred.rle"),
    "tests/fred.rle", sys.env.getOrElse("ZIPPY_DATA", "data") + "/fred.rle")

  def runMorkl(live: Set[(Int, Int)]): Set[(Int, Int)] =
    GoL.cells(eval(Space.Call(RoutinePtr("nextStep"), Vector(), Vector(Space.Literal(GoL.field(live)))))(using rc = GoL.rulesFor(live ++ GoL.step(live)).defs))

  test("blinker oscillates (MORKL nextStep == reference)") {
    val blinker = Set((1, 0), (1, 1), (1, 2))
    assertEquals(runMorkl(blinker), GoL.step(blinker))
    assertEquals(runMorkl(blinker), Set((0, 1), (1, 1), (2, 1)))
  }

  test("random field: SC residual eval-agrees with reference (1 step)") {
    // deterministic pseudo-random field in a 12x12 box
    val rnd = new scala.util.Random(42)
    val live = (for x <- 0 until 12; y <- 0 until 12 if rnd.nextInt(100) < 35 yield (x, y)).toSet
    val reference = GoL.step(live)
    assertEquals(runMorkl(live), reference, "plain MORKL step")
    val call = Space.Call(RoutinePtr("nextStep"), Vector(), Vector(Space.Literal(GoL.field(live))))
    val res = SC.supercompile(call, GoL.rulesFor(live ++ reference).defs)
    val got = GoL.cells(eval(res.top)(using PathContextMap(Map.empty), SpaceContextMap(Map.empty), res.env))
    assertEquals(got, reference, "SC residual step")
    Loaders.note(s"[gol/random] live=${live.size} -> ${reference.size}; SC nodes=${res.routines.size}")
  }

  test("fred.rle: load + one MORKL step == reference") {
    assume(fredFile.isDefined, "fred.rle not present in this checkout (set -Dfred.rle=... to run)")
    Loaders.parseRLE(fredFile.get.getPath) match
      case None => fail("fred.rle present but unparseable")
      case Some((live, w, h)) =>
        assertEquals((w, h), (20, 20))
        assert(live.size > 50, s"fred should be dense, got ${live.size}")
        assertEquals(runMorkl(live), GoL.step(live))
        Loaders.note(s"[gol/fred] ${live.size} live cells in ${w}x${h} -> ${GoL.step(live).size} after 1 step")
  }

  test("two-step fusion: SC fuses nextStep∘nextStep (deforestation)") {
    val glider = Set((1, 0), (2, 1), (0, 2), (1, 2), (2, 2))
    val twoStep = Space.Call(RoutinePtr("nextStep"), Vector(), Vector(
      Space.Call(RoutinePtr("nextStep"), Vector(), Vector(Space.Literal(GoL.field(glider))))))
    val res = SC.supercompile(twoStep, GoL.rulesFor(glider ++ GoL.step(glider) ++ GoL.steps(glider, 2)).defs)
    val got = GoL.cells(eval(res.top)(using PathContextMap(Map.empty), SpaceContextMap(Map.empty), res.env))
    assertEquals(got, GoL.steps(glider, 2))
    Loaders.note(s"[gol/glider] 2-step fused; glider moved to ${GoL.steps(glider, 2).toVector.sorted}")
  }
end ExGameOfLife

/** Guiding example 4: classical n-queens as a recursive MORKL search.
 *  A partial placement is a path of column symbols (one per row). Each level extends
 *  every safe partial by one column; grounded predicates do the diagonal/column arithmetic
 *  (mirroring how the `gol` example uses grounded arithmetic). */
/** Guiding example 4: classical n-queens as a PURE MORKL program (no grounded functions).
 *  The arithmetic is precomputed into literal relations `add`/`sub`/`upto` (built at construction
 *  time); `aoe` is "attacks-or-equal"; `place(k,n)` places k queens via nested `iterk`.  A solution
 *  is encoded as the first n items of a result path (the rest is a decorating attack-set tail), so
 *  the count is the number of distinct length-n prefixes (Trie.prefixCount). */
object NQueens:
  import Space.*
  val known = Map(4 -> 2, 5 -> 10, 6 -> 4, 7 -> 40, 8 -> 92, 9 -> 352, 10 -> 724, 11 -> 2680, 12 -> 14200)
  class Board(nn: Int):
    val add: Space = s((1 to nn).flatMap(i => (1 to nn).map(j => Syntax.parse(s"${i}.${j}.${i + j}")))*)
    val sub: Space = s((1 to nn).flatMap(i => (1 to i).map(j => Syntax.parse(s"${i}.${j}.${i - j}")))*)
    val upto: Space = s((1 to nn).flatMap(i => (1 to i).map(j => Syntax.parse(s"${i}.${j}")))*)
    val aoe_routine: Routine = R"aoe"(P"r", P"c", P"n") := upto(P"n").iterh(P"i",
        (P"c" x sP"i") \/ (P"i" x sP"r") \/
        (add(P"c")(P"i") x add(P"r")(P"i")) \/ (add(P"c")(P"i") x sub(P"r")(P"i")) \/
        (sub(P"c")(P"i") x add(P"r")(P"i")) \/ (sub(P"c")(P"i") x sub(P"r")(P"i"))
      ) /\ (upto(P"n") x upto(P"n"))
    def defs: PartialFunction[RoutinePtr, Routine] = Syntax.mod(aoe_routine)
    def place(k: Int, n: Int): Space =
      if k == 0 then Space.Empty
      else
        val kp = Path.Constant(PathValue(k.toString :: Nil))
        val np = Path.Constant(PathValue(n.toString :: Nil))
        place(k - 1, n).iterk(k - 1, S"taken", qs =>
          (upto(np) \ S"taken"(kp)).iterh(P"q", P"q" x (qs x (R"aoe"(P"q", kp, np) \/ S"taken"))))
    def program: Space = place(nn, nn)
  def board(n: Int): Board = new Board(n)
  /** solution count = distinct length-n prefixes of the (trie-)evaluated program */
  def solutionsT(n: Int): Int = { val b = board(n); evalT(b.program)(using rc = b.defs).prefixCount(n) }
  def solutionsEval(n: Int): Int =
    val b = board(n); eval(b.program)(using rc = b.defs).paths.map(p => PathValue(p.items.take(n))).size
end NQueens

class ExNQueens extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  // small boards under the reference Set evaluator
  for n <- 4 to 8 do
    test(s"n-queens n=$n (pure): eval count == OEIS A000170 (${NQueens.known(n)})") {
      assertEquals(NQueens.solutionsEval(n), NQueens.known(n))
    }

  test("n-queens n=8 (pure): SC residual eval-agrees with original") {
    val b = NQueens.board(8)
    val res = SC.supercompile(b.program, b.defs)
    val got = eval(res.top)(using PathContextMap(Map.empty), SpaceContextMap(Map.empty), res.env)
    val orig = eval(b.program)(using rc = b.defs)
    assertEquals(got, orig)
    assertEquals(got.paths.map(p => PathValue(p.items.take(8))).size, 92)
  }

  // larger boards (trie evaluator) — 9..12
  for n <- Seq(9, 10, 11, 12) do
    test(s"n-queens n=$n (pure, trie): solutions == ${NQueens.known(n)}".tag(SlowTag.Slow)) {
      val t0 = System.nanoTime()
      assertEquals(NQueens.solutionsT(n), NQueens.known(n))
      Loaders.note(s"[queens/n=$n] ${NQueens.known(n)} solutions in ${(System.nanoTime - t0) / 1000000}ms")
    }
end ExNQueens

/** Guiding example 5: sliding-tile puzzle state space as a PURE MORKL program (no grounded
 *  functions). Cells `c0..c(rc-1)` (row-major); a state is `blankCell.tile1...tile_{rc-1}` with
 *  tiles listed in the fixed order of the non-blank cells. `moves`/`all_moves` encode the swap
 *  permutations; `superpose` labels a compact state, `collapse` re-compacts it, and `explore`
 *  is BFS reachability to a fixpoint. Generalizes to any rows x cols. */
object Sliding:
  import Space.*
  /** Nest k Iterations exposing each head as a named PathRef (the n-ary `iter`). */
  def iterN(src: Space, heads: Vector[PathRef], rest: SpaceMention, body: Space): Space =
    val marked = subs(body)(ppre = { case Path.Deref(pr) if heads.contains(pr) => Path.Deref(pr.known(1)) })
    def rec(i: Int, cur: Space): Space =
      if i == heads.size - 1 then Space.Iteration(cur, heads(i).known(1), rest, marked)
      else
        val mid = SpaceMention(s"__n${i}h${math.abs(ProofTrace.structural(body).hashCode)}")
        Space.Iteration(cur, heads(i).known(1), mid, rec(i + 1, Space.Mention(mid)))
    rec(0, src)

  class Puzzle(rows: Int, cols: Int):
    val n: Int = rows * cols
    val cells: Vector[String] = (0 until n).map(i => s"c$i").toVector
    private def rc(i: Int) = (i / cols, i % cols)
    private def neighbors(i: Int): Vector[Int] =
      val (r, c) = rc(i)
      Vector((r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1))
        .filter((rr, cc) => rr >= 0 && rr < rows && cc >= 0 && cc < cols).map((rr, cc) => rr * cols + cc)
    private def others(b: String): Vector[String] = cells.filterNot(_ == b)
    private def tileRefs(k: Int): Vector[PathRef] = (0 until k).map(i => PathRef(s"ft$i")).toVector

    val id_map: Space = s(cells.map(c => Syntax.parse(s"$c.$c"))*)
    val moves: Space =
      (for i <- 0 until n; j <- neighbors(i) yield
        (ss"${cells(i)}.${cells(j)}": Space) x s(Syntax.parse(s"${cells(i)}.${cells(j)}"), Syntax.parse(s"${cells(j)}.${cells(i)}"))
      ).reduce(_ \/ _)
    val all_moves: Space = moves.iter(P"loc", S"r", S"r".iter(P"a", S"map", P"loc" x P"a" x ((id_map \| head(S"map")) \/ S"map")))

    val superpose: Routine = R"superpose"(P"loc", S"res") := cells.map { b =>
      val os = others(b); val refs = tileRefs(os.size)
      val labeled = ((ss"$b._": Space) +: os.indices.map(i => (os(i): Path) x sP"${refs(i).s}").toVector).reduce(_ \/ _)
      (\/(sP"loc" /\ (ss"$b": Space)): Space) x iterN(S"res", refs, SpaceMention("_"), labeled)
    }.reduce(_ \/ _)
    val collapse: Routine = R"collapse"(P"loc", S"state") := cells.map { b =>
      (sP"loc" /\ (ss"$b": Space)) x others(b).map(o => S"state"(Path.Constant(Syntax.parse(o)))).reduce(_ x _)
    }.reduce(_ \/ _)

    private val exploreRefs = PathRef("q") +: tileRefs(n - 1)
    private val tupleP = tileRefs(n - 1).map(r => Path.Deref(r): Path).reduce(_ x _)
    /** one BFS expansion: the successor states of `frontier` (compact form). */
    def expandStep(frontier: Space): Space =
      iterN(frontier, exploreRefs, SpaceMention("_"),
        R"superpose"(P"q", Space.Singleton(tupleP)).iter(P"l", S"t",
          all_moves(P"q").iter(P"act", S"map", P"act" x S"map"(P"l") x S"t")
        ).iter(P"act", S"ass", all_moves(P"q" x P"act" x P"q").iterh(P"d", R"collapse"(P"d", S"ass"))))
    val explore: Routine = R"explore"(S"frontier", S"states") :=
      (S"states" \/ R"explore"((expandStep(S"frontier") \ S"states"): Space, (S"frontier" \/ S"states"): Space))
    def defs: PartialFunction[RoutinePtr, Routine] = Syntax.mod(superpose, collapse, explore)
    def initial: PathValue = Syntax.parse((cells.head +: (1 until n).map(_.toString)).mkString("."))
    def entry: Space = R"explore"(Space.Singleton(Path.Constant(initial)), Space.Empty)

  def puzzle(rows: Int, cols: Int): Puzzle = new Puzzle(rows, cols)

  /** Independent reference: count of states reachable within `maxDepth` BFS levels.  State =
   *  permutation vector (cell index -> tile, 0 = blank); moves swap blank with a grid neighbour. */
  def refReachable(rows: Int, cols: Int, maxDepth: Int = Int.MaxValue): Int =
    val n = rows * cols
    def nbrs(v: Vector[Int]): Set[Vector[Int]] =
      val b = v.indexOf(0); val r = b / cols; val c = b % cols
      Vector((r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1)).filter((rr, cc) => rr >= 0 && rr < rows && cc >= 0 && cc < cols)
        .map((rr, cc) => { val j = rr * cols + cc; v.updated(b, v(j)).updated(j, 0) }).toSet
    val start = (0 +: (1 until n)).toVector
    var visited = Set(start); var frontier = Set(start); var d = 0
    while frontier.nonEmpty && d < maxDepth do { val nf = frontier.flatMap(nbrs) -- visited; visited ++= nf; frontier = nf; d += 1 }
    visited.size

  /** bounded MORKL BFS using a given evaluator, for fast tests/benchmarks on big boards. */
  def boundedStates(p: Puzzle, ev: Space => SpaceValue, maxDepth: Int): Int =
    var visited = Set(p.initial); var frontier = Set(p.initial); var d = 0
    while frontier.nonEmpty && d < maxDepth do
      val succ = ev(p.expandStep(Space.Literal(SpaceValue(frontier)))).paths
      val nf = succ -- visited; visited ++= nf; frontier = nf; d += 1
    visited.size
end Sliding

class ExSlidingPuzzle extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  test("2x2 (pure): full reachable state space == 4!/2 = 12") {
    val p = Sliding.puzzle(2, 2)
    assertEquals(Sliding.refReachable(2, 2), 12)
    assertEquals(eval(p.entry)(using rc = p.defs).paths.size, 12)
    assertEquals(evalT(p.entry)(using rc = p.defs).size, 12)
  }

  test("3x3 (pure): bounded BFS matches reference (eval == evalT == ref)") {
    val p = Sliding.puzzle(3, 3); val depth = 6
    val ref = Sliding.refReachable(3, 3, depth)
    assertEquals(Sliding.boundedStates(p, s => eval(s)(using rc = p.defs), depth), ref)
    assertEquals(Sliding.boundedStates(p, s => evalT(s)(using rc = p.defs).toSpaceValue, depth), ref)
    Loaders.note(s"[puzzle/3x3] reachable within $depth moves = $ref")
  }

  test("3x3 (pure): FULL reachable state space == 9!/2 = 181440".tag(SlowTag.Slow)) {
    val p = Sliding.puzzle(3, 3)
    val t0 = System.nanoTime()
    assertEquals(evalT(p.entry)(using rc = p.defs).size, 181440)
    Loaders.note(s"[puzzle/3x3-full] 181440 states in ${(System.nanoTime - t0) / 1000000}ms")
  }

  test("4x4 / 5x5 (pure): bounded BFS matches reference".tag(SlowTag.Slow)) {
    for (r, c, depth) <- Seq((4, 4, 6), (5, 5, 5)) do
      val p = Sliding.puzzle(r, c)
      val got = Sliding.boundedStates(p, s => evalT(s)(using rc = p.defs).toSpaceValue, depth)
      assertEquals(got, Sliding.refReachable(r, c, depth))
      Loaders.note(s"[puzzle/${r}x$c] reachable within $depth = $got")
  }
end ExSlidingPuzzle

/** Guiding example 6: spatial temperature query over the NOAA gridded anomaly slice.
 *  Cells are indexed in a binary trie (lat,lon bits) with a temperature bucket; restriction
 *  by a trie-prefix interval is a spatial range query, restriction by a bucket is a
 *  temperature query (cf. ALGEBRA.md §10 fuzzy trie search). */
object NOAA:
  import Space.*
  // committed, reproducible fixture (extracted by scripts/extract_noaa_slice.py); repo-relative.
  val file: Option[java.io.File] = Loaders.resolve("src/test/resources/noaa_slice.txt")
  case class Cell(lat: Int, lon: Int, anom: Double)
  def load(p: String): Vector[Cell] = Loaders.fileOpt(p).getOrElse(Vector.empty).flatMap { l =>
    val t = l.trim
    if t.startsWith("#") || t.isEmpty then None
    else t.split("\\s+") match { case Array(a, b, c) => Some(Cell(a.toInt, b.toInt, c.toDouble)); case _ => None }
  }
  def bucket(a: Double): String = if a < -1 then "VC" else if a < -0.2 then "C" else if a < 0.2 then "N" else if a < 1 then "W" else "VW"
  def bits(v: Int, n: Int): List[PathItem] = (n - 1 to 0 by -1).map(i => ((v >> i) & 1).toString).toList
  // spatial-trie encoding: lat(6 bits).lon(7 bits).bucket  — prefix restriction = spatial range query
  def worldBin(cells: Vector[Cell]): SpaceValue =
    SpaceValue(cells.map(c => PathValue(bits(c.lat, 6) ++ bits(c.lon, 7) :+ (bucket(c.anom)))).toSet)
  // temperature-first encoding: bucket.lat.lon — prefix restriction by bucket = temperature query
  def worldTemp(cells: Vector[Cell]): SpaceValue =
    SpaceValue(cells.map(c => PathValue(List(bucket(c.anom), c.lat.toString, c.lon.toString))).toSet)
  /** Canonical covering of integer interval [lo,hi] by binary-trie prefixes of an `n`-bit trie. */
  def interval(lo: Int, hi: Int, n: Int): SpaceValue =
    val out = collection.mutable.Set.empty[PathValue]
    def rec(prefix: List[PathItem], level: Int, base: Int): Unit =
      val top = base + (1 << level) - 1
      if lo <= base && top <= hi then out += PathValue(prefix.reverse)
      else if level > 0 then
        rec("0" :: prefix, level - 1, base)
        rec("1" :: prefix, level - 1, base + (1 << (level - 1)))
    rec(Nil, n, 0)
    SpaceValue(out.toSet)
end NOAA

class ExNOAATemperature extends FunSuite:
  import Space.*

  val cells = NOAA.file.map(f => NOAA.load(f.getPath)).getOrElse(Vector.empty)

  test("NOAA slice loaded (2592 grid cells)") {
    assertEquals(cells.size, 2592)
    val mean = cells.map(_.anom).sum / cells.size
    Loaders.note(f"[temp/load] ${cells.size} cells; global mean anomaly = $mean%.3f C (May 2026)")
  }

  test("NOAA fixture provenance: checksum detects accidental edits") {
    // reproducible via scripts/extract_noaa_slice.py; pin the sha256 of the committed slice
    val f = NOAA.file
    assume(f.isDefined, "noaa_slice.txt fixture missing")
    val bytes = java.nio.file.Files.readAllBytes(f.get.toPath)
    val sha = java.security.MessageDigest.getInstance("SHA-256").digest(bytes)
      .map(b => f"$b%02x").mkString
    assertEquals(sha, "e985eb81df7a19a6e7cecb121f7d0f436f2c732f2b3f6498105045197b285856")
  }

  test("temperature query: 'where is it very warm' (bucket restriction) == reference") {
    val world = Space.Literal(NOAA.worldTemp(cells))
    // very-warm cells: restrict by the VW prefix, then drop the bucket tag -> spatial coords
    val q = Space.Unwrap(Space.Restriction(world, ss"VW"), Path.Constant("VW"))
    val got = eval(q)
    val reference = cells.filter(_.anom >= 1.0).map(c => s"${c.lat}.${c.lon}").toSet
    assertEquals(got.paths.map(_.show).toSet, reference)
    Loaders.note(s"[temp/query] very-warm cells (anom>=1C) = ${got.paths.size} of ${cells.size}")
  }

  test("spatial trie range query: Arctic band (lat idx 30..35) == reference") {
    val world = Space.Literal(NOAA.worldBin(cells))
    // restrict to the lat-prefix interval covering indices 30..35 (binary trie over 6 lat bits)
    val arctic = Space.Restriction(world, Space.Literal(NOAA.interval(30, 35, 6)))
    val got = eval(arctic)
    val reference = cells.count(c => c.lat >= 30 && c.lat <= 35)
    assertEquals(got.paths.size, reference)
    Loaders.note(s"[temp/spatial] cells with lat idx in [30,35] = ${got.paths.size} (trie interval = ${NOAA.interval(30,35,6).paths.size} prefixes)")
  }

  test("SC specializes the temperature query to the static grid (band dynamic)") {
    val world = Space.Literal(NOAA.worldTemp(cells))
    // query parameterized by a dynamic temperature band S"band"
    val routine = R"tempq"(S"world", S"band") := Space.Restriction(S"world", S"band")
    val call = Space.Call(RoutinePtr("tempq"), Vector(), Vector(world, Space.Mention(SpaceMention("band"))))
    val res = SC.supercompile(call, Syntax.mod(routine))
    val sc = SpaceContextMap(Map(SpaceMention("band") -> SpaceValue("VW")))
    val got = eval(res.top)(using PathContextMap(Map.empty), sc, res.env)
    val orig = eval(call)(using PathContextMap(Map.empty), sc, Syntax.mod(routine))
    assertEquals(got, orig)
    val entryRoutine = res.routines(res.top.asInstanceOf[Space.Call].r)
    assert(!entryRoutine.mentions.exists(_.s == "world"), s"world should be specialized away; ${entryRoutine.mentions}")
    Loaders.note(s"[temp/SC] residual specialized to the grid; params=${entryRoutine.mentions.map(_.s)}")
  }
end ExNOAATemperature
