import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** Three datalog examples from ~/carac — transitive closure (`tc`), reverse same-generation (`rsg`),
 *  and Andersen points-to (`andersen`, copy-propagation core) — each written as BOTH a naive and a
 *  semi-naive MORKL routine.  Every one is EXECUTED (naive == semi-naive == an independent Scala
 *  reference) and then printed with the Scala `Space.*` constructors fully expanded. */
class DatalogShowTest extends FunSuite:
  import Space.*

  // ============================================================================================
  // datalog join idiom in MORKL trie algebra
  //   join(r,s) = { x.z : r(x,y), s(y,z) }   — compose r with s on the middle item
  //   invert(r) = { a.b : r(b,a) }           — swap the two items of a binary relation
  // ============================================================================================
  def join(r: Space, s: Space): Space = r.iter(P"n", S"nbs", P"n" x \/(s <| S"nbs"))
  def invert(r: Space): Space = r.iter(P"b", S"as", S"as".iter(P"a", S"_", Singleton(P"a" x P"b")))

  // ---- the six datalog functions ----
  // tc : tc(X,Y):-e(X,Y). tc(X,Y):-tc(X,Z),e(Z,Y).            (linear transitive closure)
  val tcNaive = R"tc"(S"e", S"acc") :=
    S"acc" \/ R"tc"(S"e", S"e" \/ join(S"acc", S"e"))
  val tcSemi = R"tc_sn"(S"e", S"all", S"delta") :=
    S"all" \/ R"tc_sn"(S"e", S"all" \/ (join(S"delta", S"e") \ S"all"), join(S"delta", S"e") \ S"all")

  // routines with >3 space parameters are built with the constructors (the DSL head/Call caps at 3)
  def routineN(name: String, ms: String*)(body: Space): Routine =
    Routine(RoutinePtr(name), Vector.empty, ms.map(SpaceMention(_)).toVector, body)
  def callN(name: String, ms: Space*): Space = Space.Call(RoutinePtr(name), Vector.empty, ms.toVector)

  // rsg : rsg(X,Y):-flat(X,Y). rsg(X,Y):-up(X,A),rsg(B,A),down(B,Y).   (reverse same-generation)
  //   rsg_step(r) = join(join(up, invert(r)), down)
  def rsgStep(r: Space): Space = join(join(S"up", invert(r)), S"down")
  val rsgNaive = routineN("rsg", "up", "flat", "down", "rsg") {
    S"rsg" \/ callN("rsg", S"up", S"flat", S"down", S"flat" \/ rsgStep(S"rsg")) }
  val rsgSemi = routineN("rsg_sn", "up", "flat", "down", "all", "delta") {
    S"all" \/ callN("rsg_sn", S"up", S"flat", S"down", S"all" \/ (rsgStep(S"delta") \ S"all"), rsgStep(S"delta") \ S"all") }

  // andersen : pointsTo(Y,X):-addressOf(Y,X). pointsTo(Y,X):-assign(Y,Z),pointsTo(Z,X).  (copy core)
  val andNaive = R"pt"(S"addressOf", S"assign", S"pt") :=
    S"pt" \/ R"pt"(S"addressOf", S"assign", S"addressOf" \/ join(S"assign", S"pt"))
  val andSemi = routineN("pt_sn", "addressOf", "assign", "all", "delta") {
    S"all" \/ callN("pt_sn", S"addressOf", S"assign", S"all" \/ (join(S"assign", S"delta") \ S"all"), join(S"assign", S"delta") \ S"all") }

  // ---- fact sets (carac fixtures for tc/rsg; a small sensible instance for andersen) ----
  def pair(a: String, b: String): PathValue = PathValue(List(PathItem.Symbol(a), PathItem.Symbol(b)))
  def rel(ps: (String, String)*): SpaceValue = SpaceValue(ps.map(pair.tupled).toSet)
  val edges = rel("a" -> "b", "b" -> "c", "c" -> "d", "z" -> "z")                    // carac tc/base
  val up    = rel("a"->"e","a"->"f","f"->"m","g"->"n","h"->"n","i"->"o","j"->"o")     // carac rsg
  val flat  = rel("g"->"f","m"->"n","m"->"o","p"->"m")
  val down  = rel("l"->"f","m"->"f","g"->"b","h"->"c","i"->"d","p"->"k")
  val addressOf = rel("p" -> "h1", "q" -> "h2")                                       // andersen instance
  val assign    = rel("r" -> "p", "s" -> "r", "p" -> "q")

  // ---- independent Scala references ----
  def closure(step: Set[(String, String)] => Set[(String, String)], seed: Set[(String, String)]): Set[(String, String)] =
    var s = seed; var g = true
    while g do { val ns = s ++ step(s); g = ns != s; s = ns }; s
  def tuples(es: SpaceValue): Set[(String, String)] = es.paths.map { case PathValue(List(PathItem.Symbol(a), PathItem.Symbol(b))) => (a, b) }
  val refTC  = closure(s => for ((a, b) <- s; (c, d) <- s if b == c) yield (a, d), tuples(edges))
  val refRSG = closure(r => tuples(flat) ++ (for ((x, a) <- tuples(up); (b, a2) <- r if a2 == a; (b2, y) <- tuples(down) if b2 == b) yield (x, y)), tuples(flat))
  val refPT  = closure(pt => tuples(addressOf) ++ (for ((y, z) <- tuples(assign); (z2, x) <- pt if z2 == z) yield (y, x)), tuples(addressOf))

  def run(defs: Routine, entry: Space): Set[(String, String)] =
    tuples(eval(entry)(using rc = Syntax.mod(defs)))

  test("three carac datalog examples: naive == semi-naive == reference, then print expanded MORKL") {
    // tc
    val tcEntry  = Space.Call(RoutinePtr("tc"),    Vector(), Vector(Literal(edges), Literal(edges)))
    val tcEntryS = Space.Call(RoutinePtr("tc_sn"), Vector(), Vector(Literal(edges), Literal(edges), Literal(edges)))
    assertEquals(run(tcNaive, tcEntry), refTC, "tc naive")
    assertEquals(run(tcSemi, tcEntryS), refTC, "tc semi-naive")
    // rsg
    val rsgEntry  = Space.Call(RoutinePtr("rsg"),    Vector(), Vector(Literal(up), Literal(flat), Literal(down), Literal(flat)))
    val rsgEntryS = Space.Call(RoutinePtr("rsg_sn"), Vector(), Vector(Literal(up), Literal(flat), Literal(down), Literal(flat), Literal(flat)))
    assertEquals(run(rsgNaive, rsgEntry), refRSG, "rsg naive")
    assertEquals(run(rsgSemi, rsgEntryS), refRSG, "rsg semi-naive")
    // andersen
    val ptEntry  = Space.Call(RoutinePtr("pt"),    Vector(), Vector(Literal(addressOf), Literal(assign), Literal(addressOf)))
    val ptEntryS = Space.Call(RoutinePtr("pt_sn"), Vector(), Vector(Literal(addressOf), Literal(assign), Literal(addressOf), Literal(addressOf)))
    assertEquals(run(andNaive, ptEntry), refPT, "andersen naive")
    assertEquals(run(andSemi, ptEntryS), refPT, "andersen semi-naive")

    val sb = new StringBuilder
    def show(title: String, defs: Routine, entry: Space): Unit =
      sb.append(s"\n// ==================== $title ====================\n")
      sb.append(Expand.routine(defs)).append("\n")
      sb.append(s"// invoke:\n${Expand.space(entry, 0)}\n")
    show("TRANSITIVE CLOSURE — NAIVE", tcNaive, tcEntry)
    show("TRANSITIVE CLOSURE — SEMI-NAIVE", tcSemi, tcEntryS)
    show("REVERSE SAME-GENERATION — NAIVE", rsgNaive, rsgEntry)
    show("REVERSE SAME-GENERATION — SEMI-NAIVE", rsgSemi, rsgEntryS)
    show("ANDERSEN POINTS-TO — NAIVE", andNaive, ptEntry)
    show("ANDERSEN POINTS-TO — SEMI-NAIVE", andSemi, ptEntryS)
    val out = new java.io.File(Loaders.repoRoot, "datalog-morkl.txt")
    val w = new java.io.FileWriter(out); try w.write(sb.toString) finally w.close()
    System.out.println(sb.toString)
  }
end DatalogShowTest

/** Render a [[Space]] / [[Routine]] as explicit, runnable Scala `Space.*` / `Path.*` constructor source. */
object Expand:
  import Space.*
  def item(pi: PathItem): String = pi match
    case PathItem.Symbol(n)   => s"""PathItem.Symbol("$n")"""
    case PathItem.Variable(n) => s"""PathItem.Variable("$n")"""
    case PathItem.Arity(k)    => s"PathItem.Arity($k)"
  def pv(p: PathValue): String = s"PathValue(List(${p.items.map(item).mkString(", ")}))"
  def ref(pr: PathRef): String = if pr.lengthHint < 0 then s"""PathRef("${pr.s}")""" else s"""PathRef("${pr.s}").known(${pr.lengthHint})"""
  def path(p: Path): String = p match
    case Path.Deref(pr)    => s"Path.Deref(${ref(pr)})"
    case Path.Constant(x)  => s"Path.Constant(${pv(x)})"
    case Path.Concat(l, r) => s"Path.Concat(${path(l)}, ${path(r)})"
    case other             => other.toString
  def sv(s: SpaceValue): String =
    s"SpaceValue(Set(${s.paths.toList.sortBy(_.items.map(_.show).mkString(".")).map(pv).mkString(", ")}))"
  def space(s: Space, ind: Int): String =
    val p = "  " * ind; val q = "  " * (ind + 1)
    def bin(name: String, x: Space, y: Space) = s"Space.$name(\n$q${space(x, ind + 1)},\n$q${space(y, ind + 1)})"
    s match
      case Empty            => "Space.Empty"
      case Mention(m)       => s"""Space.Mention(SpaceMention("${m.s}"))"""
      case Singleton(pt)    => s"Space.Singleton(${path(pt)})"
      case Literal(v)       => s"Space.Literal(${sv(v)})"
      case Union(x, y)         => bin("Union", x, y)
      case Intersection(x, y)  => bin("Intersection", x, y)
      case Subtraction(x, y)   => bin("Subtraction", x, y)
      case Restriction(x, y)   => bin("Restriction", x, y)
      case Composition(x, y)   => bin("Composition", x, y)
      case Wrap(src, pt)    => s"Space.Wrap(\n$q${space(src, ind + 1)},\n$q${path(pt)})"
      case Unwrap(src, pt)  => s"Space.Unwrap(\n$q${space(src, ind + 1)},\n$q${path(pt)})"
      case TailsUnion(src)  => s"Space.TailsUnion(\n$q${space(src, ind + 1)})"
      case TailsIntersection(src) => s"Space.TailsIntersection(\n$q${space(src, ind + 1)})"
      case Iteration(src, sym, rest, tmpl) =>
        s"""Space.Iteration(\n$q${space(src, ind + 1)},\n$q${ref(sym)}, SpaceMention("${rest.s}"),\n$q${space(tmpl, ind + 1)})"""
      case Call(rp, refs, ms) =>
        val r = if refs.isEmpty then "Vector()" else s"Vector(${refs.map(path).mkString(", ")})"
        val m = if ms.isEmpty then "Vector()" else s"Vector(\n$q${ms.map(space(_, ind + 1)).mkString(s",\n$q")})"
        s"""Space.Call(RoutinePtr("${rp.s}"), $r, $m)"""
      case other            => other.toString
  def routine(r: Routine): String =
    val refs = r.refs.map(pr => s"""PathRef("${pr.s}")""").mkString(", ")
    val ms   = r.mentions.map(m => s"""SpaceMention("${m.s}")""").mkString(", ")
    s"""Routine(RoutinePtr("${r.name.s}"), Vector($refs), Vector($ms),\n  ${space(r.body, 1)})"""
