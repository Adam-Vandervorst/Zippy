package morkl

import munit.FunSuite
import scala.collection.mutable

/** Structural census of the space fuzzer: generate N programs at the demo size (depth 6, >=12 nodes)
 *  and tally the full "a term of type X occurs at position p inside a term of type Y" matrix — i.e.
 *  parent-constructor + child-slot (rows) against child-constructor (columns).  Writes a TSV for plotting.
 *  Structure only (no eval): the dependent argument still shapes each program's literals/prefixes. */
class ProgramStats extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  def tS(s: Space): String = s match
    case Space.Empty => "Empty"; case _: Space.Mention => "Mention"; case _: Space.Singleton => "Singleton"
    case _: Space.Literal => "Literal"; case _: Space.Union => "Union"; case _: Space.Intersection => "Intersection"
    case _: Space.Subtraction => "Subtraction"; case _: Space.Restriction => "Restriction"; case _: Space.Raffination => "Raffination"
    case _: Space.Composition => "Composition"; case _: Space.Wrap => "Wrap"; case _: Space.Unwrap => "Unwrap"
    case _: Space.TailsUnion => "TailsUnion"; case _: Space.TailsIntersection => "TailsIntersection"
    case _: Space.Iteration => "Iteration"; case _: Space.Fixpoint => "Fixpoint"; case _: Space.Fold => "Fold"
    case _: Space.Range => "Range"
    case _: Space.GroundedPS => "GroundedPS"; case _: Space.GroundedSS => "GroundedSS"; case _: Space.Call => "Call"
  def tP(p: Path): String = p match
    case _: Path.Constant => "Constant"; case _: Path.Deref => "Deref"; case _: Path.Concat => "Concat"
    case _: Path.GroundedPP => "GroundedPP"; case _: Path.GroundedSP => "GroundedSP"

  // ONE OWNER (SpatialPipeline.nodeCount, over the total SizeZ3.children).  The hand-written copy this
  // replaces had no arm for Raffination / TailsIntersection / Fixpoint / Fold, so their whole subtrees
  // counted as leaves and the `nodes >= 12` accept filter silently admitted smaller programs.
  def nodes(s: Space): Int = SpatialPipeline.nodeCount(s)

  type Counts = mutable.HashMap[(String, String), mutable.HashMap[String, Long]]
  def add(c: Counts, y: String, pos: String, x: String): Unit =
    val row = c.getOrElseUpdate((y, pos), mutable.HashMap.empty); row.update(x, row.getOrElse(x, 0L) + 1L)

  def walkP(p: Path, c: Counts): Unit = p match
    case Path.Concat(l, r) => add(c, "Concat", "l", tP(l)); add(c, "Concat", "r", tP(r)); walkP(l, c); walkP(r, c)
    case _ => ()
  def walk(s: Space, c: Counts): Unit =
    val y = tS(s)
    def S(pos: String, ch: Space): Unit = { add(c, y, pos, tS(ch)); walk(ch, c) }
    def P(pos: String, ch: Path): Unit = { add(c, y, pos, tP(ch)); walkP(ch, c) }
    s match
      case Space.Union(a, b) => S("l", a); S("r", b)
      case Space.Intersection(a, b) => S("l", a); S("r", b)
      case Space.Subtraction(a, b) => S("l", a); S("r", b)
      case Space.Composition(a, b) => S("l", a); S("r", b)
      case Space.Restriction(a, b) => S("src", a); S("by", b)
      case Space.Wrap(a, p) => S("src", a); P("pre", p)
      case Space.Unwrap(a, p) => S("src", a); P("pre", p)
      case Space.Raffination(a, b) => S("l", a); S("r", b)
      case Space.TailsUnion(a) => S("src", a)
      case Space.TailsIntersection(a) => S("src", a)
      case Space.Range(a, _, _) => S("src", a)
      case Space.Iteration(a, _, _, b) => S("src", a); S("body", b)
      case Space.Fixpoint(a, _, b) => S("init", a); S("body", b)
      case Space.Fold(a, _, _, _, _, b, _) => S("src", a); S("body", b)
      case Space.Singleton(p) => P("path", p)
      case _ => ()   // leaves: Empty / Mention / Literal

  // a stable display order
  val typeOrder = Vector("Mention", "Literal", "Singleton", "Union", "Intersection", "Subtraction", "Restriction",
    "Raffination", "Composition", "Wrap", "Unwrap", "TailsUnion", "TailsIntersection", "Range",
    "Iteration", "Fold", "Fixpoint", "Constant", "Deref", "Concat")
  val posOrder = Vector("l", "r", "src", "by", "body", "init", "pre", "pat", "tmpl", "path")
  def tIdx(t: String) = { val i = typeOrder.indexOf(t); if i < 0 then 999 else i }
  def pIdx(p: String) = { val i = posOrder.indexOf(p); if i < 0 then 999 else i }

  test("structural matrix over N random programs".tag(SlowTag.Slow)) {
    val N = sys.props.get("prog.n").map(_.toInt).getOrElse(1000000)
    val depth = sys.props.get("prog.depth").map(_.toInt).getOrElse(6)
    val minNodes = sys.props.get("prog.minNodes").map(_.toInt).getOrElse(12)
    val rng = new java.util.Random(2026L)
    val c: Counts = mutable.HashMap.empty
    val t0 = System.nanoTime()
    var got = 0L; var draws = 0L; var totalNodes = 0L
    while got < N do
      draws += 1
      val arg = SpaceFuzzer.argDist.sample(using rng)
      val p = SpaceFuzzer.genProg(arg, depth).sample(using rng)
      if nodes(p) >= minNodes then { walk(p, c); got += 1; totalNodes += nodes(p) }
    val secs = (System.nanoTime() - t0) / 1e9
    // assemble matrix
    val rows = c.keys.toVector.sortBy((y, p) => (tIdx(y), pIdx(p), y, p))
    val cols = c.values.flatMap(_.keys).toSet.toVector.sortBy(x => (tIdx(x), x))
    val sb = new StringBuilder
    sb.append(s"# prog_matrix.tsv — ${RunEnvironment.oneLine(Seq("programs" -> got.toString, "min-nodes" -> minNodes.toString,
                                                 "seed" -> "2026"))}\n")
    sb.append("row\t").append(cols.mkString("\t")).append('\n')
    for (y, p) <- rows do
      val row = c((y, p))
      sb.append(s"$y.$p").append('\t').append(cols.map(x => row.getOrElse(x, 0L)).mkString("\t")).append('\n')
    // THE REPO ROOT, not /tmp: this artifact is committed, and writing it to /tmp meant every
    // regeneration had to be copied over by hand — which is how the committed copy came to carry a
    // `Transformation` column for a constructor the `Space` enum no longer has.
    // as CorpusRuntimes: measured always, published only under a manifest
    if BenchmarkArtifact.publishing then BenchmarkArtifact.write("prog_matrix.tsv", sb.toString)
    else println(BenchmarkArtifact.skipNote("prog_matrix.tsv"))
    System.out.println(s"PROGSTATS: N=$got accepted of $draws draws (${(100.0*got/draws).round}% >= $minNodes nodes), " +
      f"avg ${totalNodes.toDouble/got}%.1f nodes/program, ${secs}%.1fs; matrix ${rows.size}x${cols.size} -> prog_matrix.tsv")
    System.out.println(sb.toString)
    assertEquals(got, N.toLong)
  }
end ProgramStats
