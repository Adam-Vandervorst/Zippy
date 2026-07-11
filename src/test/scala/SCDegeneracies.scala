import munit.FunSuite
import scala.collection.mutable

/** Diagnose what stops the supercompiler reducing the corpus further: supercompile all 1000 programs
 *  and scan the RESIDUALS for sub-patterns that are provably reducible but survive.  Each surviving
 *  pattern names a missing algebraic law or driving move; we rank them by how often they occur. */
class SCDegeneracies extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(60, "min")

  def sub(s: Space): List[Space] = s :: (s match
    case Space.Union(a, b) => sub(a) ::: sub(b); case Space.Intersection(a, b) => sub(a) ::: sub(b)
    case Space.Subtraction(a, b) => sub(a) ::: sub(b); case Space.Restriction(a, b) => sub(a) ::: sub(b)
    case Space.Raffination(a, b) => sub(a) ::: sub(b); case Space.Composition(a, b) => sub(a) ::: sub(b)
    case Space.Wrap(a, _) => sub(a); case Space.Unwrap(a, _) => sub(a); case Space.TailsUnion(a) => sub(a)
    case Space.TailsIntersection(a) => sub(a); case Space.Range(a, _, _) => sub(a)
    case Space.Iteration(a, _, _, b) => sub(a) ::: sub(b); case Space.Fixpoint(a, _, b) => sub(a) ::: sub(b)
    case Space.Call(_, _, ms) => ms.flatMap(sub).toList; case _ => Nil)
  def nodes(s: Space): Int = sub(s).size
  def cst(p: Path): Option[PathValue] = p match { case Path.Constant(pv) => Some(pv); case _ => None }
  val maxS = 3; val maxP = 2; val A = SpaceFuzzer.alphabet
  val sNames = (0 until maxS).map(i => SpaceMention("s" + i)).toVector
  val pNames = (0 until maxP).map(j => PathRef("p" + j)).toVector
  def rpath(r: java.util.Random) = PathValue(List.fill(1 + r.nextInt(2))(A(r.nextInt(A.length))))
  def strie(r: java.util.Random) = SpaceValue((0 until (1 + r.nextInt(6))).map(_ => rpath(r)).toSet)
  def icOf(ns: Int, sv: Array[SpaceValue]) = (0 until ns).map(i => sNames(i) -> ITrie.fromSpaceValue(sv(i))).toMap
  def pcOf(np: Int, pv: Array[PathValue]): PathContext = PathContextMap((0 until np).map(j => pNames(j) -> pv(j)).toMap)

  // each detector returns how many reducible-but-unreduced occurrences a residual contains
  val detectors: Vector[(String, Space => Int)] = Vector(
    "Intersection(x,x) -> x"        -> (t => sub(t).count { case Space.Intersection(a, b) => a == b; case _ => false }),
    "Union(x,x) -> x"               -> (t => sub(t).count { case Space.Union(a, b) => a == b; case _ => false }),
    "Subtraction(x,x) -> Empty"     -> (t => sub(t).count { case Space.Subtraction(a, b) => a == b; case _ => false }),
    "Empty subterm (absorption)"    -> (t => if t == Space.Empty then 0 else sub(t).count(_ == Space.Empty)),
    "Literal(emptyset) (=Empty)"    -> (t => sub(t).count { case Space.Literal(sv) => sv.paths.isEmpty; case _ => false }),
    "Unwrap(Wrap(s,p),q) const"     -> (t => sub(t).count { case Space.Unwrap(Space.Wrap(_, p), q) => cst(p).isDefined && cst(q).isDefined; case _ => false }),
    "Range(Singleton(_))"           -> (t => sub(t).count { case Space.Range(Space.Singleton(_), _, _) => true; case _ => false }),
    "Range(Literal(_))"             -> (t => sub(t).count { case Space.Range(Space.Literal(_), _, _) => true; case _ => false }),
    "iter(s,h,t, Mention t)=Tails"  -> (t => sub(t).count { case Space.Iteration(_, _, rest, Space.Mention(m)) => m == rest; case _ => false }),
    "TailsUnion(Singleton(_))"      -> (t => sub(t).count { case Space.TailsUnion(Space.Singleton(_)) => true; case _ => false }),
    "Unwrap(Unwrap(s,c1),c2) merge" -> (t => sub(t).count { case Space.Unwrap(Space.Unwrap(_, c1), c2) => cst(c1).isDefined && cst(c2).isDefined; case _ => false }),
    "Singleton(Const) (no fold)"    -> (t => sub(t).count { case Space.Singleton(Path.Constant(_)) => true; case _ => false }),
    "Restriction/Raffination(x,x)"  -> (t => sub(t).count { case Space.Restriction(a, b) => a == b; case Space.Raffination(a, b) => a == b; case _ => false }),
  )

  test("SC degeneracies: reducible patterns surviving in residuals".tag(SlowTag.Slow)) {
    val recs = locally {
      val f = new java.io.File(Loaders.repoRoot, "corpus_1000.ser"); assert(f.exists)
      val ois = new java.io.ObjectInputStream(new java.io.FileInputStream(f))
      try ois.readObject().asInstanceOf[Vector[FuzzRec]]
      catch case e: java.io.InvalidClassException =>
        throw new AssertionError("corpus_1000.ser is STALE (serialized classes changed) — rerun morkl.ProgramExpressivity to regenerate it", e)
      finally ois.close()
    }
    val noRc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
    val totals = mutable.LinkedHashMap.from(detectors.map(_._1 -> 0L))
    val progsWith = mutable.LinkedHashMap.from(detectors.map(_._1 -> 0L))
    var origN = 0L; var scN = 0L; var failed = 0
    val scTops = Array.ofDim[Space](recs.size)
    val erng = new java.util.Random(77)                                   // SC-soundness guard: 8 inputs/program
    val envs = Array.fill(8) { (Array.fill(maxS)(strie(erng)), Array.fill(maxP)(rpath(erng))) }
    for (r, i) <- recs.zipWithIndex do
      scala.util.Try(SC.supercompile(r.prog, noRc)) match
        case scala.util.Success(res) =>
          scTops(i) = res.top; origN += nodes(r.prog); scN += nodes(res.top)
          for (sv, pv) <- envs do
            assertEquals(evalI(res.top)(using pcOf(r.nPath, pv), icOf(r.nSpace, sv), noRc).toSpaceValue,
              evalI(r.prog)(using pcOf(r.nPath, pv), icOf(r.nSpace, sv), noRc).toSpaceValue, s"SC changed semantics for idx=$i")
          for (name, d) <- detectors do
            val c = d(res.top); if c > 0 then { totals(name) += c; progsWith(name) += 1 }
        case scala.util.Failure(ex) => failed += 1; if failed <= 3 then System.out.println(s"  SC FAIL idx=$i: ${ex.getClass.getSimpleName}: ${Option(ex.getMessage).getOrElse("").take(160)}")
    System.out.println(f"SCDEGEN: ${recs.size} programs; SC nodes $origN -> $scN (${100.0 * (origN - scN) / origN}%.1f%% smaller); $failed SC failures")
    System.out.println(f"  ${"reducible pattern surviving in residual"}%-34s | ${"total"}%8s | ${"%% of programs"}%13s")
    for (name, _) <- detectors.sortBy(d => -totals(d._1)) do
      System.out.println(f"  $name%-34s | ${totals(name)}%8d | ${100.0 * progsWith(name) / recs.size}%11.1f%%")

    // show the slowest-program residuals annotated with surviving patterns
    System.out.println("\nResiduals of a few programs (look for the patterns above):")
    for i <- Vector(336, 935, 264, 635, 271) do
      val t = scTops(i)
      if t != null then System.out.println(s"\n  idx=$i  SC-nodes=${nodes(t)}\n   " + t.show.replaceAll("\\s+", " ").trim)
  }
end SCDegeneracies
