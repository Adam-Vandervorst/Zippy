package morkl

import munit.FunSuite
import scala.util.Random

/** Correctness of the SpaceZipper paradigm: every virtual zipper op must match the reference `eval` of the
 *  corresponding Space op (lift via `traversal`, drop via `materialize`), the algebraic laws must hold
 *  over zippers, and `execZ` must agree with the other evaluators on whole programs. */
class ZipperTest extends FunSuite:
  import Space.*
  private val A = SpaceFuzzer.alphabet

  private def randPath(r: Random): PathValue = PathValue(List.fill(1 + r.nextInt(3))(A(r.nextInt(A.length))))
  private def randSV(r: Random): SpaceValue = SpaceValue((0 to r.nextInt(6)).map(_ => randPath(r)).toSet)
  private def ip(p: PathValue): List[Int] = Interner.internPath(p.items)

  test("zipper local ops match reference eval over random tries (lift→op→materialize)") {
    var n = 0
    for seed <- 0 until 500 do
      val r = new Random(seed.toLong * 0x9E3779B1L + 1)
      val x = randSV(r); val y = randSV(r)
      val zx = SpaceZipper.traversal(ITrie.fromSpaceValue(x)); val zy = SpaceZipper.traversal(ITrie.fromSpaceValue(y))
      def chk(name: String, sp: Space, z: SpaceZipper): Unit =
        assertEquals(SpaceZipper.materialize(z).toSpaceValue, eval(sp), s"$name seed=$seed\n x=$x\n y=$y"); n += 1
      chk("union", Union(Literal(x), Literal(y)), SpaceZipper.Union(zx, zy))
      chk("intersection", Intersection(Literal(x), Literal(y)), SpaceZipper.Intersection(zx, zy))
      chk("subtraction", Subtraction(Literal(x), Literal(y)), SpaceZipper.Subtraction(zx, zy))
      chk("restriction", Restriction(Literal(x), Literal(y)), SpaceZipper.restriction(zx, zy))
      chk("raffination", Raffination(Literal(x), Literal(y)), SpaceZipper.raffination(zx, zy))
      chk("composition", Composition(Literal(x), Literal(y)), SpaceZipper.Composition(zx, zy))
      chk("tailsUnion", TailsUnion(Literal(x)), SpaceZipper.TailsUnion(zx))
      chk("tailsIntersection", TailsIntersection(Literal(x)), SpaceZipper.TailsIntersection(zx))
      val p = randPath(r)
      chk("wrap", Wrap(Literal(x), Path.Constant(p)), SpaceZipper.Prefix(ip(p), zx))
      chk("unwrap", Unwrap(Literal(x), Path.Constant(p)), SpaceZipper.unwrap(zx, ip(p)))
    System.out.println(s"ZIPPER OPS: $n op-vs-eval checks over 500 seeds")
    assert(n > 0)
  }

  test("zipper algebraic laws: union/intersection commutative + associative, materialized") {
    for seed <- 0 until 300 do
      val r = new Random(seed.toLong * 0x85EBCA77L + 3)
      val zx = SpaceZipper.traversal(ITrie.fromSpaceValue(randSV(r)))
      val zy = SpaceZipper.traversal(ITrie.fromSpaceValue(randSV(r)))
      val zz = SpaceZipper.traversal(ITrie.fromSpaceValue(randSV(r)))
      def mat(z: SpaceZipper) = SpaceZipper.materialize(z).toSpaceValue
      assertEquals(mat(SpaceZipper.Union(zx, zy)), mat(SpaceZipper.Union(zy, zx)), s"union comm seed=$seed")
      assertEquals(mat(SpaceZipper.Union(zx, SpaceZipper.Union(zy, zz))), mat(SpaceZipper.Union(SpaceZipper.Union(zx, zy), zz)), s"union assoc seed=$seed")
      assertEquals(mat(SpaceZipper.Intersection(zx, zy)), mat(SpaceZipper.Intersection(zy, zx)), s"inter comm seed=$seed")
      assertEquals(mat(SpaceZipper.Intersection(zx, SpaceZipper.Intersection(zy, zz))), mat(SpaceZipper.Intersection(SpaceZipper.Intersection(zx, zy), zz)), s"inter assoc seed=$seed")
  }

  // --- a random non-recursive, non-grounded program generator (eval is total on it) ---
  private def randSpace(depth: Int, vars: Vector[String], pvars: Vector[String], r: Random): Space =
    def leaf(): Space = r.nextInt(5) match
      case 0 => Empty
      case 1 => Literal(randSV(r))
      case 2 if vars.nonEmpty => Mention(SpaceMention(vars(r.nextInt(vars.length))))
      case 3 if pvars.nonEmpty => Singleton(Path.Deref(PathRef(pvars(r.nextInt(pvars.length))).known(1)))
      case _ => Singleton(Path.Constant(randPath(r)))
    if depth <= 0 then leaf()
    else
      def sub() = randSpace(depth - 1, vars, pvars, r)
      r.nextInt(13) match
        case 0 => Union(sub(), sub());        case 1 => Intersection(sub(), sub())
        case 2 => Subtraction(sub(), sub());  case 3 => Restriction(sub(), sub())
        case 4 => Raffination(sub(), sub());  case 5 => Composition(sub(), sub())
        case 6 => Wrap(sub(), Path.Constant(randPath(r))); case 7 => Unwrap(sub(), Path.Constant(randPath(r)))
        case 8 => TailsUnion(sub());          case 9 => TailsIntersection(sub())
        case 10 => { val lo = r.nextInt(3); Range(sub(), lo, lo + 1 + r.nextInt(3)) }
        case 11 => Range(sub(), 0, 1 + r.nextInt(3))
        case _ => val h = s"h${r.nextInt(999)}"; val t = s"t${r.nextInt(999)}"
                  Iteration(sub(), PathRef(h).known(1), SpaceMention(t), randSpace(depth - 1, vars :+ t, pvars :+ h, r))

  test("execZ agrees with eval and evalI over 500 random programs") {
    val mentions = Vector("a", "b", "c")
    var n = 0
    for seed <- 0 until 500 do
      val r = new Random(seed.toLong * 0x27D4EB2FL + 5)
      val prog = randSpace(3, mentions, Vector.empty, r)
      val binds = mentions.map(m => SpaceMention(m) -> randSV(r)).toMap
      val ref = eval(prog)(using sc = SpaceContextMap(binds))
      val ic = binds.map((m, v) => m -> ITrie.fromSpaceValue(v))
      assertEquals(execZ(prog)(using ic = ic).toSpaceValue, ref, s"execZ seed=$seed: ${prog.show}")
      assertEquals(evalI(prog)(using ic = ic).toSpaceValue, ref, s"evalI seed=$seed")  // sanity
      n += 1
    System.out.println(s"ZIPPER PROGRAMS: $n execZ==eval checks")
    assertEquals(n, 500)
  }
end ZipperTest
