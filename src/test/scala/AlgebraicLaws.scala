package morkl

import munit.FunSuite

/** Metamorphic algebraic-law properties (design_plan §6.6).  Unlike the differential tests (which
 *  cross-check the *backends* against each other) and the SC-soundness gate (which checks the
 *  supercompiler preserves meaning), these assert that the SET-ALGEBRA LAWS THEMSELVES hold under
 *  the trusted reference `eval`, over randomly generated programs and inputs.  A failure here means
 *  either a bug in the reference interpreter or a mistaken law — exactly the class of error a
 *  backend-vs-backend differential cannot catch (a shared misconception agrees with itself).
 *
 *  Every assertion is a universally-valid identity of the path-set algebra, so the suite must stay
 *  green; a counterexample (printed with its seed and the offending subprograms) is a real finding. */
class AlgebraicLaws extends FunSuite:
  import Space.*

  private val mentionNames = Vector("a", "b", "c")
  private val syms = Vector("p", "q", "r")
  private val eps = Path.Constant(PathValue(Nil))

  private def pathItem(rng: scala.util.Random): PathItem = syms(rng.nextInt(syms.length))
  private def randPath(rng: scala.util.Random): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(pathItem(rng)))
  private def oneItemPath(rng: scala.util.Random): PathValue = PathValue(List(pathItem(rng)))
  private def randLiteral(rng: scala.util.Random): SpaceValue =
    SpaceValue((0 to rng.nextInt(4)).map(_ => randPath(rng)).toSet)

  /** A random Space in the non-recursive, non-grounded fragment (so `eval` is total on it). */
  private def randSpace(depth: Int, vars: Vector[String], pvars: Vector[String], rng: scala.util.Random): Space =
    def leaf(): Space = rng.nextInt(5) match
      case 0 => Empty
      case 1 => Literal(randLiteral(rng))
      case 2 if vars.nonEmpty => Mention(SpaceMention(vars(rng.nextInt(vars.length))))
      case 3 if pvars.nonEmpty => Singleton(Path.Deref(PathRef(pvars(rng.nextInt(pvars.length))).known(1)))
      case _ => Singleton(Path.Constant(randPath(rng)))
    if depth <= 0 then leaf()
    else
      def sub() = randSpace(depth - 1, vars, pvars, rng)
      rng.nextInt(12) match
        case 0 => Union(sub(), sub())
        case 1 => Intersection(sub(), sub())
        case 2 => Subtraction(sub(), sub())
        case 3 => Restriction(sub(), sub())
        case 4 => Raffination(sub(), sub())
        case 5 => Composition(sub(), sub())
        case 6 => Wrap(sub(), Path.Constant(randPath(rng)))
        case 7 => Unwrap(sub(), Path.Constant(randPath(rng)))
        case 8 => TailsUnion(sub())
        case 9 => TailsIntersection(sub())
        case 10 => { val lo = rng.nextInt(3); Range(sub(), lo, lo + 1 + rng.nextInt(3)) }
        case _ =>
          val h = s"h${rng.nextInt(1000)}"; val t = s"t${rng.nextInt(1000)}"
          Iteration(sub(), PathRef(h).known(1), SpaceMention(t), randSpace(depth - 1, vars :+ t, pvars :+ h, rng))

  test("metamorphic: the path-set algebra laws hold under the reference eval (400 seeds)") {
    var checks = 0
    for seed <- 0 until 400 do
      val rng = new scala.util.Random(seed.toLong * 0x27D4EB2FL + 7)
      val binds = mentionNames.map(m => SpaceMention(m) -> randLiteral(rng)).toMap
      given SpaceContext = SpaceContextMap(binds)
      def a = randSpace(2, mentionNames, Vector.empty, rng)
      def b = randSpace(2, mentionNames, Vector.empty, rng)
      def c = randSpace(2, mentionNames, Vector.empty, rng)
      val (x, y, z) = (a, b, c)
      val p = Path.Constant(randPath(rng)); val q = Path.Constant(oneItemPath(rng))
      def law(name: String, l: Space, r: Space): Unit =
        assertEquals(eval(l), eval(r), s"LAW $name seed=$seed\n l=${l.show}\n r=${r.show}"); checks += 1

      // --- Union: commutative, associative, idempotent, Empty unit ---
      law("union-comm", Union(x, y), Union(y, x))
      law("union-assoc", Union(x, Union(y, z)), Union(Union(x, y), z))
      law("union-idem", Union(x, x), x)
      law("union-unit-r", Union(x, Empty), x)
      law("union-unit-l", Union(Empty, x), x)
      // --- Intersection: commutative, associative, idempotent, Empty annihilator ---
      law("inter-comm", Intersection(x, y), Intersection(y, x))
      law("inter-assoc", Intersection(x, Intersection(y, z)), Intersection(Intersection(x, y), z))
      law("inter-idem", Intersection(x, x), x)
      law("inter-annih-r", Intersection(x, Empty), Empty)
      law("inter-annih-l", Intersection(Empty, x), Empty)
      // --- Subtraction / Restriction / Raffination ---
      law("sub-self", Subtraction(x, x), Empty)
      law("sub-unit-r", Subtraction(x, Empty), x)
      law("sub-annih-l", Subtraction(Empty, x), Empty)
      law("restr-self", Restriction(x, x), x)
      law("restr-empty-r", Restriction(x, Empty), Empty)
      law("restr-empty-l", Restriction(Empty, x), Empty)
      law("raff-self", Raffination(x, x), Empty)
      law("raff-def", Raffination(x, y), Subtraction(x, Restriction(x, y)))   // definition
      // --- Composition: associative, Empty annihilator ---
      law("comp-assoc", Composition(x, Composition(y, z)), Composition(Composition(x, y), z))
      law("comp-annih-l", Composition(Empty, x), Empty)
      law("comp-annih-r", Composition(x, Empty), Empty)
      // --- Wrap / Unwrap round-trips and ε ---
      law("unwrap-wrap", Unwrap(Wrap(x, p), p), x)
      law("wrap-eps", Wrap(x, eps), x)
      law("unwrap-eps", Unwrap(x, eps), x)
      law("wrap-empty", Wrap(Empty, p), Empty)
      law("unwrap-empty", Unwrap(Empty, p), Empty)
      law("tailsunion-wrap1", TailsUnion(Wrap(x, q)), x)   // q single-item: drop the wrapped head
      // --- Distribution over Union ---
      law("unwrap/union", Unwrap(Union(x, y), p), Union(Unwrap(x, p), Unwrap(y, p)))
      law("wrap/union", Wrap(Union(x, y), p), Union(Wrap(x, p), Wrap(y, p)))
      law("comp-l/union", Composition(Union(x, y), z), Union(Composition(x, z), Composition(y, z)))
      law("comp-r/union", Composition(x, Union(y, z)), Union(Composition(x, y), Composition(x, z)))
      law("restr/union-by", Restriction(x, Union(y, z)), Union(Restriction(x, y), Restriction(x, z)))
      law("inter/union", Intersection(x, Union(y, z)), Union(Intersection(x, y), Intersection(x, z)))
      law("sub-l/union", Subtraction(Union(x, y), z), Union(Subtraction(x, z), Subtraction(y, z)))
      law("tailsunion/union", TailsUnion(Union(x, y)), Union(TailsUnion(x), TailsUnion(y)))
      // --- Range (ordered slice) identities ---
      law("range-full", Range(x, 0, 0), x)                  // [0,size) = everything
      law("range-empty", Range(Empty, 1, 3), Empty)
      law("range-nest-prefix", Range(Range(x, 0, 4), 0, 2), Range(x, 0, 2))   // first 2 of first 4 = first 2
      law("range-idem-prefix", Range(Range(x, 0, 3), 0, 3), Range(x, 0, 3))
    System.out.println(s"ALGEBRAIC LAWS: $checks identities checked over 400 seeds")
    assert(checks > 0)
  }
end AlgebraicLaws
