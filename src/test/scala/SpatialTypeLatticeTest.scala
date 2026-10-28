package morkl

import munit.FunSuite

/** Finite executable model of the semantic lattice used by the FOL spatial
  * obligations. The production `SpatialType` is a finite reduced product over
  * this interval envelope; this oracle deliberately tests the quotient lattice
  * independently of the implementation's representation choices.
  */
class SpatialTypeLatticeTest extends FunSuite:
  private type Concrete = Set[Int]

  private enum Abstract:
    case Bottom
    case Interval(must: Concrete, may: Concrete)

  import Abstract.*

  private val universe: Concrete = Set(0, 1, 2)
  private val concrete: Vector[Concrete] =
    universe.subsets().map(_.toSet).toVector
  private val intervals: Vector[Abstract] =
    (for
      must <- concrete
      may <- concrete
      if must.subsetOf(may)
    yield Interval(must, may)).toVector
  private val domain: Vector[Abstract] = Bottom +: intervals
  private val top: Abstract = Interval(Set.empty, universe)

  private def gamma(value: Abstract): Set[Concrete] = value match
    case Bottom => Set.empty
    case Interval(must, may) => concrete.filter(space => must.subsetOf(space) && space.subsetOf(may)).toSet

  private def leq(left: Abstract, right: Abstract): Boolean =
    gamma(left).subsetOf(gamma(right))

  private def normalize(must: Concrete, may: Concrete): Abstract =
    if must.subsetOf(may) then Interval(must, may) else Bottom

  private def join(left: Abstract, right: Abstract): Abstract = (left, right) match
    case (Bottom, value) => value
    case (value, Bottom) => value
    case (Interval(lm, lp), Interval(rm, rp)) => Interval(lm.intersect(rm), lp.union(rp))

  private def meet(left: Abstract, right: Abstract): Abstract = (left, right) match
    case (Bottom, _) | (_, Bottom) => Bottom
    case (Interval(lm, lp), Interval(rm, rp)) => normalize(lm.union(rm), lp.intersect(rp))

  private def supremum(values: Iterable[Abstract]): Abstract =
    values.foldLeft(Bottom: Abstract)(join)

  private def infimum(values: Iterable[Abstract]): Abstract =
    values.foldLeft(top)(meet)

  private def collecting(results: Set[Concrete]): Abstract =
    if results.isEmpty then Bottom
    else Interval(results.reduce(_.intersect(_)), results.reduce(_.union(_)))

  private def mask(values: Concrete): Int =
    values.foldLeft(0)((result, item) => result | (1 << item))

  private def finite(value: Abstract): FiniteSpatialTypeBridge.Interval = value match
    case Bottom => FiniteSpatialTypeBridge.Interval(isBottom = true, 0, 0)
    case Interval(must, may) =>
      FiniteSpatialTypeBridge.Interval(isBottom = false, mask(must), mask(may))

  private def abstractValue(value: FiniteSpatialTypeBridge.Interval): Abstract =
    if value.isBottom then Bottom
    else
      def members(bits: Int): Concrete =
        (0 until FiniteSpatialTypeBridge.Width).filter(item => (bits & (1 << item)) != 0).toSet
      Interval(members(value.mustMask), members(value.mayMask))

  /** Shared production embedding and fail-closed decoder. The semantic oracle
    * above remains independently implemented in sets.
    */
  private def production(value: Abstract): SpatialType =
    FiniteSpatialTypeBridge.embed(finite(value))

  private def semantic(value: SpatialType): Abstract =
    FiniteSpatialTypeBridge.decode(value).fold(
      reason => fail(s"finite production bridge rejected output: $reason"),
      abstractValue,
    )

  test("the normalized interval quotient is a bounded lattice") {
    domain.foreach { a =>
      assert(leq(Bottom, a))
      assert(leq(a, top))
      assertEquals(join(a, a), a)
      assertEquals(meet(a, a), a)
      assertEquals(meet(a, join(a, top)), a)
      assertEquals(join(a, meet(a, Bottom)), a)
    }
    for a <- domain; b <- domain do
      assertEquals(join(a, b), join(b, a))
      assertEquals(meet(a, b), meet(b, a))
      assert(leq(a, join(a, b)))
      assert(leq(b, join(a, b)))
      assert(leq(meet(a, b), a))
      assert(leq(meet(a, b), b))
      domain.foreach { c =>
        assertEquals(join(join(a, b), c), join(a, join(b, c)))
        assertEquals(meet(meet(a, b), c), meet(a, meet(b, c)))
        if leq(a, c) && leq(b, c) then assert(leq(join(a, b), c))
        if leq(c, a) && leq(c, b) then assert(leq(c, meet(a, b)))
      }
    assertEquals(domain.size, 28) // bottom plus 3^|universe| valid intervals
  }

  test("normalizing inconsistent meets makes the interval lattice non-distributive") {
    val meetOverJoinFails = (for a <- domain; b <- domain; c <- domain yield
      meet(a, join(b, c)) != join(meet(a, b), meet(a, c))).exists(identity)
    val joinOverMeetFails = (for a <- domain; b <- domain; c <- domain yield
      join(a, meet(b, c)) != meet(join(a, b), join(a, c))).exists(identity)
    assert(meetOverJoinFails)
    assert(joinOverMeetFails)
  }

  test("finite arbitrary suprema and infima satisfy their universal properties") {
    val collections =
      Vector(Vector.empty[Abstract], domain) ++
        domain.map(Vector(_)) ++
        domain.combinations(2).map(_.toVector).toVector ++
        domain.combinations(3).map(_.toVector).toVector
    collections.foreach { values =>
      val sup = supremum(values)
      val inf = infimum(values)
      values.foreach { value =>
        assert(leq(value, sup))
        assert(leq(inf, value))
      }
      domain.foreach { bound =>
        if values.forall(leq(_, bound)) then assert(leq(sup, bound))
        if values.forall(leq(bound, _)) then assert(leq(bound, inf))
      }
    }
    assertEquals(supremum(Vector.empty), Bottom)
    assertEquals(infimum(Vector.empty), top)
  }

  test("closed-form precision order and exact abstraction agree with concretization") {
    intervals.foreach {
      case left @ Interval(lm, lp) =>
        intervals.foreach {
          case right @ Interval(rm, rp) =>
            assertEquals(leq(left, right), rm.subsetOf(lm) && lp.subsetOf(rp))
          case Bottom => fail("interval enumeration cannot contain bottom")
        }
      case Bottom => fail("interval enumeration cannot contain bottom")
    }
    concrete.foreach { space =>
      assertEquals(gamma(Interval(space, space)), Set(space))
    }
  }

  test("union, intersection, and subtraction formulas are best correct intervals") {
    val operations = Vector[(Concrete, Concrete) => Concrete](_ union _, _ intersect _, _ diff _)
    intervals.foreach {
      case left @ Interval(lm, lp) =>
        intervals.foreach {
          case right @ Interval(rm, rp) =>
            val formulas = Vector[Abstract](
              Interval(lm union rm, lp union rp),
              Interval(lm intersect rm, lp intersect rp),
              normalize(lm diff rp, lp diff rm)
            )
            operations.zip(formulas).foreach { (operation, formula) =>
              val results = for l <- gamma(left); r <- gamma(right) yield operation(l, r)
              assertEquals(formula, collecting(results))
              assert(results.subsetOf(gamma(formula)))
            }
          case Bottom => fail("interval enumeration cannot contain bottom")
        }
      case Bottom => fail("interval enumeration cannot contain bottom")
    }
  }

  test("production spatial types expose bottom, join, meet, order, and widening") {
    val one = SpatialType.lengths(1 -> ResultSizeEstimate.exact(SizeExpr.One))
    val two = SpatialType.lengths(2 -> ResultSizeEstimate.exact(SizeExpr.const(2)))
    val joined = SpatialType.join(one, two)
    assert(SpatialType.lessOrEqual(SpatialType.bottom, one))
    assert(SpatialType.lessOrEqual(one, joined))
    assert(SpatialType.lessOrEqual(two, joined))
    assertEquals(SpatialType.join(SpatialType.bottom, one), one)
    assertEquals(SpatialType.meet(SpatialType.bottom, one), SpatialType.bottom)
    assertEquals(SpatialType.join(one, one), one)
    assertEquals(SpatialType.meet(one, one), one)

    val contradiction = SpatialType.reduce(one.copy(size = ResultSizeEstimate(
      SizeExpr.One, SizeExpr.const(2))))
    assert(contradiction.isBottom)

    val widened = SpatialType.widenCardinalities(joined)
    assertEquals(widened.size.upper, SizeExpr.Infinity)
    assert(SpatialType.lessOrEqual(joined, widened))
    assertEquals(widened.pathLength, joined.pathLength)
  }

  test("production SpatialType join, meet, and reduction implement every finite set interval") {
    domain.foreach { value =>
      assertEquals(semantic(production(value)), value)
      assertEquals(semantic(SpatialType.reduce(production(value))), value)
    }
    val impossible = production(Interval(Set.empty, Set(0))).copy(
      size = ResultSizeEstimate.exact(SizeExpr.const(2)))
    assertEquals(SpatialType.reduce(impossible), SpatialType.bottom)
    val exactOne = production(Interval(Set(1), Set(1)))
    val requiresMissingZero = production(Interval(Set(0), Set(0, 1)))
    assert(!SpatialType.lessOrEqual(exactOne, requiresMissingZero),
      "an absent mandatory right stratum must prevent convergence")
    val inconsistentMandatory = production(Interval(Set(0), Set(0))).copy(
      size = ResultSizeEstimate.empty)
    assert(!SpatialType.lessOrEqual(production(Interval(Set.empty, Set.empty)), inconsistentMandatory),
      "empty inclusion must still inspect unreduced mandatory strata")
    for left <- domain; right <- domain do
      assertEquals(
        SpatialType.lessOrEqual(production(left), production(right)),
        leq(left, right),
        s"order bridge failed for $left and $right",
      )
      assertEquals(
        semantic(SpatialType.joinAlternatives(production(left), production(right))),
        join(left, right),
        s"join bridge failed for $left and $right",
      )
      assertEquals(
        semantic(SpatialType.meet(production(left), production(right))),
        meet(left, right),
        s"meet bridge failed for $left and $right",
      )
  }
