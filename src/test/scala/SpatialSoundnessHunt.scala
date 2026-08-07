package morkl

import munit.FunSuite
import scala.collection.immutable.SortedMap

/** THE SOUNDNESS HUNTER — an adversarial randomized differential gate against every claim the
 *  spatial type system makes.
 *
 *  This suite is deliberately NOT a regression test for the bugs already found.  It is a hunter:
 *  it generates random `Space` terms over a tiny alphabet using EVERY constructor (including the
 *  ones the existing matrix under-covers: nested binders whose bodies read OUTER binders,
 *  interprocedural and recursive `Call`, `Fold` with a real accumulator update, `Fixpoint` with
 *  set-op bodies, `Range` with every sign combination), binds the free names with random
 *  ENVIRONMENTS THAT ARE NOT EXACT (weakened shapes, ⊤ on one component, open head sets, a lub of
 *  two point abstractions), evaluates the term with the reference `eval`, infers the spatial type,
 *  and then checks EVERY claim the type makes about the value:
 *
 *    - `SpatialTyping.withinEnvelope` (the dispatcher envelope) and `SpatialTyping.gammaMember` (full
 *      γ-membership) and `SpatialGamma.gamma` (the independent copy);
 *    - the per-length count bracket `t.lens.at(L)` for every length, populated or not — the
 *      soundness statement in the header of SpatialTypes.scala;
 *    - `size.lo`/`size.hi` AND `size.loHeaded` (a lower bound on the number of length-≥1 paths,
 *      which no other suite checks);
 *    - `len.lo`/`len.hi` as a ∀-path fact, and non-emptiness versus `len.isEmpty`;
 *    - the distinct-head count against `headCount`;
 *    - the four shape channels individually (ε / tracked head / untracked count / other-tail), so a
 *      failure names the channel and the trie position it failed at;
 *    - `mayHavePrefix` (a `false` is a PROOF of absence) and `mustHaveHead`;
 *    - EVERY `Fact` in `Fact.from(t)` — the highest-value check, because a wrong Fact is exactly
 *      what an optimizer would act on.
 *
 *  Also gated: the ABSTRACTION itself.  Every declared input type is checked to contain the
 *  concrete value it was built from (`α` and `SpatialGamma.lub` soundness); a failure there is
 *  reported separately, because it would make every downstream verdict vacuous.
 *
 *  `eval` appears ONLY here, as ground truth — never inside the analysis
 *  (docs/design_spatial_lattice.md §0).  Every violation is delta-debugged to a minimal witness
 *  (term AND environment, since a witness that needs an inexact declared input is not reproducible
 *  from the term alone). */
class SpatialSoundnessHunt extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(60, "min")

  /** `HUNT_SCALE=0.01` runs a smoke-sized sweep; the default is the full gate. */
  private val scale: Double =
    sys.env.get("HUNT_SCALE").flatMap(s => scala.util.Try(s.toDouble).toOption).getOrElse(1.0)
  private def n(k: Int): Int = math.max(1, (k * scale).toInt)

  private def run(name: String, seed: Long, cases: Int, cfg: Hunt.Cfg): Hunt.Result =
    val r = Hunt.sweep(seed, n(cases), cfg)
    println(r.render(name))
    r

  test("HUNT 1: closed terms, exact declared inputs, all constructors") {
    val r = run("HUNT 1 closed/exact", 0x5EED01L, 24000,
                Hunt.Cfg(alpha = Hunt.A3, maxPaths = 4, maxLen = 3, depth = 4,
                         exactEnv = true, hints = false, recCall = true))
    assertEquals(r.violations, 0, r.firstWitness)
  }

  test("HUNT 2: APPROXIMATE declared inputs (weakened / ⊤ / open heads / lub) and opaque refs") {
    val r = run("HUNT 2 approx env", 0x5EED02L, 24000,
                Hunt.Cfg(alpha = Hunt.A3, maxPaths = 4, maxLen = 3, depth = 4,
                         exactEnv = false, hints = true, recCall = true))
    assertEquals(r.violations, 0, r.firstWitness)
  }

  test("HUNT 3: deep nesting, binder bodies that read OUTER binders") {
    val r = run("HUNT 3 deep/binders", 0x5EED03L, 12000,
                Hunt.Cfg(alpha = Hunt.A3, maxPaths = 3, maxLen = 3, depth = 6,
                         exactEnv = false, hints = true, recCall = true, binderBias = true))
    assertEquals(r.violations, 0, r.firstWitness)
  }

  test("HUNT 4: the degenerate shapes — 1-2 items, many epsilons, empty operands") {
    val r = run("HUNT 4 degenerate", 0x5EED04L, 20000,
                Hunt.Cfg(alpha = Hunt.A2, maxPaths = 3, maxLen = 2, depth = 4,
                         exactEnv = false, hints = true, recCall = true, epsBias = true))
    assertEquals(r.violations, 0, r.firstWitness)
  }

  test("HUNT 5: past the caps — >MaxHeads distinct heads and >MaxDepth long paths") {
    val r = run("HUNT 5 wide/deep", 0x5EED05L, 9000,
                Hunt.Cfg(alpha = Hunt.ABig, maxPaths = 26, maxLen = 7, depth = 3,
                         exactEnv = false, hints = true, recCall = false))
    assertEquals(r.violations, 0, r.firstWitness)
  }

  test("HUNT 7: the per-transfer γ-simulation matrix on ADVERSARIAL abstract inputs") {
    // ground truth first: the concrete set operations used below must agree with the reference
    // `eval`, or every verdict in this matrix is meaningless
    val g = Hunt.groundTruthCheck(0xC0FFEEL, n(3000))
    assertEquals(g, Vector.empty[String], "the hunter's concrete operations disagree with eval")
    val r = Hunt.transferMatrix(0x5EED07L, n(60000), 3)
    println(r.render("HUNT 7 transfers"))
    assertEquals(r.violations, 0, r.firstWitness)
  }

  test("HUNT 8: the order, the widenings and the lub — γ-containment laws") {
    val r = Hunt.orderLaws(0x5EED08L, n(40000))
    println(r.render("HUNT 8 order/widen"))
    assertEquals(r.violations, 0, r.firstWitness)
  }

  /** MEASUREMENT, not a gate for every operator, and the reason is now settled rather than unstated.
   *
   *  `sub`, `raffination` and `tailsInter` CONSUME an operand's MUST channel — `sub` uses
   *  `b.eps.mustBe` to prove ε removed, `tailsInter` intersects only the children of must-present
   *  heads.  That is legitimate and is the point of review.md finding 1, but it means those three are
   *  sound in the STRONG reading only: subtraction is antitone in its right operand, so an operand
   *  read may-only licenses a LARGER result than `sub#` returns.  They will therefore always appear
   *  in this table, and the three rows are a documented NON-law, not an open bug.
   *
   *  What makes that safe is that the analysis never reads a shape may-only and then feeds it back
   *  into a transfer.  It does pass WEAKENED shapes in (`Shape.under` on an untracked head,
   *  `groupUnion`'s `rest` binding, `SpatialTyping.fixpoint`'s iterate) — but `γ_s(s) ⊆ γ_s(weaken s)`,
   *  so a weakened shape is still a valid STRONG abstraction of the same value and HUNT 7 covers it.
   *  `fixpoint` in particular keeps its iterate may-only precisely so that `γ_may = γ_s` there and the
   *  body is analysed in the reading its transfers are sound for.
   *
   *  So only the pure loosening operators are asserted — those must hold in both readings because
   *  `weaken`/`openCounts`/`widenShape`/`capDepth` are the operations the may reading is DEFINED by. */
  test("HUNT 9: which transfers are sound in the MAY reading (what Fixpoint relies on)") {
    val r = Hunt.mayMatrix(0x5EED09L, n(40000), 3)
    println(r.render("HUNT 9 may-reading"))
    val mustHold = Set("weaken", "openCounts", "widenShape", "capDepth")
    val broken = r.bad.filter((k, _) => mustHold.exists(op => k.startsWith(op + " ::")))
    assertEquals(broken.size, 0, broken.map((k, v) => s"$k -> ${v._2}").mkString("\n"))
  }

  // ===============================================================================================
  // THE MINIMAL WITNESSES the hunts above reduced to, pinned as named regressions.
  //
  // These three tests were written as bug reports against the then-current implementation and FAILED
  // on it.  Each asserts only SOUNDNESS (the concrete value satisfies the inferred type / the claimed
  // order really is γ-containment), so each started passing exactly when the defect was fixed and
  // never pinned the buggy behaviour.  All three are GREEN as of the integration commit; the fixes
  // landed in SpatialTyping.fixpoint, Shape.leq/Shape.lub and the SpatialTypes Subtraction transfer
  // respectively.  They stay here as named regressions.
  // ===============================================================================================

  /** WITNESS 1 — `Fixpoint` whose body deletes members through a MUST channel.
   *
   *  `Literal({a.b}).fix(k){TailsIntersection($k)}` really evaluates to `{a.b, b, ε}`: the concrete
   *  operator accumulates the UNION of the iterates `{a.b}`, `TI({a.b}) = {b}`, `TI({b}) = {ε}`,
   *  `TI({ε}) = ∅`.  The analysis infers `{a·{b·{ε!}}, b·{ε?}}` — ε=No, a CLOSED head set, and
   *  `size.hi = 2` — so it excludes ε and one whole path, and licenses the FALSE facts
   *  `MaximumCardinality(2)` and `AllPathsHaveAtLeast(1)`.
   *
   *  Why: the Kleene chain joins iterates with `Shape.union`, the UNION TRANSFER, which keeps MUST
   *  from BOTH operands — so `γ(x) ⊄ γ(union(x, y))` and the join is not an upper bound.  The
   *  candidate `t = union(i0, tailsInter(i0)) = {a·{b·{ε!}}, b·{ε!}}` therefore forces BOTH heads,
   *  which makes `tailsInter(t)` intersect the two children and return ∅ — so the loop converges
   *  one round early and never sees the ε that `TI({b})` produces.
   *
   *  HOW IT WAS FIXED (it is green now): `fixpoint` ascends with the real join [[Shape.lub]] and keeps
   *  every iterate MAY-ONLY.  Being may-only is what closes the argument — `γ_may = γ_s` there, so
   *  `Shape.leq` (a γ_may order) is exactly the right certificate AND the body is still analysed by
   *  the transfers in the STRONG reading they are sound for, which is what the three permanent HUNT 9
   *  rows require.  The accumulated union is then bounded by `openCounts` of the candidate, because
   *  `γ` of a shape is not closed under unbounded union. */
  test("WITNESS 1: Fixpoint over a MUST-consuming body excludes real members of its own result") {
    val src = Space.Literal(SpaceValue(Set(PathValue(List("a", "b")))))
    val k = SpaceMention("k")
    val term = Space.Fixpoint(src, k, Space.TailsIntersection(Space.Mention(k)))
    val v = eval(term)
    assertEquals(Hunt.showSV(v), "{a.b,b,ε}", "ground truth: the union of the iterates")
    val t = SpatialTyping.infer(term)
    val bad = Hunt.checkClaims(v, t)
    assertEquals(bad, Vector.empty[String],
      s"inferred ${t.show}\n  size=${t.size} len=${t.len} headCount=${t.headCount.show}\n" +
      s"  facts=${Fact.from(t).map(_.show).mkString(", ")}")
  }

  /** WITNESS 1b — THE CONSUMER CONSEQUENCE of witness 1.  The wrong shape says ε ∉ result, so
   *  meeting the same `Fixpoint` with `{ε}` is inferred DEFINITELY EMPTY while it really evaluates
   *  to `{ε}`.  `Fact.DefinitelyEmpty` and `isProvablyEmpty` are exactly what `Lower.eliminate`
   *  consumes, so this is the shape of an optimizer replacing a live subterm by `Empty`.  Observed by
   *  the hunts as the broken-claim keys `isProvablyEmpty @Restriction` / `Fact.DefinitelyEmpty
   *  @Restriction` (HUNT 1 and HUNT 5); reproduced here in two nodes. */
  test("WITNESS 1b: a non-empty term is inferred DEFINITELY EMPTY (what eliminate acts on)") {
    val src = Space.Literal(SpaceValue(Set(PathValue(List("a", "b")))))
    val k = SpaceMention("k")
    val fx = Space.Fixpoint(src, k, Space.TailsIntersection(Space.Mention(k)))
    val term = Space.Intersection(fx, Space.Literal(SpaceValue(Set(PathValue(Nil)))))
    assertEquals(Hunt.showSV(eval(term)), "{ε}", "ground truth: the fixpoint result contains ε")
    val t = SpatialTyping.infer(term)
    assert(!t.isProvablyEmpty, s"inferred provably empty: ${t.show}")
    assert(!Fact.from(t).contains(Fact.DefinitelyEmpty), s"facts: ${Fact.from(t).map(_.show)}")
  }

  /** WITNESS 2 — `Shape.leq` claims an order it does not have.
   *
   *  `leq(a, b)` is documented as `γ_may(a) ⊆ γ_may(b)`, and it is the order
   *  `SpatialTyping.fixpoint` uses both to detect convergence and to accept a post-fixpoint.  It
   *  iterates over `a`'s LIVE TRACKED HEADS only, so a head that `b` TRACKS and `a` leaves untracked
   *  is never compared: a value that puts that head in `a`'s untracked bucket (tails ⊤) becomes a
   *  TRACKED head for `b` and must then satisfy `b`'s child, which it need not.
   *  `SpatialGamma.leqShape` keys on `a.heads.keySet ++ b.heads.keySet` and gets this right. */
  test("WITNESS 2: Shape.leq ignores heads the right-hand side tracks and the left does not") {
    val a = Shape.capDepth(Shape.of(SpaceValue(Set(PathValue(Nil), PathValue(List("x"))))), 0)
    val b = Shape.weaken(Shape.widenShape(
      Shape.of(SpaceValue(Set(PathValue(Nil), PathValue(List("a", "b")))))))
    val v = SpaceValue(Set(PathValue(Nil), PathValue(List("a"))))
    assert(SpatialGamma.gammaShapeMay(a, v), s"precondition: ${Hunt.showSV(v)} in γ_may(${a.show})")
    assert(!SpatialGamma.gammaShapeMay(b, v), s"precondition: not in γ_may(${b.show})")
    assert(!SpatialGamma.leqShape(a, b), "precondition: the strong order correctly says no")
    assert(!Shape.leq(a, b),
      s"Shape.leq(${a.show}, ${b.show}) claims γ_may containment, but ${Hunt.showSV(v)} is in the " +
      "first and not the second")
  }

  /** WITNESS 3 — the histogram's `Subtraction` transfer keeps a lower bound the subtrahend deletes.
   *
   *  `SpatialTypes` Subtraction computes the SPILL bucket as
   *  `Ivl(relu(x.rest.lo - y.rest.hi), x.rest.hi)`.  It subtracts only `y`'s own spill total and
   *  ignores every class `y` TRACKS, even though those lengths lie inside `x`'s spill window and
   *  those paths can be exactly the ones `x.rest.lo` was counting.  Here `x = s0 ∪ TU(L)` has
   *  `rest = [2, ∞)` (the `join` spill branch: `|A ∪ B| ≥ max(|A|,|B|) ≥ |TU(L)| = 2`) and
   *  `y = TU(L)` tracks `len 1: [1,1]`, `len 2: [1,1]` with an empty spill, so the transfer keeps
   *  `rest.lo = 2` — and claims `DefinitelyNonEmpty` / `MinimumCardinality(2)` about the empty set. */
  test("WITNESS 3: Subtraction's spill lower bound ignores the subtrahend's tracked classes") {
    val lit = Space.Literal(SpaceValue(Set(PathValue(List("a", "b")), PathValue(List("d", "d", "a")))))
    val y = Space.TailsUnion(lit)
    val s0 = SpaceMention("s0")
    val term = Space.Subtraction(Space.Union(Space.Mention(s0), y), y)
    val env = SpatialTyping.Env(spaces = Map(s0 -> SpatialType.top))
    val v = eval(term)(using PathContextMap(Map.empty), SpaceContextMap(Map(s0 -> SpaceValue(Set.empty))))
    assertEquals(Hunt.showSV(v), "∅", "ground truth: (∅ ∪ y) ∖ y = ∅")
    val t = SpatialTyping.infer(term, env)
    val bad = Hunt.checkClaims(v, t)
    // the same defect with no `Union` and no declared input at all, which rules out the `join`
    // spill branch as the cause: an unknown-length `Singleton` is `boundedExact([0,∞), 1)`, i.e.
    // `rest = [1,1]`, and subtracting a literal that TRACKS `len 0` still leaves `rest.lo = 1`
    val p0 = PathRef("p0")
    val small = Space.Subtraction(Space.Singleton(Path.Deref(p0)),
                                 Space.Literal(SpaceValue(Set(PathValue(Nil)))))
    val vs = eval(small)(using PathContextMap(Map(p0 -> PathValue(Nil))), SpaceContextMap(Map.empty))
    assertEquals(Hunt.showSV(vs), "∅", "ground truth: {ε} ∖ {ε} = ∅")
    val ts = SpatialTyping.infer(small)
    assertEquals(bad ++ Hunt.checkClaims(vs, ts), Vector.empty[String],
      s"corpus witness inferred ${t.show}\n  size=${t.size}\n" +
      s"  facts=${Fact.from(t).map(_.show).mkString(", ")}\n" +
      s"minimal witness  inferred ${ts.show}\n  size=${ts.size}\n" +
      s"  facts=${Fact.from(ts).map(_.show).mkString(", ")}")
  }

  test("HUNT 6: the corpus, analysed OPEN under approximate declared inputs") {
    val recs = Hunt.corpus
    assume(recs.nonEmpty, "corpus_1000.ser not found")
    val r = Hunt.sweepCorpus(recs.take(n(recs.size)), 0x5EED06L, math.max(1, n(4)))
    println(r.render("HUNT 6 corpus/open"))
    assertEquals(r.violations, 0, r.firstWitness)
  }
end SpatialSoundnessHunt

/** The hunter's machinery: generators, the abstraction recipes, the claim checker with per-channel
 *  attribution, and a delta-debugger over (term, environment) pairs. */
object Hunt:
  import Lower.{LenBounds, SizeBounds}

  val A2: Vector[PathItem] = Vector("a", "b")
  val A3: Vector[PathItem] = Vector("a", "b", "c")
  /** 18 items > `Shape.MaxHeads` = 12, so the width spill into `others`/`otherTail` actually fires */
  val ABig: Vector[PathItem] = (0 until 18).map(i => ('a' + i).toChar.toString).toVector

  /** a hard wall-clock budget per sweep, so a pathological term can never hang the gate */
  val budgetNanos: Long =
    sys.env.get("HUNT_BUDGET_MIN").flatMap(s => scala.util.Try(s.toLong).toOption).getOrElse(12L) *
      60L * 1000000000L

  val sNames: Vector[SpaceMention] = (0 until 3).map(i => SpaceMention("s" + i)).toVector
  val pNames: Vector[PathRef] = (0 until 3).map(i => PathRef("p" + i)).toVector

  // -----------------------------------------------------------------------------------------------
  // a total pretty-printer (`Space.show` has no `Fold` arm, so it is not usable in a diagnostic)
  // -----------------------------------------------------------------------------------------------
  def pp(s: Space): String = s match
    case Space.Empty => "0"
    case Space.Literal(v) => "L" + v.paths.toVector.map(x => x.items.mkString(".")).sorted.mkString("{", ",", "}")
    case Space.Singleton(p) => "S(" + ppp(p) + ")"
    case Space.Mention(m) => "$" + m.s
    case Space.Union(a, b) => s"(${pp(a)} u ${pp(b)})"
    case Space.Intersection(a, b) => s"(${pp(a)} n ${pp(b)})"
    case Space.Subtraction(a, b) => s"(${pp(a)} \\ ${pp(b)})"
    case Space.Restriction(a, b) => s"(${pp(a)} <| ${pp(b)})"
    case Space.Raffination(a, b) => s"(${pp(a)} \\| ${pp(b)})"
    case Space.Composition(a, b) => s"(${pp(a)} . ${pp(b)})"
    case Space.Wrap(a, p) => s"(${ppp(p)} x ${pp(a)})"
    case Space.Unwrap(a, p) => s"${pp(a)}/${ppp(p)}"
    case Space.TailsUnion(a) => s"TU(${pp(a)})"
    case Space.TailsIntersection(a) => s"TI(${pp(a)})"
    case Space.Range(a, l, h) => s"Rng(${pp(a)},$l,$h)"
    case Space.Iteration(x, y, r, b) => s"${pp(x)}.iter(${y.s},${r.s}){${pp(b)}}"
    case Space.Fold(x, i, ac, y, r, b, u) =>
      s"${pp(x)}.fold(${ppp(i)};${ac.s},${y.s},${r.s}){${pp(b)}}upd[${ppp(u)}]"
    case Space.Fixpoint(i, r, b) => s"${pp(i)}.fix(${r.s}){${pp(b)}}"
    case Space.Call(r, rs, ms) => s"${r.s}(${rs.map(ppp).mkString(",")};${ms.map(pp).mkString(",")})"
    case Space.GroundedPS(p, _) => s"gPS(${ppp(p)})"
    case Space.GroundedSS(x, _) => s"gSS(${pp(x)})"

  def ppp(p: Path): String = p match
    case Path.Constant(v) => "\"" + v.items.mkString(".") + "\""
    case Path.Deref(r) => "?" + r.s + (if r.lengthHint >= 0 then "{" + r.lengthHint + "}" else "")
    case Path.Concat(a, b) => ppp(a) + "++" + ppp(b)
    case Path.GroundedPP(a, _) => "gPP(" + ppp(a) + ")"
    case Path.GroundedSP(x, _) => "gSP(" + pp(x) + ")"

  /** `SpaceValue.pretty` renders BOTH `∅` and `{ε}` as `{}` — an ambiguity that makes every
   *  ε-related witness unreadable, so diagnostics use this instead. */
  def showSV(v: SpaceValue): String =
    if v.paths.isEmpty then "∅"
    else v.paths.toVector.map(p => if p.items.isEmpty then "ε" else p.items.mkString(".")).sorted.mkString("{", ",", "}")

  def opName(s: Space): String = s match
    case Space.Empty => "Empty"
    case Space.Literal(_) => "Literal"
    case Space.Singleton(_) => "Singleton"
    case Space.Mention(_) => "Mention"
    case Space.Union(_, _) => "Union"
    case Space.Intersection(_, _) => "Intersection"
    case Space.Subtraction(_, _) => "Subtraction"
    case Space.Restriction(_, _) => "Restriction"
    case Space.Raffination(_, _) => "Raffination"
    case Space.Composition(_, _) => "Composition"
    case Space.Wrap(_, _) => "Wrap"
    case Space.Unwrap(_, _) => "Unwrap"
    case Space.TailsUnion(_) => "TailsUnion"
    case Space.TailsIntersection(_) => "TailsIntersection"
    case Space.Range(_, _, _) => "Range"
    case Space.Iteration(_, _, _, _) => "Iteration"
    case Space.Fold(_, _, _, _, _, _, _) => "Fold"
    case Space.Fixpoint(_, _, _) => "Fixpoint"
    case Space.Call(_, _, _) => "Call"
    case Space.GroundedPS(_, _) => "GroundedPS"
    case Space.GroundedSS(_, _) => "GroundedSS"

  // -----------------------------------------------------------------------------------------------
  // structural surgery (own copy — this file must not depend on another suite's helpers)
  // -----------------------------------------------------------------------------------------------
  def kids(s: Space): Vector[Space] = s match
    case Space.Union(a, b) => Vector(a, b)
    case Space.Intersection(a, b) => Vector(a, b)
    case Space.Subtraction(a, b) => Vector(a, b)
    case Space.Restriction(a, b) => Vector(a, b)
    case Space.Raffination(a, b) => Vector(a, b)
    case Space.Composition(a, b) => Vector(a, b)
    case Space.Wrap(a, _) => Vector(a)
    case Space.Unwrap(a, _) => Vector(a)
    case Space.TailsUnion(a) => Vector(a)
    case Space.TailsIntersection(a) => Vector(a)
    case Space.Range(a, _, _) => Vector(a)
    case Space.Iteration(a, _, _, b) => Vector(a, b)
    case Space.Fixpoint(a, _, b) => Vector(a, b)
    case Space.Fold(a, _, _, _, _, b, _) => Vector(a, b)
    case Space.Call(_, _, ms) => ms
    case Space.GroundedSS(a, _) => Vector(a)
    case _ => Vector.empty

  def withKids(s: Space, k: Vector[Space]): Space = s match
    case Space.Union(_, _) => Space.Union(k(0), k(1))
    case Space.Intersection(_, _) => Space.Intersection(k(0), k(1))
    case Space.Subtraction(_, _) => Space.Subtraction(k(0), k(1))
    case Space.Restriction(_, _) => Space.Restriction(k(0), k(1))
    case Space.Raffination(_, _) => Space.Raffination(k(0), k(1))
    case Space.Composition(_, _) => Space.Composition(k(0), k(1))
    case Space.Wrap(_, p) => Space.Wrap(k(0), p)
    case Space.Unwrap(_, p) => Space.Unwrap(k(0), p)
    case Space.TailsUnion(_) => Space.TailsUnion(k(0))
    case Space.TailsIntersection(_) => Space.TailsIntersection(k(0))
    case Space.Range(_, a, b) => Space.Range(k(0), a, b)
    case Space.Iteration(_, y, r, _) => Space.Iteration(k(0), y, r, k(1))
    case Space.Fixpoint(_, r, _) => Space.Fixpoint(k(0), r, k(1))
    case Space.Fold(_, i, a, y, r, _, u) => Space.Fold(k(0), i, a, y, r, k(1), u)
    case Space.Call(r, rs, _) => Space.Call(r, rs, k)
    case Space.GroundedSS(_, f) => Space.GroundedSS(k(0), f)
    case _ => s

  def nodes(s: Space): Int = 1 + kids(s).map(nodes).sum
  def countOps(s: Space, into: collection.mutable.Map[String, Long]): Unit =
    into(opName(s)) = into.getOrElse(opName(s), 0L) + 1
    kids(s).foreach(k => countOps(k, into))

  // -----------------------------------------------------------------------------------------------
  // the abstraction recipes: how a concrete input value becomes a DECLARED input type
  // -----------------------------------------------------------------------------------------------
  enum Abs:
    case Exact, WeakShape, TopAll, TopShape, TopLens, OpenHeads
    case LubWith(other: SpaceValue)
    def tag: String = this match
      case Abs.LubWith(o) => "LubWith" + showSV(o)
      case x => x.toString

  def declared(v: SpaceValue, a: Abs): SpatialType = a match
    case Abs.Exact => SpatialType.of(v)
    case Abs.WeakShape => SpatialType(Shape.weaken(Shape.of(v)), SpaceType.of(v))
    case Abs.TopAll => SpatialType.top
    case Abs.TopShape => SpatialType(Shape.top, SpaceType.of(v))
    case Abs.TopLens => SpatialType(Shape.of(v), SpaceType.unknown)
    case Abs.OpenHeads => SpatialType(Shape.widenShape(Shape.of(v)), SpaceType.of(v))
    case Abs.LubWith(o) => SpatialGamma.lub(SpatialType.of(v), SpatialType.of(o))

  // -----------------------------------------------------------------------------------------------
  // the interprocedural fixtures
  // -----------------------------------------------------------------------------------------------
  val f0: RoutinePtr = RoutinePtr("hunt$f0")
  val f1: RoutinePtr = RoutinePtr("hunt$f1")
  /** a routine whose PARAMETERS SHADOW the caller's free mentions — if the interprocedural transfer
   *  leaked the caller's declared type instead of binding the argument's, this is what shows it */
  val f2: RoutinePtr = RoutinePtr("hunt$f2")
  val cRef: PathRef = PathRef("q$0")
  val cMentions: Vector[SpaceMention] = Vector(SpaceMention("m$0"), SpaceMention("m$1"))
  val shadowMentions: Vector[SpaceMention] = Vector(SpaceMention("s0"), SpaceMention("s1"))

  /** A RECURSIVE routine in the union-saturating idiom `r(m) = m ∪ r(next(m))`.  The reference
   *  `eval` only terminates on this shape when the recursive call's argument EXPRESSIONS are
   *  syntactically the ones at the call site (MORKL.scala's `Call` arm), so both the routine's
   *  parameter and the call site are pinned to `s0` and `TailsUnion($s0)`.  `next = TailsUnion`
   *  strictly shortens, so the concrete recursion bottoms out at ∅. */
  val recPtr: RoutinePtr = RoutinePtr("hunt$rec")
  private val recArg: Space = Space.TailsUnion(Space.Mention(SpaceMention("s0")))
  val recRoutine: Routine = Routine(recPtr, Vector.empty, Vector(SpaceMention("s0")),
    Space.Union(Space.Mention(SpaceMention("s0")), Space.Call(recPtr, Vector.empty, Vector(recArg))))
  val recCall: Space = Space.Call(recPtr, Vector.empty, Vector(recArg))

  val gPS: PathValue => SpaceValue =
    pv => SpaceValue(pv.items.indices.map(i => PathValue(pv.items.take(i + 1))).toSet)
  val gSS: SpaceValue => SpaceValue = sv => SpaceValue(sv.paths.map(x => PathValue(x.items.reverse)))

  // -----------------------------------------------------------------------------------------------
  // the concrete generators
  // -----------------------------------------------------------------------------------------------
  def randPath(rng: java.util.Random, alpha: Vector[PathItem], maxLen: Int): PathValue =
    PathValue(List.fill(rng.nextInt(maxLen + 1))(alpha(rng.nextInt(alpha.length))))

  def randSV(rng: java.util.Random, alpha: Vector[PathItem], maxPaths: Int, maxLen: Int,
             epsBias: Boolean = false): SpaceValue =
    val n = rng.nextInt(maxPaths + 1)
    val base = (0 until n).map(_ => randPath(rng, alpha, maxLen)).toSet
    SpaceValue(if epsBias && rng.nextInt(3) == 0 then base + PathValue(Nil) else base)

  def randAbs(rng: java.util.Random, alpha: Vector[PathItem], maxPaths: Int, maxLen: Int): Abs =
    rng.nextInt(12) match
      case 0 | 1 | 2 | 3 => Abs.Exact
      case 4 | 5 => Abs.WeakShape
      case 6 => Abs.TopAll
      case 7 => Abs.TopShape
      case 8 => Abs.TopLens
      case 9 => Abs.OpenHeads
      case _ => Abs.LubWith(randSV(rng, alpha, maxPaths, maxLen))

  // -----------------------------------------------------------------------------------------------
  // the TERM generator
  // -----------------------------------------------------------------------------------------------
  final class Gen(val rng: java.util.Random, val cfg: Cfg, val table: Vector[Routine],
                  val allowRecCall: Boolean):
    private var ctr = 0
    private def fresh(pfx: String): String = { ctr += 1; pfx + "$" + ctr }

    def path(ps: Vector[Path]): Path =
      if ps.isEmpty then Path.Constant(randPath(rng, cfg.alpha, cfg.maxLen))
      else rng.nextInt(10) match
        case 0 | 1 | 2 | 3 => Path.Constant(randPath(rng, cfg.alpha, cfg.maxLen))
        case 9 => Path.Concat(ps(rng.nextInt(ps.size)), Path.Constant(randPath(rng, cfg.alpha, 1)))
        case _ => ps(rng.nextInt(ps.size))

    def leaf(ps: Vector[Path], ms: Vector[SpaceMention]): Space =
      rng.nextInt(if ms.isEmpty then 7 else 10) match
        case 0 => Space.Empty
        case 1 | 2 | 3 => Space.Literal(randSV(rng, cfg.alpha, cfg.maxPaths, cfg.maxLen, cfg.epsBias))
        case 4 | 5 | 6 => Space.Singleton(path(ps))
        case _ => Space.Mention(ms(rng.nextInt(ms.size)))

    def space(d: Int, ps: Vector[Path], ms: Vector[SpaceMention]): Space =
      if d <= 0 then leaf(ps, ms)
      else
        def sub: Space = space(d - 1, ps, ms)
        val k = rng.nextInt(if cfg.binderBias then 22 else 28)
        k match
          case 0 | 1 => leaf(ps, ms)
          case 2 => Space.Union(sub, sub)
          case 3 => Space.Intersection(sub, sub)
          case 4 => Space.Subtraction(sub, sub)
          case 5 => Space.Restriction(sub, sub)
          case 6 => Space.Raffination(sub, sub)
          case 7 => Space.Composition(sub, sub)
          case 8 => Space.Wrap(sub, path(ps))
          case 9 => Space.Unwrap(sub, path(ps))
          case 10 => Space.TailsUnion(sub)
          case 11 => Space.TailsIntersection(sub)
          case 12 => Space.Range(sub, rng.nextInt(5) - 2, rng.nextInt(5) - 2)
          case 13 => if allowRecCall then recCall else Space.Range(sub, 0, 0)
          case 14 | 15 | 16 => iteration(d, ps, ms)
          case 17 | 18 => fold(d, ps, ms)
          case 19 | 20 => fixpoint(d, ps, ms)
          case 21 => call(d, ps, ms)
          case 22 | 23 => call(d, ps, ms)
          case 24 => Space.GroundedSS(sub, gSS)
          case 25 => Space.GroundedPS(path(ps), gPS)
          case _ => leaf(ps, ms)

    /** the binder rows.  The body sees the binder's own symbol AND every enclosing one, which is
     *  the case the fixed-template bodies of the existing matrix never build. */
    private def iteration(d: Int, ps: Vector[Path], ms: Vector[SpaceMention]): Space =
      val sym = if rng.nextBoolean() then PathRef(fresh("y")).known(1) else PathRef(fresh("y"))
      val rest = SpaceMention(fresh("r"))
      val src = space(d - 1, ps, ms)
      val body = space(d - 1, ps :+ Path.Deref(sym), ms :+ rest)
      Space.Iteration(src, sym, rest, body)

    private def fold(d: Int, ps: Vector[Path], ms: Vector[SpaceMention]): Space =
      val sym = PathRef(fresh("y"))
      val acc = PathRef(fresh("a"))
      val rest = SpaceMention(fresh("r"))
      val src = space(d - 1, ps, ms)
      val init = path(ps)
      val body = space(d - 1, ps :+ Path.Deref(sym) :+ Path.Deref(acc), ms :+ rest)
      val upd = rng.nextInt(5) match
        case 0 => Path.Deref(sym)
        case 1 | 2 => Path.Concat(Path.Deref(acc), Path.Deref(sym))
        case 3 => Path.Deref(acc)
        case _ => Path.Constant(randPath(rng, cfg.alpha, 1))
      Space.Fold(src, init, acc, sym, rest, body, upd)

    /** Every `Fixpoint` body here is CONCRETELY CONVERGENT by construction: the reference `eval`
     *  iterates `rec := body` until the argument stabilises, so the body must be either
     *  subset-decreasing in `rec` (∩, ∖, <|, \|, Range, TailsIntersection), strictly
     *  length-decreasing (TailsUnion, Unwrap by a non-ε prefix), or idempotent (∪ with a term that
     *  does not mention `rec`).  A growing body would make `eval` diverge, which would be a bug in
     *  the GENERATOR, not a finding. */
    private def fixpoint(d: Int, ps: Vector[Path], ms: Vector[SpaceMention]): Space =
      val rec = SpaceMention(fresh("k"))
      val init = space(d - 1, ps, ms)
      val g = space(d - 1, ps, ms)
      val R = Space.Mention(rec)
      if rng.nextInt(6) == 0 then Space.Fixpoint(init, rec, Space.Union(R, g))
      else
        val core = rng.nextInt(7) match
          case 0 => R
          case 1 => Space.Intersection(R, g)
          case 2 => Space.Subtraction(R, g)
          case 3 => Space.Restriction(R, g)
          case 4 => Space.Raffination(R, g)
          case 5 => Space.Range(R, rng.nextInt(4) - 1, rng.nextInt(4) - 1)
          case _ => Space.TailsIntersection(R)
        val body = rng.nextInt(3) match
          case 0 => core
          case 1 => Space.TailsUnion(core)
          case _ => Space.Unwrap(core, path(ps))
        Space.Fixpoint(init, rec, body)

    private def call(d: Int, ps: Vector[Path], ms: Vector[SpaceMention]): Space =
      if table.isEmpty then leaf(ps, ms)
      else
        val r = table(rng.nextInt(table.size))
        Space.Call(r.name, r.refs.map(_ => path(ps)), r.mentions.map(_ => space(d - 1, ps, ms)))
  end Gen

  // -----------------------------------------------------------------------------------------------
  // a static WORK/SIZE estimate, so a randomly generated Composition chain cannot hang the gate
  // -----------------------------------------------------------------------------------------------
  private val CAP = 20000L
  private def sat(a: Long, b: Long): Long = if a >= CAP || b >= CAP then CAP else (a + b) min CAP
  private def satMul(a: Long, b: Long): Long =
    if a == 0 || b == 0 then 0 else if a >= CAP || b >= CAP then CAP else (a * b) min CAP

  def est(s: Space, sz: Map[SpaceMention, Long], tbl: Map[RoutinePtr, Routine], d: Int): Long =
    if d <= 0 then CAP
    else
      def go(x: Space): Long = est(x, sz, tbl, d - 1)
      s match
        case Space.Empty => 0L
        case Space.Literal(v) => v.paths.size.toLong
        case Space.Singleton(_) => 1L
        case Space.Mention(m) => sz.getOrElse(m, CAP)
        case Space.Union(a, b) => sat(go(a), go(b))
        case Space.Intersection(a, b) => sat(go(a), go(b))
        case Space.Subtraction(a, b) => sat(go(a), go(b))
        case Space.Restriction(a, b) => sat(go(a), go(b))
        case Space.Raffination(a, b) => sat(go(a), go(b))
        case Space.Composition(a, b) => satMul(go(a), go(b))
        case Space.Wrap(a, _) => go(a)
        case Space.Unwrap(a, _) => go(a)
        case Space.TailsUnion(a) => go(a)
        case Space.TailsIntersection(a) => go(a)
        case Space.Range(a, _, _) => go(a)
        case Space.Iteration(src, _, rest, body) =>
          val n = go(src); satMul(n, est(body, sz + (rest -> n), tbl, d - 1))
        case Space.Fold(src, _, _, _, rest, body, _) =>
          val n = go(src); satMul(n, est(body, sz + (rest -> n), tbl, d - 1))
        case Space.Fixpoint(init, rec, body) =>
          val n = satMul(go(init), 4L)
          sat(n, satMul(est(body, sz + (rec -> n), tbl, d - 1), 4L))
        case Space.Call(rp, _, mentions) =>
          if rp == recPtr then sat(satMul(mentions.map(go).foldLeft(0L)(sat), 16L), 16L)
          else tbl.get(rp) match
            case None => CAP
            case Some(r) => est(r.body, r.mentions.zip(mentions.map(go)).toMap, tbl - rp, d - 1)
        case Space.GroundedPS(_, _) => 12L
        case Space.GroundedSS(a, _) => satMul(go(a), 2L)

  // -----------------------------------------------------------------------------------------------
  // a case = a term + the environment that binds its free names, abstractly AND concretely
  // -----------------------------------------------------------------------------------------------
  final case class Case(term: Space,
                        sv: Map[SpaceMention, SpaceValue],
                        sa: Map[SpaceMention, Abs],
                        pv: Map[PathRef, PathValue],
                        known: Set[PathRef],
                        tbl: Map[RoutinePtr, Routine]):
    def routines: PartialFunction[RoutinePtr, Routine] = tbl
    def declaredEnv: Map[SpaceMention, SpatialType] =
      sv.map((m, v) => m -> declared(v, sa.getOrElse(m, Abs.Exact)))
    def env: SpatialTyping.Env =
      SpatialTyping.Env(spaces = declaredEnv, paths = pv.filter((r, _) => known(r)),
                        lenv = SpatialEnv(routines = tbl))
    def pctx: PathContext = PathContextMap(pv)
    def sctx: SpaceContext = SpaceContextMap(sv)
    def evaluated: Option[SpaceValue] =
      try Some(eval(term)(using pctx, sctx, routines)) catch case _: Throwable => None
    /** the declared inputs must contain the values they were built from, or every verdict below is
     *  vacuous.  This gates `α` and `SpatialGamma.lub`, not the transfers. */
    def envUnsound: Option[String] =
      sv.collectFirst { case (m, v) if !SpatialTyping.gammaMember(v, declared(v, sa.getOrElse(m, Abs.Exact))) =>
        s"declared input ${m.s} = ${sa.getOrElse(m, Abs.Exact).tag} does not contain ${showSV(v)} " +
          s"(declared ${declared(v, sa.getOrElse(m, Abs.Exact)).show})" }
    def weight: Int = nodes(term) + sv.values.map(_.paths.size).sum +
      sv.values.map(_.paths.toVector.map(_.items.length).sum).sum + sa.values.count(_ != Abs.Exact)

  // -----------------------------------------------------------------------------------------------
  // THE CLAIM CHECKER
  // -----------------------------------------------------------------------------------------------
  def factName(f: Fact): String = f.toString.takeWhile(_ != '(')

  /** is the proposition FALSE of `v`? */
  def factFails(f: Fact, v: SpaceValue): Boolean =
    val n = v.paths.size.toLong
    val lens = v.paths.toVector.map(_.items.length.toLong)
    val heads: Set[PathItem] = v.paths.collect { case PathValue(h :: _) => h }
    f match
      case Fact.DefinitelyEmpty => v.paths.nonEmpty
      case Fact.DefinitelyNonEmpty => v.paths.isEmpty
      case Fact.MinimumCardinality(k) => n < k || v.paths.isEmpty
      case Fact.MaximumCardinality(k) => n > k
      case Fact.AllPathsHaveAtLeast(i) => v.paths.isEmpty || lens.exists(_ < i)
      case Fact.MaximumPathLength(i) => lens.exists(_ > i)
      case Fact.ExactHeadSet(hs) => heads != hs
      case Fact.HeadSetWithin(hs) => !heads.subsetOf(hs)
      case Fact.MinimumHeadCount(k) => heads.size.toLong < k
      case Fact.MaximumHeadCount(k) => heads.size.toLong > k
      case Fact.PrefixAbsent(pre) => v.paths.exists(_.items.startsWith(pre))

  /** which of the four γ channels rejects `v`, and where in the trie.  A `None` means the shape
   *  admits the value; this is the attribution the report needs (eps / head / others / otherTail,
   *  may versus must). */
  def shapeWhy(sh: Shape, v: SpaceValue, at: List[PathItem]): Option[String] =
    val where = if at.isEmpty then "root" else at.mkString(".")
    val hasEps = v.paths.contains(PathValue(Nil))
    val groups: Map[PathItem, SpaceValue] =
      v.paths.iterator.collect { case PathValue(h :: t) => (h, PathValue(t)) }
        .toVector.groupMap(_._1)(_._2).view.mapValues(ts => SpaceValue(ts.toSet)).toMap
    val untracked = groups.keySet.diff(sh.heads.keySet)
    if sh.eps == Presence.No && hasEps then Some(s"(a) eps=No at $where but eps IS present [may leak]")
    else if sh.eps == Presence.Must && !hasEps then
      Some(s"(a) eps=Must at $where but eps is ABSENT [MUST leak]")
    else if untracked.size.toLong < sh.others.lo then
      Some(s"(c) others.lo=${sh.others.lo} at $where but only ${untracked.size} untracked heads [MUST leak]")
    else if untracked.size.toLong > sh.others.hi then
      Some(s"(c) others.hi=${sh.others.hi} at $where but ${untracked.size} untracked heads [may leak]")
    else
      val trackedBad = sh.heads.iterator.flatMap { (h, c) =>
        val tv = groups.getOrElse(h, SpaceValue(Set.empty))
        val absent = !groups.contains(h)
        shapeWhy(c, tv, at :+ h).map(w =>
          if absent && c.definitelyNonEmpty then s"(b) head $h at $where is forced present but ABSENT [MUST leak] :: $w"
          else s"(b) head $h :: $w")
      }
      if trackedBad.hasNext then Some(trackedBad.next())
      else sh.otherTail match
        case Some(ot) =>
          untracked.iterator.flatMap(h => shapeWhy(ot, groups(h), at :+ h).map(w => s"(d) otherTail under $h :: $w")).nextOption()
        case None => None

  /** every claim the type makes, and the ones that are false of `v` */
  def checkClaims(v: SpaceValue, t: SpatialType): Vector[String] =
    val out = Vector.newBuilder[String]
    val n = v.paths.size.toLong
    val byLen: Map[Long, Long] = v.paths.groupBy(_.items.length.toLong).view.mapValues(_.size.toLong).toMap
    val heads: Set[PathItem] = v.paths.collect { case PathValue(h :: _) => h }
    val headed = v.paths.count(_.items.nonEmpty).toLong
    val sz = t.size; val ln = t.len; val hc = t.headCount

    if !SpatialTyping.gammaMember(v, t) then out += "gammaMember"
    if !SpatialTyping.withinEnvelope(v, t) then out += "satisfies"
    if !SpatialGamma.gamma(t)(v) then out += "SpatialGamma.gamma"
    if n < sz.lo then out += "size.lo"
    if n > sz.hi then out += "size.hi"
    if headed < sz.loHeaded then out += "size.loHeaded"
    if v.paths.nonEmpty && ln.isEmpty then out += "len.isEmpty-but-nonempty"
    if !ln.isEmpty && v.paths.exists(_.items.length.toLong < ln.lo) then out += "len.lo"
    if !ln.isEmpty && v.paths.exists(_.items.length.toLong > ln.hi) then out += "len.hi"
    val maxL = if byLen.isEmpty then 0L else byLen.keysIterator.max
    val ls = ((0L to (maxL + 3)).toSet ++ t.lens.byLen.keySet).toVector.sorted
    for l <- ls do
      val c = byLen.getOrElse(l, 0L); val i = t.lens.at(l)
      if c < i.lo then out += s"lens.at.lo"
      if c > i.hi then out += s"lens.at.hi"
    if heads.size.toLong < hc.lo then out += "headCount.lo"
    if heads.size.toLong > hc.hi then out += "headCount.hi"
    if t.isProvablyEmpty && v.paths.nonEmpty then out += "isProvablyEmpty"
    shapeWhy(t.shape, v, Nil).foreach(w => out += ("shape " + w))
    for p <- v.paths.toVector; k <- 1 to (p.items.length min Shape.MaxDepth) do
      if !t.shape.mayHavePrefix(p.items.take(k)) then out += "mayHavePrefix (false absence proof)"
    for h <- t.shape.heads.keysIterator do
      if t.shape.mustHaveHead(h) && !heads.contains(h) then out += "mustHaveHead"
    for f <- Fact.from(t) do
      if factFails(f, v) then out += ("Fact." + factName(f))
    out.result().distinct

  enum Outcome:
    case Skipped
    case EnvBad(why: String)
    case Crashed(why: String)
    case Checked(v: SpaceValue, t: SpatialType, bad: Vector[String])

  def judge(c: Case): Outcome =
    c.envUnsound match
      case Some(w) => Outcome.EnvBad(w)
      case None => c.evaluated match
        case None => Outcome.Skipped
        case Some(v) =>
          val t = try Right(SpatialTyping.infer(c.term, c.env))
                  catch case e: Throwable => Left(e.getClass.getSimpleName + ": " + String.valueOf(e.getMessage))
          t match
            case Left(w) => Outcome.Crashed(w)
            case Right(ty) =>
              val bad = try checkClaims(v, ty)
                        catch case e: Throwable => Vector("checker crashed: " + e.getClass.getSimpleName)
              Outcome.Checked(v, ty, bad)

  def violated(c: Case): Vector[String] = judge(c) match
    case Outcome.Checked(_, _, bad) => bad
    case Outcome.Crashed(w) => Vector("CRASH " + w)
    case _ => Vector.empty

  // -----------------------------------------------------------------------------------------------
  // the delta-debugger, over (term, environment) pairs
  // -----------------------------------------------------------------------------------------------
  private def termVariants(s: Space): Vector[Space] =
    val here: Vector[Space] = kids(s) ++ Vector(Space.Empty) ++ (s match
      case Space.Literal(v) if v.paths.size > 1 => v.paths.toVector.map(x => Space.Literal(SpaceValue(Set(x))))
      case Space.Literal(v) if v.paths.exists(_.items.length > 1) =>
        v.paths.toVector.map(x => Space.Literal(SpaceValue(Set(PathValue(x.items.take(1))))))
      case _ => Vector.empty)
    val ks = kids(s)
    here ++ ks.indices.toVector.flatMap(i => termVariants(ks(i)).map(k2 => withKids(s, ks.updated(i, k2))))

  private def variants(c: Case): Vector[Case] =
    val byTerm = termVariants(c.term).map(t => c.copy(term = t))
    val byAbs = c.sa.iterator.collect { case (m, a) if a != Abs.Exact => c.copy(sa = c.sa + (m -> Abs.Exact)) }.toVector
    val byVal = c.sv.iterator.flatMap { (m, v) =>
      val drops = if v.paths.size > 0 then v.paths.toVector.map(p => c.copy(sv = c.sv + (m -> SpaceValue(v.paths - p)))) else Vector.empty
      val trims = v.paths.toVector.filter(_.items.nonEmpty).map(p =>
        c.copy(sv = c.sv + (m -> SpaceValue(v.paths - p + PathValue(p.items.init)))))
      drops ++ trims
    }.toVector
    byTerm ++ byAbs ++ byVal

  /** greedy delta-debugging: keep any strictly smaller (term, env) pair that still violates */
  def shrink(c0: Case): Case =
    var cur = c0
    var going = true
    var steps = 0
    while going && steps < 300 do
      going = false; steps += 1
      variants(cur).filter(x => x.weight < cur.weight).sortBy(_.weight)
        .find(x => violated(x).nonEmpty) match
        case Some(x) => cur = x; going = true
        case None => ()
    cur

  def describe(c: Case): String =
    val used = c.sv.keys.filter(m => mentions(c.term).contains(m)).toVector.sortBy(_.s)
    val usedP = c.pv.keys.filter(r => refs(c.term).contains(r)).toVector.sortBy(_.s)
    val sb = new StringBuilder
    sb ++= "term  : " + pp(c.term) + "\n"
    for m <- used do
      sb ++= s"  env $$${m.s} = ${showSV(c.sv(m))}  declared[${c.sa.getOrElse(m, Abs.Exact).tag}] = " +
        s"${declared(c.sv(m), c.sa.getOrElse(m, Abs.Exact)).show}\n"
    for r <- usedP do
      sb ++= s"  ref ?${r.s} = \"${c.pv(r).items.mkString(".")}\"" +
        (if c.known(r) then " (value declared)" else " (value NOT declared)") + "\n"
    for (p, r) <- c.tbl.toVector.sortBy(_._1.s) if calls(c.term).contains(p) do
      sb ++= s"  routine ${p.s}(${r.refs.map(_.s).mkString(",")};${r.mentions.map(_.s).mkString(",")}) = ${pp(r.body)}\n"
    c.evaluated match
      case Some(v) =>
        val t = try SpatialTyping.infer(c.term, c.env) catch case _: Throwable => SpatialType.top
        sb ++= s"  eval  = ${showSV(v)}\n"
        sb ++= s"  typed = ${t.show}\n"
        sb ++= s"  size=${t.size}  len=${t.len}  headCount=${t.headCount.show}\n"
        sb ++= s"  facts = ${Fact.from(t).map(_.show).mkString(", ")}\n"
        sb ++= s"  FAILS : ${violated(c).mkString(" | ")}\n"
      case None => sb ++= "  eval  = <threw>\n"
    sb.result()

  def mentions(s: Space): Set[SpaceMention] =
    val here: Set[SpaceMention] = s match
      case Space.Mention(m) => Set(m)
      case _ => Set.empty
    kids(s).foldLeft(here)((a, k) => a ++ mentions(k))
  def refs(s: Space): Set[PathRef] =
    def inP(p: Path): Set[PathRef] = p match
      case Path.Deref(r) => Set(r)
      case Path.Concat(a, b) => inP(a) ++ inP(b)
      case Path.GroundedPP(a, _) => inP(a)
      case Path.GroundedSP(x, _) => refs(x)
      case _ => Set.empty
    val here: Set[PathRef] = s match
      case Space.Singleton(p) => inP(p)
      case Space.Wrap(_, p) => inP(p)
      case Space.Unwrap(_, p) => inP(p)
      case Space.GroundedPS(p, _) => inP(p)
      case Space.Fold(_, i, _, _, _, _, u) => inP(i) ++ inP(u)
      case Space.Call(_, rs, _) => rs.flatMap(inP).toSet
      case _ => Set.empty
    kids(s).foldLeft(here)((a, k) => a ++ refs(k))
  def calls(s: Space): Set[RoutinePtr] =
    val here: Set[RoutinePtr] = s match
      case Space.Call(r, _, _) => Set(r)
      case _ => Set.empty
    kids(s).foldLeft(here)((a, k) => a ++ calls(k))

  // -----------------------------------------------------------------------------------------------
  // the sweep
  // -----------------------------------------------------------------------------------------------
  final case class Cfg(alpha: Vector[PathItem], maxPaths: Int, maxLen: Int, depth: Int,
                       exactEnv: Boolean, hints: Boolean, recCall: Boolean,
                       binderBias: Boolean = false, epsBias: Boolean = false)

  final case class Result(cases: Long, skipped: Long, crashes: Long, envBad: Long,
                          bad: Map[String, (Long, Case)],
                          envBadWitness: Option[String],
                          ops: Map[String, Long], cover: Map[String, Long]):
    def violations: Int = bad.values.map(_._1).sum.toInt
    /** every stored witness delta-debugged, then grouped by the MINIMAL WITNESS it reduces to —
     *  one entry per distinct root cause, not one per broken claim (a single unsound transfer breaks
     *  a dozen claims at once and would otherwise be reported a dozen times) */
    lazy val minimal: Vector[(String, Vector[String], Long, Case)] =
      val rows = bad.toVector.map((k, v) => (k, v._1, shrink(v._2)))
      rows.groupBy((_, _, c) => pp(c.term) + " ||| " +
                     c.sa.toVector.sortBy(_._1.s).map((m, a) => m.s + "=" + a.tag).mkString(","))
        .toVector.map { (sig, rs) => (sig, rs.map(_._1).distinct.sorted, rs.map(_._2).sum, rs.head._3) }
        .sortBy(-_._3)
    def firstWitness: String =
      if bad.isEmpty then "" else
        val (_, ks, n, c) = minimal.head
        s"${ks.mkString(", ")} (x$n): " + describe(c)
    def render(name: String): String =
      val sb = new StringBuilder
      sb ++= f"\n=== $name%-24s cases=$cases%7d  skipped=$skipped%7d  analysis-crashes=$crashes%4d  " +
        f"unsound-declared-inputs=$envBad%4d  broken-claim-keys=${bad.size}%3d  MINIMAL WITNESSES=${if bad.isEmpty then 0 else minimal.size}%d\n"
      sb ++= "    ops generated : " + ops.toVector.sortBy(-_._2).map((k, v) => s"$k=$v").mkString(" ") + "\n"
      sb ++= "    coverage      : " + cover.toVector.sortBy(_._1).map((k, v) => s"$k=$v").mkString("  ") + "\n"
      envBadWitness.foreach(w => sb ++= "    UNSOUND DECLARED INPUT: " + w + "\n")
      for (_, ks, n, c) <- minimal do
        sb ++= s"    *** MINIMAL WITNESS (x$n raw cases) broken claims: ${ks.mkString(", ")}\n"
        sb ++= describe(c).linesIterator.map("        " + _).mkString("\n") + "\n"
      sb.result()

  private def routineTable(rng: java.util.Random, cfg: Cfg): Map[RoutinePtr, Routine] =
    val g0 = new Gen(rng, cfg, Vector.empty, false)
    val b0 = g0.space(2, Vector(Path.Deref(cRef)), cMentions)
    val r0 = Routine(f0, Vector(cRef), cMentions, b0)
    val g1 = new Gen(rng, cfg, Vector(r0), false)
    val b1 = g1.space(2, Vector(Path.Deref(cRef)), cMentions)
    val r1 = Routine(f1, Vector(cRef), cMentions, b1)
    val g2 = new Gen(rng, cfg, Vector(r0), false)
    val b2 = g2.space(2, Vector(Path.Deref(cRef)), shadowMentions)
    val r2 = Routine(f2, Vector(cRef), shadowMentions, b2)
    Map(f0 -> r0, f1 -> r1, f2 -> r2, recPtr -> recRoutine)

  def trial(rng: java.util.Random, cfg: Cfg): Option[Case] =
    val sv = sNames.map(m => m -> randSV(rng, cfg.alpha, cfg.maxPaths, cfg.maxLen, cfg.epsBias)).toMap
    val sa = sNames.map(m => m -> (if cfg.exactEnv then Abs.Exact
                                   else randAbs(rng, cfg.alpha, cfg.maxPaths, cfg.maxLen))).toMap
    val pv = pNames.map(r => r -> randPath(rng, cfg.alpha, cfg.maxLen)).toMap
    // mode 0 = the abstract env knows the ref's VALUE; 1 = only its length (a trusted annotation);
    // 2 = nothing at all (the `oneUnknownPath`/`wrapUnknown`/`unwrapUnknown` arms)
    val modes = pNames.map(r => r -> (if !cfg.hints then 0 else rng.nextInt(3))).toMap
    val exprs: Vector[Path] = pNames.map(r =>
      if modes(r) == 1 then Path.Deref(r.known(pv(r).items.length)) else Path.Deref(r))
    val known = pNames.filter(r => modes(r) == 0).toSet
    val tbl = routineTable(rng, cfg)
    val g = new Gen(rng, cfg, Vector(tbl(f0), tbl(f1), tbl(f2)), cfg.recCall)
    val term = g.space(cfg.depth, exprs, sNames)
    val szs = sv.view.mapValues(_.paths.size.toLong).toMap
    if est(term, szs, tbl, 14) >= 4000L then None
    else Some(Case(term, sv, sa, pv, known, tbl))

  def sweep(seed: Long, n: Int, cfg: Cfg): Result =
    val rng = new java.util.Random(seed)
    var cases = 0L; var skipped = 0L; var crashes = 0L; var envBad = 0L
    var envBadW: Option[String] = None
    val bad = collection.mutable.Map.empty[String, (Long, Case)]
    val ops = collection.mutable.Map.empty[String, Long]
    val cover = collection.mutable.Map.empty[String, Long]
    def bump(k: String): Unit = cover(k) = cover.getOrElse(k, 0L) + 1
    val deadline = System.nanoTime() + budgetNanos
    var i = 0
    while i < n && System.nanoTime() < deadline do
      i += 1
      trial(rng, cfg) match
        case None => skipped += 1
        case Some(c) =>
          countOps(c.term, ops)
          judge(c) match
            case Outcome.Skipped => skipped += 1
            case Outcome.EnvBad(w) => envBad += 1; if envBadW.isEmpty then envBadW = Some(w)
            case Outcome.Crashed(w) =>
              crashes += 1
              val k = "CRASH " + w.take(60)
              bad(k) = bad.get(k).map((m, x) => (m + 1, x)).getOrElse((1L, c))
            case Outcome.Checked(v, t, errs) =>
              cases += 1
              if t.shape.isTop then bump("shapeTop")
              if t.shape.headsClosed then bump("headsClosed")
              if t.isProvablyEmpty then bump("provablyEmpty")
              if t.size.hi != Ivl.INF then bump("sizeBounded")
              if t.headCount.lo == t.headCount.hi then bump("headCountExact")
              if t.headCount.lo >= 1 then bump("headCountPositive")
              if t.shape.eps == Presence.Must then bump("epsMust")
              if t.shape.eps == Presence.No then bump("epsNo")
              if t.shape.others.lo >= 1 then bump("othersLoPositive")
              if t.shape.otherTail.nonEmpty then bump("otherTailPresent")
              if t.shape.heads.exists((_, ch) => ch.definitelyNonEmpty) then bump("mustHead")
              if v.paths.nonEmpty then bump("nonEmptyValue")
              if v.paths.exists(_.items.length > Shape.MaxDepth) then bump("pastMaxDepth")
              if v.paths.collect { case PathValue(h :: _) => h }.size > Shape.MaxHeads then bump("pastMaxHeads")
              bump("facts=" + (Fact.from(t).size min 9))
              for e <- errs do
                val k = e + " @" + opName(c.term)
                bad(k) = bad.get(k).map((m, x) => (m + 1, if x.weight <= c.weight then x else c)).getOrElse((1L, c))
    Result(cases, skipped, crashes, envBad, bad.toMap, envBadW, ops.toMap, cover.toMap)

  // ===============================================================================================
  // THE PER-TRANSFER γ-SIMULATION MATRIX
  //
  // The term-level hunts above can only reach the abstract inputs the analysis itself builds.  This
  // matrix attacks the `Shape` algebra directly: it carries an INVARIANT-PAIRED (shape, value) —
  // `Shape.contains(sh, v)` holds by construction at every step — applies one transfer abstractly
  // and the corresponding set operation concretely, and checks that the result still pairs.  That
  // is exactly `γ(a op# b) ⊇ γ(a) op γ(b)` restricted to the two witnesses, and it is where the
  // must/may leaks in this domain's history live.
  // ===============================================================================================
  final case class AV(sh: Shape, v: SpaceValue)

  // the concrete operations, mirroring `eval` (gated against it by `groundTruthCheck`)
  def cUnion(a: SpaceValue, b: SpaceValue): SpaceValue = SpaceValue(a.paths union b.paths)
  def cInter(a: SpaceValue, b: SpaceValue): SpaceValue = SpaceValue(a.paths intersect b.paths)
  def cSub(a: SpaceValue, b: SpaceValue): SpaceValue = SpaceValue(a.paths removedAll b.paths)
  def cRestrict(a: SpaceValue, b: SpaceValue): SpaceValue =
    SpaceValue(a.paths.filter(x => b.paths.exists(p => x.items.startsWith(p.items))))
  def cRaff(a: SpaceValue, b: SpaceValue): SpaceValue = cSub(a, cRestrict(a, b))
  def cComp(a: SpaceValue, b: SpaceValue): SpaceValue =
    SpaceValue(for x <- a.paths; y <- b.paths yield PathValue(x.items ++ y.items))
  def cWrap(items: List[PathItem], a: SpaceValue): SpaceValue =
    SpaceValue(a.paths.map(x => PathValue(items ++ x.items)))
  def cUnwrap(items: List[PathItem], a: SpaceValue): SpaceValue =
    SpaceValue(a.paths.collect { case x if x.items.startsWith(items) => PathValue(x.items.drop(items.length)) })
  def cTailsU(a: SpaceValue): SpaceValue =
    SpaceValue(a.paths.collect { case PathValue(_ :: t) => PathValue(t) })
  def cTailsI(a: SpaceValue): SpaceValue =
    val gs = a.paths.collect { case PathValue(h :: t) => h -> PathValue(t) }.groupMap(_._1)(_._2)
    if gs.isEmpty then SpaceValue(Set.empty) else SpaceValue(gs.valuesIterator.map(_.toSet).reduce(_ intersect _))

  /** the hunter's concrete operations against the reference `eval` — if these disagree, nothing
   *  below means anything */
  def groundTruthCheck(seed: Long, n: Int): Vector[String] =
    val rng = new java.util.Random(seed)
    val out = Vector.newBuilder[String]
    for _ <- 0 until n do
      val u = randSV(rng, A3, 4, 3, epsBias = true)
      val w = randSV(rng, A3, 4, 3, epsBias = true)
      val is = randPath(rng, A3, 2).items
      val L = (x: SpaceValue) => Space.Literal(x)
      def chk(name: String, mine: SpaceValue, term: Space): Unit =
        val ref = eval(term)
        if mine != ref then out += s"$name: mine ${showSV(mine)} vs eval ${showSV(ref)} on ${showSV(u)} / ${showSV(w)}"
      chk("union", cUnion(u, w), Space.Union(L(u), L(w)))
      chk("inter", cInter(u, w), Space.Intersection(L(u), L(w)))
      chk("sub", cSub(u, w), Space.Subtraction(L(u), L(w)))
      chk("restrict", cRestrict(u, w), Space.Restriction(L(u), L(w)))
      chk("raffination", cRaff(u, w), Space.Raffination(L(u), L(w)))
      chk("comp", cComp(u, w), Space.Composition(L(u), L(w)))
      chk("wrap", cWrap(is, u), Space.Wrap(L(u), Path.Constant(PathValue(is))))
      chk("unwrap", cUnwrap(is, u), Space.Unwrap(L(u), Path.Constant(PathValue(is))))
      chk("tailsUnion", cTailsU(u), Space.TailsUnion(L(u)))
      chk("tailsInter", cTailsI(u), Space.TailsIntersection(L(u)))
    out.result().distinct

  /** a base (shape, value) pair.  The shape is an α of the value put through one of the domain's
   *  own loosening operators, so it respects the representation invariants that every transfer
   *  relies on — including the WIDE case, where `mk`'s width spill is the only source of a
   *  must-carrying `others.lo` and a real `otherTail`. */
  def baseAV(rng: java.util.Random, cfg: Cfg): AV =
    val v = randSV(rng, cfg.alpha, cfg.maxPaths, cfg.maxLen, epsBias = true)
    val w = randSV(rng, cfg.alpha, cfg.maxPaths, cfg.maxLen, epsBias = true)
    rng.nextInt(10) match
      case 0 | 1 | 2 | 3 => AV(Shape.of(v), v)
      case 4 => AV(Shape.weaken(Shape.of(v)), v)
      case 5 => AV(Shape.widenShape(Shape.of(v)), v)
      case 6 => AV(Shape.openCounts(Shape.of(v)), v)
      case 7 => AV(Shape.capDepth(Shape.of(v), rng.nextInt(Shape.MaxDepth + 1)), v)
      case 8 => AV(SpatialGamma.lubShape(Shape.of(v), Shape.of(w)), v)
      case _ => AV(Shape.top, v)

  /** a length interval that DOES contain `k` — the annotation the unknown-path arms are entitled to
   *  trust (docs/design_spatial_lattice.md §0) */
  private def randLen(rng: java.util.Random, k: Int): LenBounds =
    rng.nextInt(5) match
      case 0 => LenBounds(k, k)
      case 1 => LenBounds(0 max (k - 1), k + 1)
      case 2 => LenBounds(0, k + 2)
      case 3 => LenBounds(k, k + 3)
      case _ => LenBounds(0 max (k - 1), LenBounds.INF)

  /** one transfer application: the operator's name, the (abstract, concrete) result, and a rendering
   *  of the OTHER inputs, so a witness is reproducible from the printout alone */
  final case class Step(op: String, res: AV, extra: String)

  /** one abstract transfer plus the matching concrete operation */
  def step(rng: java.util.Random, cfg: Cfg, a: AV, b: => AV): Step =
    def items: List[PathItem] = randPath(rng, cfg.alpha, 2).items
    def rhs(y: AV): String = s"rhs ${y.sh.show} ∋ ${showSV(y.v)}"
    rng.nextInt(18) match
      case 0 => val y = b; Step("union", AV(Shape.union(a.sh, y.sh), cUnion(a.v, y.v)), rhs(y))
      case 1 => val y = b; Step("inter", AV(Shape.inter(a.sh, y.sh), cInter(a.v, y.v)), rhs(y))
      case 2 => val y = b; Step("sub", AV(Shape.sub(a.sh, y.sh), cSub(a.v, y.v)), rhs(y))
      case 3 => val y = b; Step("restrict", AV(Shape.restrict(a.sh, y.sh), cRestrict(a.v, y.v)), rhs(y))
      case 4 =>
        val y = b
        Step("raffination", AV(Shape.sub(a.sh, Shape.restrict(a.sh, y.sh)), cRaff(a.v, y.v)), rhs(y))
      case 5 => val y = b; Step("comp", AV(Shape.comp(a.sh, y.sh), cComp(a.v, y.v)), rhs(y))
      case 6 => val is = items; Step("wrap", AV(Shape.wrap(is, a.sh), cWrap(is, a.v)), s"p=${is.mkString(".")}")
      case 7 => val is = items; Step("unwrap", AV(Shape.unwrap(is, a.sh), cUnwrap(is, a.v)), s"p=${is.mkString(".")}")
      case 8 => Step("tailsUnion", AV(Shape.tailsUnion(a.sh), cTailsU(a.v)), "")
      case 9 => Step("tailsInter", AV(Shape.tailsInter(a.sh), cTailsI(a.v)), "")
      case 10 => Step("weaken", AV(Shape.weaken(a.sh), a.v), "")
      case 11 => Step("openCounts", AV(Shape.openCounts(a.sh), a.v), "")
      case 12 => Step("widenShape", AV(Shape.widenShape(a.sh), a.v), "")
      case 13 =>
        val d = rng.nextInt(Shape.MaxDepth + 1)
        Step("capDepth", AV(Shape.capDepth(a.sh, d), a.v), s"d=$d")
      case 14 =>
        val is = items; val k = randLen(rng, is.length)
        Step("wrapUnknown", AV(Shape.wrapUnknown(k, a.sh), cWrap(is, a.v)), s"p=${is.mkString(".")} k=$k")
      case 15 =>
        val is = items; val k = randLen(rng, is.length)
        Step("unwrapUnknown", AV(Shape.unwrapUnknown(k, a.sh), cUnwrap(is, a.v)), s"p=${is.mkString(".")} k=$k")
      case 16 =>
        val is = items; val k = randLen(rng, is.length)
        Step("oneUnknownPath", AV(Shape.oneUnknownPath(k), SpaceValue(Set(PathValue(is)))), s"p=${is.mkString(".")} k=$k")
      case _ =>
        // a positional slice with a width that IS an upper bound on what it keeps (the width the
        // analysis derives statically is exercised by the term-level hunts)
        val (lo, hi) = (rng.nextInt(5) - 2, rng.nextInt(5) - 2)
        val kept = sliceRange(a.v.paths, lo, hi)
        Step("range", AV(Shape.range(a.sh, kept.size.toLong, false), SpaceValue(kept)),
             s"window($lo,$hi) width=${kept.size}")

  /** the representation invariants every transfer in SpatialShape.scala relies on */
  def invariantWhy(sh: Shape, d: Int = 0): Option[String] =
    if d > 8 then None
    else if sh.others.lo < 0 || sh.others.hi < 0 then Some("others has a negative endpoint")
    else if sh.others.lo > sh.others.hi then Some("others.lo > others.hi")
    else if sh.heads.size > Shape.MaxHeads then Some(s"${sh.heads.size} > MaxHeads tracked heads")
    else if sh.depth > Shape.MaxDepth then Some(s"depth ${sh.depth} > MaxDepth")
    else if sh.others.hi == 0 && sh.otherTail.nonEmpty then Some("closed head set but otherTail present")
    else if sh.otherTail.exists(t => t.eps == Presence.Must || t.others.lo > 0) then
      Some("otherTail carries a MUST claim (mk establishes may-only)")
    else sh.heads.iterator.flatMap((h, c) => invariantWhy(c, d + 1).map(w => s"under $h: $w")).nextOption()
      .orElse(sh.otherTail.flatMap(t => invariantWhy(t, d + 1).map(w => s"in otherTail: $w")))

  final case class LawResult(cases: Long, runs: Map[String, Long], bad: Map[String, (Long, String)],
                             notes: Map[String, Long]):
    def violations: Int = bad.values.map(_._1).sum.toInt
    def firstWitness: String =
      if bad.isEmpty then "" else { val (k, (n, w)) = bad.toVector.sortBy(-_._2._1).head; s"$k ($n): $w" }
    def render(name: String): String =
      val sb = new StringBuilder
      sb ++= f"\n=== $name%-24s checks=$cases%8d  DISTINCT VIOLATIONS=${bad.size}%d\n"
      sb ++= "    per-operator  : " + runs.toVector.sortBy(_._1).map((k, v) => s"$k=$v").mkString(" ") + "\n"
      if notes.nonEmpty then
        sb ++= "    notes         : " + notes.toVector.sortBy(_._1).map((k, v) => s"$k=$v").mkString("  ") + "\n"
      for (k, (n, w)) <- bad.toVector.sortBy(-_._2._1) do
        sb ++= s"    *** VIOLATION [$k] x$n\n        $w\n"
      sb.result()

  def transferMatrix(seed: Long, n: Int, depth: Int): LawResult =
    val rng = new java.util.Random(seed)
    val cfgs = Vector(Cfg(A3, 4, 3, depth, false, false, false),
                      Cfg(A2, 3, 2, depth, false, false, false, epsBias = true),
                      Cfg(ABig, 20, 6, depth, false, false, false))
    val runs = collection.mutable.Map.empty[String, Long]
    val bad = collection.mutable.Map.empty[String, (Long, String)]
    val notes = collection.mutable.Map.empty[String, Long]
    def note(k: String): Unit = notes(k) = notes.getOrElse(k, 0L) + 1
    var cases = 0L
    val deadline = System.nanoTime() + budgetNanos
    var i = 0
    while i < n && System.nanoTime() < deadline do
      i += 1
      val cfg = cfgs(i % cfgs.size)
      def build(d: Int): AV =
        if d <= 0 then baseAV(rng, cfg)
        else
          val a = build(d - 1)
          val Step(op, r, extra) = step(rng, cfg, a, build(d - 1))
          runs(op) = runs.getOrElse(op, 0L) + 1
          cases += 1
          if !r.sh.headsClosed then note("openHeadSet")
          if r.sh.others.lo >= 1 then note("othersLoPositive")
          if r.sh.otherTail.nonEmpty then note("otherTailPresent")
          if r.sh.eps == Presence.Must then note("epsMust")
          if r.sh.heads.exists((_, c) => c.definitelyNonEmpty) then note("mustHead")
          if r.v.paths.exists(_.items.length > Shape.MaxDepth) then note("pastMaxDepth")
          if r.v.paths.collect { case PathValue(h :: _) => h }.size > Shape.MaxHeads then note("pastMaxHeads")
          def fail(k: String, why: String): Unit =
            val key = s"$op :: $k"
            bad(key) = bad.get(key).map((m, x) => (m + 1, x)).getOrElse((1L,
              s"$why\n          lhs      ${a.sh.show}  ∋ ${showSV(a.v)}\n" +
              (if extra.isEmpty then "" else s"          $extra\n") +
              s"          result#  ${r.sh.show}\n          concrete ${showSV(r.v)}"))
          var ok = true
          if !Shape.contains(r.sh, r.v) then
            ok = false
            fail("Shape.contains", "channel: " + shapeWhy(r.sh, r.v, Nil).getOrElse("<contains says no, shapeWhy says yes>"))
          if !SpatialGamma.gammaShape(r.sh, r.v) then
            ok = false
            fail("SpatialGamma.gammaShape", "the independent γ rejects the result")
          invariantWhy(r.sh).foreach(w => note("INVARIANT " + w.takeWhile(_ != ':')))
          // never continue a chain on a broken pair: the next step would inherit the violation and
          // be blamed for it.  ⊤ admits everything, so it restores the invariant without hiding it.
          if ok then r else AV(Shape.top, r.v)
      try build(depth) catch case _: Throwable => note("builder threw")
    LawResult(cases, runs.toMap, bad.toMap, notes.toMap)

  /** THE MAY-READING MATRIX.  `SpatialTyping.fixpoint` establishes only γ_MAY membership of the
   *  concrete iterates — it joins with `Shape.union` (the union TRANSFER, which keeps MUST from both
   *  operands and is therefore not an upper bound in γ), tests convergence with `Shape.leq` (a
   *  may-only order by its own documentation), and weakens the answer.  So every transfer applied
   *  inside that loop must be sound in the MAY reading:
   *
   *      v ∈ γ_may(a)  ∧  w ∈ γ_may(b)   ⇒   (v op w) ∈ γ_may(a op# b)
   *
   *  This matrix carries a may-only pair (obtained by DROPPING paths from a strong pair, which is
   *  exactly how a must-present head becomes absent) and reports, per operator, whether that holds.
   *  Only the pure loosening operators are asserted; the rest is measured, because the domain does
   *  not state which reading each transfer is sound for. */
  def mayMatrix(seed: Long, n: Int, depth: Int): LawResult =
    val rng = new java.util.Random(seed)
    val cfgs = Vector(Cfg(A3, 4, 3, depth, false, false, false),
                      Cfg(A2, 3, 2, depth, false, false, false, epsBias = true))
    val runs = collection.mutable.Map.empty[String, Long]
    val bad = collection.mutable.Map.empty[String, (Long, String)]
    val notes = collection.mutable.Map.empty[String, Long]
    def note(k: String): Unit = notes(k) = notes.getOrElse(k, 0L) + 1
    var cases = 0L
    val deadline = System.nanoTime() + budgetNanos
    var i = 0
    /** a pair satisfying only the MAY reading: drop a random subset of the strong pair's paths */
    def mayBase(cfg: Cfg): AV =
      val a = baseAV(rng, cfg)
      val cand = a.v.paths.filter(_ => rng.nextInt(3) != 0)
      val v2 = SpaceValue(cand)
      if SpatialGamma.gammaShapeMay(a.sh, v2) then
        if !Shape.contains(a.sh, v2) then note("genuinely-may-only pair")
        AV(a.sh, v2)
      else a
    while i < n && System.nanoTime() < deadline do
      i += 1
      val cfg = cfgs(i % cfgs.size)
      def build(d: Int): AV =
        if d <= 0 then mayBase(cfg)
        else
          val a = build(d - 1)
          val Step(op, r, extra) = step(rng, cfg, a, build(d - 1))
          runs(op) = runs.getOrElse(op, 0L) + 1
          cases += 1
          if SpatialGamma.gammaShapeMay(r.sh, r.v) then r
          else
            val key = s"$op :: not sound in the MAY reading"
            bad(key) = bad.get(key).map((m, x) => (m + 1, x)).getOrElse((1L,
              s"lhs      ${a.sh.show}  ∋may ${showSV(a.v)}\n" +
              (if extra.isEmpty then "" else s"          $extra\n") +
              s"          result#  ${r.sh.show}\n          concrete ${showSV(r.v)}  (γ_may REJECTS it)"))
            AV(Shape.top, r.v)   // do not contaminate the rest of the chain
      try build(depth) catch case _: Throwable => note("builder threw")
    LawResult(cases, runs.toMap, bad.toMap, notes.toMap)

  /** the ORDER and the WIDENINGS: `leq(a,b) ⇒ γ(a) ⊆ γ(b)`, every widening/weakening only loosens,
   *  and the lub keeps both members.  `Shape.leq` is the order `SpatialTyping.fixpoint` uses to
   *  accept a post-fixpoint, so an unsound `leq` is an unsound `Fixpoint`. */
  def orderLaws(seed: Long, n: Int): LawResult =
    val rng = new java.util.Random(seed)
    val cfgs = Vector(Cfg(A3, 4, 3, 2, false, false, false),
                      Cfg(A2, 3, 2, 2, false, false, false, epsBias = true),
                      Cfg(ABig, 20, 6, 2, false, false, false))
    val runs = collection.mutable.Map.empty[String, Long]
    val bad = collection.mutable.Map.empty[String, (Long, String)]
    val notes = collection.mutable.Map.empty[String, Long]
    def note(k: String): Unit = notes(k) = notes.getOrElse(k, 0L) + 1
    def hit(k: String): Unit = runs(k) = runs.getOrElse(k, 0L) + 1
    var cases = 0L
    val deadline = System.nanoTime() + budgetNanos
    var i = 0
    while i < n && System.nanoTime() < deadline do
      i += 1
      val cfg = cfgs(i % cfgs.size)
      def build(d: Int): AV =
        if d <= 0 then baseAV(rng, cfg)
        else
          val r = step(rng, cfg, build(d - 1), build(d - 1)).res
          // the order laws below need a well-paired (shape, value); a transfer that breaks the
          // pairing is HUNT 7's finding, not theirs
          if Shape.contains(r.sh, r.v) then r else AV(Shape.top, r.v)
      val a = build(1 + rng.nextInt(2))
      val other = build(1)
      def fail(k: String, why: String): Unit =
        bad(k) = bad.get(k).map((m, x) => (m + 1, x)).getOrElse((1L, why))
      cases += 1
      // 1. the loosening operators must keep the member
      if !Shape.contains(Shape.weaken(a.sh), a.v) then
        fail("weaken loses a member", s"${a.sh.show} ∋ ${showSV(a.v)} but weakened ${Shape.weaken(a.sh).show} does not")
      hit("weaken")
      if !Shape.contains(Shape.openCounts(a.sh), a.v) then
        fail("openCounts loses a member", s"${a.sh.show} ∋ ${showSV(a.v)} vs ${Shape.openCounts(a.sh).show}")
      hit("openCounts")
      if !Shape.contains(Shape.widenShape(a.sh), a.v) then
        fail("widenShape loses a member", s"${a.sh.show} ∋ ${showSV(a.v)} vs ${Shape.widenShape(a.sh).show}")
      hit("widenShape")
      for d <- 0 to Shape.MaxDepth do
        if !Shape.contains(Shape.capDepth(a.sh, d), a.v) then
          fail("capDepth loses a member", s"d=$d ${a.sh.show} ∋ ${showSV(a.v)} vs ${Shape.capDepth(a.sh, d).show}")
      hit("capDepth")
      // 2. the lub keeps BOTH members
      val l = SpatialGamma.lubShape(a.sh, other.sh)
      if !Shape.contains(l, a.v) || !Shape.contains(l, other.v) then
        fail("lubShape loses a member",
             s"lub(${a.sh.show}, ${other.sh.show}) = ${l.show} misses ${if !Shape.contains(l, a.v) then showSV(a.v) else showSV(other.v)}")
      hit("lubShape")
      // 3. the order, against a systematically LOOSER right-hand side (so the antecedent fires)
      val uppers = Vector(Shape.weaken(a.sh), Shape.widenShape(a.sh), Shape.openCounts(a.sh), l,
                          Shape.union(a.sh, other.sh), Shape.top, other.sh, build(1).sh)
      for u <- uppers do
        if Shape.leq(a.sh, u) then
          hit("Shape.leq-holds")
          if SpatialGamma.gammaShapeMay(a.sh, a.v) && !SpatialGamma.gammaShapeMay(u, a.v) then
            fail("Shape.leq unsound (may reading)",
                 s"leq(${a.sh.show}, ${u.show}) but ${showSV(a.v)} is in γ_may of the first, not the second")
        if SpatialGamma.leqShape(a.sh, u) then
          hit("Gamma.leqShape-holds")
          if Shape.contains(a.sh, a.v) && !Shape.contains(u, a.v) then
            fail("SpatialGamma.leqShape unsound",
                 s"leqShape(${a.sh.show}, ${u.show}) but ${showSV(a.v)} is in γ of the first, not the second")
      // 4. the union transfer is an UPPER BOUND in the may reading (what the Kleene loop assumes)
      val un = Shape.union(a.sh, other.sh)
      if !SpatialGamma.gammaShapeMay(un, a.v) then
        fail("union is not a may-upper-bound of its left operand",
             s"union(${a.sh.show}, ${other.sh.show}) = ${un.show} rejects ${showSV(a.v)}")
      hit("union-upper")
      // 5. the product-level order and lub
      val ta = SpatialType(a.sh, SpaceType.of(a.v))
      val tb = SpatialType(other.sh, SpaceType.of(other.v))
      val lt = SpatialGamma.lub(ta, tb)
      if !SpatialGamma.gamma(lt)(a.v) || !SpatialGamma.gamma(lt)(other.v) then
        fail("SpatialGamma.lub loses a member", s"lub(${ta.show}, ${tb.show}) = ${lt.show}")
      hit("lub(product)")
      if SpatialGamma.leq(ta, lt) then hit("leq(product)-holds")
      else note("leq(a, lub(a,b)) is not decided")
      if SpatialGamma.leq(ta, tb) && SpatialGamma.gamma(ta)(a.v) && !SpatialGamma.gamma(tb)(a.v) then
        fail("SpatialGamma.leq unsound", s"leq(${ta.show}, ${tb.show}) but ${showSV(a.v)} escapes the second")
    LawResult(cases, runs.toMap, bad.toMap, notes.toMap)

  // -----------------------------------------------------------------------------------------------
  // the corpus, kept OPEN: free mentions stay mentions with (possibly inexact) declared types
  // -----------------------------------------------------------------------------------------------
  lazy val corpus: Vector[FuzzRec] =
    val f = new java.io.File(Loaders.repoRoot, "corpus_1000.ser")
    if !f.exists then Vector.empty
    else
      val ois = new java.io.ObjectInputStream(new java.io.FileInputStream(f))
      try ois.readObject().asInstanceOf[Vector[FuzzRec]] finally ois.close()

  def sweepCorpus(recs: Vector[FuzzRec], seed: Long, envsPer: Int): Result =
    val rng = new java.util.Random(seed)
    val cfg = Cfg(A3, 4, 2, 3, exactEnv = false, hints = false, recCall = false)
    var cases = 0L; var skipped = 0L; var crashes = 0L; var envBad = 0L
    var envBadW: Option[String] = None
    val bad = collection.mutable.Map.empty[String, (Long, Case)]
    val ops = collection.mutable.Map.empty[String, Long]
    val cover = collection.mutable.Map.empty[String, Long]
    def bump(k: String): Unit = cover(k) = cover.getOrElse(k, 0L) + 1
    val deadline = System.nanoTime() + budgetNanos
    for r <- recs; _ <- 0 until envsPer if System.nanoTime() < deadline do
      val sv = sNames.map(m => m -> randSV(rng, A3, 4, 2)).toMap
      val sa = sNames.map(m => m -> randAbs(rng, A3, 4, 2)).toMap
      val pv = pNames.map(x => x -> randPath(rng, A3, 2)).toMap
      val c = Case(r.prog, sv, sa, pv, pNames.toSet, Map.empty)
      if est(r.prog, sv.view.mapValues(_.paths.size.toLong).toMap, Map.empty, 24) >= 4000L then skipped += 1
      else
        countOps(c.term, ops)
        judge(c) match
          case Outcome.Skipped => skipped += 1
          case Outcome.EnvBad(w) => envBad += 1; if envBadW.isEmpty then envBadW = Some(w)
          case Outcome.Crashed(w) =>
            crashes += 1
            val k = "CRASH " + w.take(60)
            bad(k) = bad.get(k).map((m, x) => (m + 1, x)).getOrElse((1L, c))
          case Outcome.Checked(v, t, errs) =>
            cases += 1
            if t.shape.isTop then bump("shapeTop")
            if t.shape.headsClosed then bump("headsClosed")
            if t.isProvablyEmpty then bump("provablyEmpty")
            if v.paths.nonEmpty then bump("nonEmptyValue")
            if t.headCount.lo >= 1 then bump("headCountPositive")
            for e <- errs do
              val k = e + " @" + opName(c.term)
              bad(k) = bad.get(k).map((m, x) => (m + 1, if x.weight <= c.weight then x else c)).getOrElse((1L, c))
    Result(cases, skipped, crashes, envBad, bad.toMap, envBadW, ops.toMap, cover.toMap)
end Hunt
