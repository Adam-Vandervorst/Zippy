package morkl

import munit.FunSuite
import scala.collection.immutable.SortedMap
import scala.util.Random

/** ==================================================================================================
 *  THE CERTIFICATE VALUE'S OWN LAWS.
 *
 *  `Cert` is a new carrier channel and the domain's own history says what that costs if it is not
 *  gated: `Shape.isTop`'s note records a key-certificate prototype that looked like ⊤ to the order's
 *  short circuit, so the order accepted a left-hand side with thirteen heads that γ rejected.  Every
 *  law here is one the lattice operations above this file assume, checked against `admits` — the one
 *  primitive the whole tier reduces to — on a finite path universe where "is this language contained
 *  in that one" is DECIDABLE rather than approximated.
 *
 *  ==WHAT IS DELIBERATELY CHECKED AGAINST A DECISION PROCEDURE==
 *  `Cert.leq` and `Cert.headsDisjoint` are sound and INCOMPLETE by design.  Testing them against
 *  themselves would prove nothing, so each is checked against the exhaustive containment on the
 *  universe: soundness is asserted (a `true` must be right) and incompleteness is MEASURED and
 *  printed rather than asserted away.
 *  ================================================================================================== */
class SpatialCertCheck extends FunSuite, CalibrationProbe:
  import Cert.Outside

  /** the finite path universe every containment law is decided on */
  val alphabet: Vector[PathItem] = Vector("a", "b", "c")
  val universe: Vector[List[PathItem]] =
    val ls = collection.mutable.ArrayBuffer(List.empty[PathItem])
    var frontier = Vector(List.empty[PathItem])
    for _ <- 1 to 3 do
      frontier = frontier.flatMap(p => alphabet.map(h => p :+ h))
      ls ++= frontier
    ls.toVector

  def lang(c: Cert): Set[List[PathItem]] = universe.filter(c.admits).toSet

  /** a random certificate over `alphabet`, up to `d` levels deep */
  def gen(r: Random, d: Int): Cert =
    if d <= 0 then r.nextInt(3) match
      case 0 => Cert.top
      case 1 => Cert.empty
      case _ => Cert.epsOnly
    else
      val keys = alphabet.filter(_ => r.nextBoolean())
      val out = r.nextInt(4) match
        case 0 => Outside.Closed
        case 1 => Outside.Unbounded
        case _ => Outside.Bounded(gen(r, d - 1))
      Cert.of(r.nextBoolean(), SortedMap.from(keys.map(_ -> gen(r, d - 1))), out)

  def sample(n: Int, d: Int = 3, seed: Int = 20260903): Vector[Cert] =
    val r = new Random(seed)
    Vector.fill(n)(gen(r, d))

  // ------------------------------------------------------------------------------------------------
  test("A. NORMALISATION: the smart constructor establishes every representation invariant") {
    // an empty child admits nothing, so tracking it would make the head set look larger than it is —
    // and `possibleHeads` reads `keys.keySet`
    val withDead = Cert.of(false, SortedMap("a" -> Cert.empty, "b" -> Cert.epsOnly), Outside.Closed)
    assertEquals(withDead.keys.keySet, Set("b"), s"a dead child must not be tracked: ${withDead.show}")
    assertEquals(withDead.headNames, Some(Set("b")))

    // `Bounded(⊤)` claims nothing below an unnamed head, which IS `Unbounded`
    assertEquals(Cert.of(true, SortedMap.empty, Outside.Bounded(Cert.top)).outside, Outside.Unbounded)
    // `Bounded(∅)` says no unnamed head can carry anything, which IS `Closed`
    assertEquals(Cert.of(true, SortedMap.empty, Outside.Bounded(Cert.empty)).outside, Outside.Closed)

    assert(Cert.top.isTop, Cert.top.show)
    assert(Cert.empty.isEmpty, Cert.empty.show)
    assert(!Cert.epsOnly.isTop && !Cert.epsOnly.isEmpty, Cert.epsOnly.show)
    assertEquals(lang(Cert.epsOnly), Set(List.empty[PathItem]))
    assertEquals(lang(Cert.empty), Set.empty[List[PathItem]])
    assertEquals(lang(Cert.top), universe.toSet)

    // `named` MUST admit ε — it is a claim about heads and ε has none.  The first draft did not, and
    // γ then rejected every value containing the empty path (see `Cert.named`'s note).
    assert(Cert.named(Set("a", "b")).admits(Nil), "named must admit the empty path")
    assertEquals(Cert.named(Set("a", "b")).headNames, Some(Set("a", "b")))
    assert(!Cert.named(Set("a")).admits(List("b")), "named must reject an unnamed head")
    assert(Cert.named(Set("a")).admits(List("a", "b", "c")), "named claims nothing below the head")

    // `path` is the sharpest single-path claim
    assertEquals(lang(Cert.path(List("a", "b"))), Set(List("a", "b")))
  }

  test("B. IDENTITY IS A VALUE: the arena is a cache and clearing it changes no answer") {
    // The property `HeadAtoms` did not have, and the reason the ids had to go: a `Shape` carrying an
    // atom id was meaningless without the process-wide table, and shapes OUTLIVE their analysis
    // (`SpatialPipeline` reads a stored `SpatialAnalysis`).
    val cs = sample(120)
    val before = cs.map(c => (c.show, lang(c), c.headNames, c.headBound, c.cardinality))
    Cert.reset()
    val after = cs.map(c => (c.show, lang(c), c.headNames, c.headBound, c.cardinality))
    assertEquals(after, before, "clearing the arena changed an answer — then it is not a cache")

    // and a certificate REBUILT from scratch after the reset equals the one built before it.  It is
    // NOT the same object, and it must not be: the reset dropped the arena, so the rebuild interns
    // fresh instances.  That is precisely the point — equality is structural, so the answers are the
    // same either way.
    val rebuilt = sample(120)
    assertEquals(rebuilt, cs, "structural equality must not depend on the arena's contents")
    for (a, b) <- cs.zip(rebuilt) do assertEquals(a.hashCode, b.hashCode, s"${a.show}")

    // INTERNING STILL DOES ITS JOB WITHIN ONE ARENA, which is the performance claim the tier makes
    // explicitly (`Cert.leq`/`join`/`meet` short-circuit on pointer equality).
    val again = sample(120)
    val hits = rebuilt.indices.count(i => again(i) eq rebuilt(i))
    println(s"CERT: ${rebuilt.size} certificates, $hits interned to the same instance within one arena")
    assert(hits >= rebuilt.size / 2,
           s"only $hits of ${rebuilt.size} shared an instance — interning is not working, and the " +
           "pointer short circuits every lattice operation relies on are then dead code")
  }

  test("C. JOIN and MEET are sound and EXACT on the language") {
    val cs = sample(60)
    var joinExact = 0; var meetExact = 0; var n = 0
    for a <- cs; b <- cs.take(20) do
      n += 1
      val la = lang(a); val lb = lang(b)
      val lj = lang(Cert.join(a, b)); val lm = lang(Cert.meet(a, b))
      // JOIN: sound (admits both) — the obligation `Shape.unionTransfer`'s certificate relies on
      assert((la union lb).subsetOf(lj),
             s"join(${a.show}, ${b.show}) drops a member of one side")
      if lj == (la union lb) then joinExact += 1
      // MEET: sound (a path both admit is admitted) — the reduced-product step
      assert((la intersect lb).subsetOf(lm),
             s"meet(${a.show}, ${b.show}) drops a path both sides admit")
      if lm == (la intersect lb) then meetExact += 1
    println(f"CERT: join exact on $joinExact/$n pairs, meet exact on $meetExact/$n " +
            f"(${100.0 * (n - meetExact) / n}%.1f%% of meets over-approximate)")
    // THE JOIN IS EXACT AND IS ASSERTED SO.  `L(A ∪ B) = L(A) ∪ L(B)` and the trie can represent
    // that union exactly, so an inexact join here would be a silent precision leak with no cause.
    assertEquals(joinExact, n, "the join must be EXACT on the language")
    // THE MEET IS SOUND AND OVER-APPROXIMATES, which is measured above rather than asserted away.
    // The cause is structural and not a defect: `Outside` is one summary for every unnamed head, so
    // a meet of two shapes that name DIFFERENT heads has to keep a single `Bounded` bound covering
    // both sides' unnamed tails, and that bound admits combinations neither operand does.  A meet is
    // used as a reduced-product step, where over-approximating is the safe direction.
    assert(meetExact >= n / 2,
           s"only $meetExact/$n meets were exact — that is far worse than the summary channel " +
           "explains, so something other than the `Outside` merge is losing precision")
  }

  test("D. leq is SOUND against exhaustive containment, and its incompleteness is measured") {
    val cs = sample(80)
    var sound = 0; var incomplete = 0; var n = 0
    for a <- cs; b <- cs.take(30) do
      n += 1
      val real = lang(a).subsetOf(lang(b))
      if Cert.leq(a, b) then
        assert(real, s"leq(${a.show}, ${b.show}) but the language is not contained")
        sound += 1
      else if real then incomplete += 1
    println(f"CERT: leq accepted $sound/$n pairs; $incomplete genuine containments not decided " +
            f"(${100.0 * incomplete / n}%.1f%% incomplete, sound on all $n)")
    assert(Cert.leq(Cert.empty, Cert.top) && Cert.leq(Cert.epsOnly, Cert.top))
    assert(!Cert.leq(Cert.top, Cert.epsOnly))
    // reflexivity, which the order's use in a widening chain needs
    for c <- cs do assert(Cert.leq(c, c), s"not reflexive at ${c.show}")
  }

  test("E. headsDisjoint is SOUND: `false` never hides a shared head") {
    val cs = sample(80)
    var decided = 0; var n = 0
    def heads(c: Cert): Set[PathItem] =
      universe.collect { case h :: _ if c.admits(h :: Nil) || c.admits(h :: List("a")) => h }.toSet
    for a <- cs; b <- cs.take(30) do
      n += 1
      if Cert.headsDisjoint(a, b) then
        decided += 1
        assertEquals(heads(a) intersect heads(b), Set.empty[PathItem],
                     s"headsDisjoint(${a.show}, ${b.show}) but they share a head")
    println(s"CERT: headsDisjoint decided $decided/$n pairs, sound on all of them")
    assert(Cert.headsDisjoint(Cert.named(Set("a")), Cert.named(Set("b"))))
    assert(!Cert.headsDisjoint(Cert.named(Set("a", "b")), Cert.named(Set("b"))))
    // ⊤ on either side is not disjoint from anything non-empty
    assert(!Cert.headsDisjoint(Cert.top, Cert.named(Set("a"))))
    // ∅ is disjoint from everything, including itself and ⊤
    assert(Cert.headsDisjoint(Cert.empty, Cert.top))
  }

  test("F. under / tailsUnion / tailsUnionExcept agree with admits") {
    val cs = sample(80)
    for c <- cs do
      for h <- alphabet do
        val u = c.under(h)
        for p <- universe if p.length <= 2 do
          assertEquals(u.admits(p), c.admits(h :: p),
                       s"under($h) disagrees with admits on ${p.mkString(".")}: ${c.show}")
      // the tails-union admits every tail of every head
      val tu = c.tailsUnion
      for h <- alphabet; p <- universe if p.length <= 2 && c.admits(h :: p) do
        assert(tu.admits(p), s"tailsUnion drops $h.${p.mkString(".")}: ${c.show}")
      // and the EXCEPT form admits every tail of every head OUTSIDE the excluded set
      for skip <- Vector(Set.empty[PathItem], Set("a"), Set("a", "b")) do
        val te = Cert.tailsUnionExcept(c, skip)
        for h <- alphabet if !skip.contains(h); p <- universe if p.length <= 2 && c.admits(h :: p) do
          assert(te.admits(p),
                 s"tailsUnionExcept($skip) drops $h.${p.mkString(".")}: ${c.show}")
  }

  test("G. widen only WEAKENS, and records exactly what it did") {
    val cs = sample(120, d = 4)
    for c <- cs; (md, mk) <- Vector((1, 1), (2, 2), (3, 1), (2, 0), (0, 2)) do
      val w = Cert.widen(c, md, mk)
      // every path the original admits, the widened one admits: the whole soundness obligation
      for p <- universe if c.admits(p) do
        assert(w.admits(p), s"widen(${c.show}, $md, $mk) = ${w.show} dropped ${p.mkString(".")}")
      // the result is inside the budgets it was widened to
      assert(Cert.withinBudget(w, md, mk),
             s"widen(${c.show}, $md, $mk) = ${w.show} is still outside its own budget")
      // and a degradation is RECORDED whenever the input was outside the budgets — the rule that
      // fired is named on the value, which is what `1C.5` asks for
      if !Cert.withinBudget(c, md, mk) then
        assert(w.degradationsBelow.nonEmpty,
               s"widen brought ${c.show} inside ($md,$mk) as ${w.show} and recorded no degradation")
      // …and NOT recorded when nothing fired
      if Cert.withinBudget(c, md, mk) && c.degradationsBelow.isEmpty then
        assertEquals(w.degradationsBelow, Set.empty[Cert.Degradation],
                     s"widen invented a degradation on ${c.show} at ($md,$mk)")
    // and widening something already inside the budgets is the identity, record included
    val small = Cert.named(Set("a", "b"))
    assertEquals(Cert.widen(small, 4, 4), small)
    assertEquals(small.degradationsBelow, Set.empty[Cert.Degradation])
  }

  test("H. cardinality and headBound are UPPER bounds on the real thing") {
    for c <- sample(120) do
      val l = lang(c)
      // `cardinality` bounds the language ONLY when the language is finite in the universe; the
      // universe is a truncation, so the check is one-directional and that is the claim.
      if c.cardinality < Ivl.INF then
        assert(l.size <= c.cardinality,
               s"cardinality ${c.cardinality} under-counts ${l.size}: ${c.show}")
      val hs = l.collect { case h :: _ => h }
      if c.headBound < Ivl.INF then
        assert(hs.size <= c.headBound, s"headBound ${c.headBound} under-counts ${hs.size}: ${c.show}")
      assertEquals(c.headNames.isDefined, c.headsNamed)
      for ks <- c.headNames do
        assertEquals(hs.diff(ks), Set.empty[PathItem], s"a head outside the names: ${c.show}")
  }
end SpatialCertCheck
