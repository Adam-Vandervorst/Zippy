package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** SPATIAL TYPES ([[SpatialTypes]]) — the length-indexed count abstraction that unifies the size
 *  and path-length analyses.  Gates:
 *   1. the per-length counts are SOUND on random programs (and on the guiding examples);
 *   2. the SIZE projection falls within the z3 space-size bounds ([[SizeZ3]]);
 *   3. the LENGTH projection falls within the z3 path-length bounds ([[LenZ3]]);
 *   4. the `s || g` control-flow derivation and the input→output spatial type come out exactly. */
class SpatialTypeCheck extends FunSuite:
  import Space.*
  import Lower.{LenBounds, SizeBounds}
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  def pathOf(n: Int, item: String = "a"): PathValue = PathValue(List.fill(n)(item))
  def lit(ps: PathValue*): Space = Space.Literal(SpaceValue(ps.toSet))
  /** ground truth: the per-length histogram of a space's value */
  def histogram(v: SpaceValue): Map[Long, Long] =
    v.paths.groupBy(_.items.length.toLong).view.mapValues(_.size.toLong).toMap

  /** every length class of the concrete value must sit inside the abstract interval */
  def checkSound(s: Space, t: SpaceType, name: String)(using pc: PathContext = PathContextMap(Map.empty),
                                                       sc: SpaceContext = SpaceContextMap(Map.empty)): Unit =
    val h = histogram(eval(s))
    for (l, n) <- h do
      val c = t.at(l)
      assert(c.lo <= n && n <= c.hi, s"$name: $n paths of length $l outside ${c.show} — type ${t.show} for ${s.show}")
    for l <- t.byLen.keys do
      val n = h.getOrElse(l, 0L)
      assert(t.at(l).lo <= n, s"$name: claimed ≥${t.at(l).lo} paths of length $l but found $n — ${t.show}")

  // ---- the input→output spatial type example ---------------------------------------------------
  //   S"xs" : union of classes {len 2 ↦ K, len 4 ↦ N, len 6 ↦ M};  S"ys" : size 0;  P"k" : length 3
  //   \/(S"xs" <| (S"ys" \/ Singleton(P"k")))
  // The prefix set is just {k} (|k| = 3): length-2 paths CANNOT start with a length-3 prefix and
  // are annihilated; lengths 4 and 6 survive (≤N, ≤M) and TailsUnion shifts them down to 3 and 5.
  test("input→output spatial type: restriction annihilates the short class, tails shifts the rest") {
    val (nK, nN, nM) = (7L, 5L, 3L)
    val env = SpatialEnv(
      spaces = Map(SpaceMention("xs") -> SpaceType.closed(2L -> Ivl(nK, nK), 4L -> Ivl(nN, nN), 6L -> Ivl(nM, nM)),
                   SpaceMention("ys") -> SpaceType.empty),
      paths = Map(PathRef("k") -> LenBounds(3, 3)))
    val prog = \/(S"xs" <| (S"ys" \/ Space.Singleton(P"k")))
    val t = SpatialTypes.infer(prog, env)
    // the UPPER type is exactly the user's expectation: N entries at length 3, M at length 5
    assertEquals(t.byLen.keySet, Set(3L, 5L))
    assertEquals(t.at(3).hi, nN)
    assertEquals(t.at(5).hi, nM)
    assertEquals(t.at(1).hi, 0L, "the length-2 class must be annihilated by the length-3 prefix")
    // projections
    assertEquals(t.size.hi, nN + nM)
    assertEquals((t.len.lo, t.len.hi), (3L, 5L))
    // SOUND on a concrete instantiation matching the declared input types
    val xs = SpaceValue((1L to nK).map(i => PathValue(List("z", s"z$i"))).toSet
      ++ (1L to nN).map(i => PathValue(List("k1", "k2", "k3", s"t$i"))).toSet
      ++ (1L to nM).map(i => PathValue(List("k1", "k2", "k3", s"u$i", "v", "w")).ensuring(_.items.length == 6)).toSet)
    given PathContext = PathContextMap(Map(PathRef("k") -> PathValue(List("k1", "k2", "k3"))))
    given SpaceContext = SpaceContextMap(Map(SpaceMention("xs") -> xs, SpaceMention("ys") -> SpaceValue(Set.empty)))
    checkSound(prog, t, "xs-example")
    assertEquals(histogram(eval(prog)), Map(3L -> nN, 5L -> nM), "ground truth: N at length 3, M at length 5")
    // the sound LOWER bound is 0 per class: restriction may filter everything (nothing in the
    // declared inputs says xs's long paths start with k) — see the report note.
    assertEquals(t.at(3).lo, 0L)
  }

  // ---- the `s || g` control-flow operator ------------------------------------------------------
  //   s || g  ==  s ∪ (({"E"} \ ("E"·s).iter(h,_,{h})) .iter(_,_, g))
  def cf(s: Space, g: Space): Space =
    s \/ Space.Iteration(
      Space.Subtraction(lit(PathValue(List("E"))), ("E" x s).iter(P"h", S"_", sP"h")),
      PathRef("_").known(1), SpaceMention("_"), g)

  test("control-flow operator: the spatial derivation reproduces ⌈s⌉+⌈g⌉ / ⌊s⌋ max relu(1−⌈s⌉)·⌊g⌋") {
    val g = lit(pathOf(2, "g"), pathOf(3, "g"), pathOf(4, "g"))     // 3 paths, lengths 2/3/4
    // s = {} : the guard fires, the result IS g — exactly, per length
    val e = cf(lit(), g)
    val te = SpatialTypes.infer(e)
    assertEquals(te.size, SizeBounds(3, 3, 3), "s = {}: ⌊{}||g⌋ = ⌈{}||g⌉ = |g|")
    assertEquals(te.byLen.toMap, Map(2L -> Ivl(1, 1), 3L -> Ivl(1, 1), 4L -> Ivl(1, 1)))
    checkSound(e, te, "cf-empty")
    // s nonempty : the derivation gives [⌊s⌋, ⌈s⌉+⌈g⌉] = [2, 5] and the classes are both sides'
    val s2 = lit(pathOf(1, "s"), pathOf(5, "s"))
    val n = cf(s2, g)
    val tn = SpatialTypes.infer(n)
    assertEquals((tn.size.lo, tn.size.hi), (2L, 5L))
    assertEquals(tn.byLen.keySet, Set(1L, 2L, 3L, 4L, 5L))
    checkSound(n, tn, "cf-nonempty")
    // the same derivation on an OPEN s carrying only a size contract — no literal to look at
    val sOpen = Space.Mention(SpaceMention("s").known(2))
    val to = SpatialTypes.infer(cf(sOpen, g))
    assert(to.size.lo >= 2L && to.size.hi <= 5L, s"open derivation: ${to.size} outside [2, 5]")
    locally {
      given SpaceContext = SpaceContextMap(Map(SpaceMention("s") -> SpaceValue(Set(pathOf(1, "s"), pathOf(5, "s")))))
      checkSound(cf(sOpen, g), to, "cf-open")
    }
    // never worse than the dedicated size analysis, on either
    for p <- List(e, n) do
      val (sp, base) = (SpatialTypes.infer(p).size, Lower.sizeBounds(p))
      assert(sp.lo >= base.lo && sp.hi <= base.hi, s"spatial size ${sp} looser than baseline $base")
  }

  test("per-length precision the size/length analyses cannot express separately") {
    // arithmetic-style class shifting: wrap by a length-2 tag, then unwrap it away
    val v = lit(pathOf(1, "a"), pathOf(1, "b"), pathOf(3, "c"))
    val w = Space.Wrap(v, Path.Constant(pathOf(2, "tag")))
    assertEquals(SpatialTypes.infer(w).byLen.toMap, Map(3L -> Ivl(2, 2), 5L -> Ivl(1, 1)), "wrap is a bijection: shift classes")
    assertEquals(SpatialTypes.infer(Space.Unwrap(w, Path.Constant(pathOf(2, "tag")))).byLen.keySet, Set(1L, 3L))
    // a meet of length-DISJOINT classes is provably empty (the LenZ3 motivating shape, statically)
    val disj = Space.Intersection(lit(pathOf(10)), lit(pathOf(15)))
    assert(SpatialTypes.infer(disj).isProvablyEmpty)
    // raffination keeps SHORT classes exactly (they can never be restricted away)
    val raf = Space.Raffination(lit(pathOf(1), pathOf(4)), Space.Singleton(Path.Constant(pathOf(3, "p"))))
    assertEquals(SpatialTypes.infer(raf).at(1), Ivl(1, 1), "a length-1 path cannot have a length-3 prefix")
    assertEquals(SpatialTypes.infer(raf).at(4), Ivl(0, 1), "the long class may be restricted away")
    // tails dedupe: N paths of one length collapse to between 1 and N tails
    assertEquals(SpatialTypes.infer(Space.TailsUnion(lit(pathOf(3, "x"), pathOf(3, "y")))).at(2), Ivl(1, 2))
  }

  // ---- the RELATIONAL layer (licensed by proofs/spatial/sp_subsume_*.smt2) ----------------------
  test("subsumption tightening: the shapes a pure count domain double-counts") {
    val x = lit(pathOf(1, "a"), pathOf(2, "b"), pathOf(2, "c"))       // 3 paths: {1↦1, 2↦2}
    val y = lit(pathOf(2, "b"), pathOf(3, "d"))
    val tx = SpatialTypes.infer(x)
    // x ∪ (x ∩ y) = x  — the motivating over-estimate (naive: |x| + |x∩y|)
    val absorb = Space.Union(x, Space.Intersection(x, y))
    assertEquals(SpatialTypes.infer(absorb).size, tx.size)
    assertEquals(eval(absorb), eval(x))
    // x ∩ (x ∪ y) = x ; (x∩y) ∖ x = ∅ ; x ∪ (x <| y) = x ; x ∪ (x \| y) = x
    assertEquals(SpatialTypes.infer(Space.Intersection(x, Space.Union(x, y))).size, tx.size)
    assert(SpatialTypes.infer(Space.Subtraction(Space.Intersection(x, y), x)).isProvablyEmpty)
    assertEquals(SpatialTypes.infer(Space.Union(x, Space.Restriction(x, y))).size, tx.size)
    assertEquals(SpatialTypes.infer(Space.Union(x, Space.Raffination(x, y))).size, tx.size)
    // (x<|y) ⊎ (x\|y) = x EXACTLY (the partition rule)
    val part = Space.Union(Space.Restriction(x, y), Space.Raffination(x, y))
    assertEquals(SpatialTypes.infer(part).byLen.toMap, tx.byLen.toMap)
    assertEquals(eval(part), eval(x))
    // subsumption is sound on OPEN terms too, and matches eval under a binding
    val ox = Space.Union(S"s0", Space.Intersection(S"s0", S"s1"))
    val env = SpatialEnv(spaces = Map(SpaceMention("s0") -> SpaceType.closed(1L -> Ivl(2, 2)),
                                      SpaceMention("s1") -> SpaceType.unknown))
    assertEquals(SpatialTypes.infer(ox, env).size.hi, 2L, "must NOT be |s0| + |s0∩s1|")
    locally {
      given SpaceContext = SpaceContextMap(Map(
        SpaceMention("s0") -> SpaceValue(Set(PathValue(List("a")), PathValue(List("b")))),
        SpaceMention("s1") -> SpaceValue(Set(PathValue(List("b")), PathValue(List("z"))))))
      checkSound(ox, SpatialTypes.infer(ox, env), "open-absorb")
    }
  }

  // ---- independent cross-validation against BOTH z3 tiers ---------------------------------------
  test("random programs: per-length soundness, and both projections fall within the z3 bounds") {
    val f = new java.io.File(Loaders.repoRoot, "corpus_1000.ser")
    assert(f.exists, "corpus not found — run morkl.ProgramExpressivity first")
    val recs = locally {
      val ois = new java.io.ObjectInputStream(new java.io.FileInputStream(f))
      try ois.readObject().asInstanceOf[Vector[FuzzRec]] finally ois.close()
    }
    val rng = new java.util.Random(60806)
    val A = SpaceFuzzer.alphabet
    def randPath(): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
    def randSV(): SpaceValue = SpaceValue((0 until rng.nextInt(6)).map(_ => randPath()).toSet)
    val sNames = (0 until 3).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until 3).map(j => PathRef("p" + j)).toVector

    var checked = 0; var tighterSize = 0; var tighterLen = 0
    for r <- recs; _ <- 0 until 3 do
      val svs = Vector.fill(3)(randSV()); val pvs = Vector.fill(3)(randPath())
      val closed = subs(r.prog)(
        spre = { case Space.Mention(m) if sNames.contains(m) => Space.Literal(svs(sNames.indexOf(m))) },
        ppre = { case Path.Deref(pr) if pNames.contains(pr) => Path.Constant(pvs(pNames.indexOf(pr))) })
      // (1) per-length soundness of the closed program
      val tc = SpatialTypes.infer(closed)
      checkSound(closed, tc, "corpus-closed")
      // and of the OPEN program under the env describing those same inputs
      val env = SpatialEnv(spaces = sNames.zipWithIndex.map((m, i) => m -> SpaceType.of(svs(i))).toMap,
                           paths = pNames.zipWithIndex.map((p, j) => p -> LenBounds(pvs(j).items.length, pvs(j).items.length)).toMap)
      val to = SpatialTypes.infer(r.prog, env)
      checkSound(r.prog, to, "corpus-open")(using PathContextMap(pNames.zip(pvs).toMap), SpaceContextMap(sNames.zip(svs).toMap))
      // (2) the size projection is sound and at least as tight as tier-1
      val sp = SpatialTypes.sizeOf(closed); val sb = Lower.sizeBounds(closed)
      val n = eval(closed).paths.size.toLong
      assert(sp.lo <= n && n <= sp.hi, s"spatial size ${sp} excludes $n for ${closed.show}")
      if sp.hi < sb.hi || sp.lo > sb.lo then tighterSize += 1
      // (3) the length projection is sound and at least as tight as tier-1
      val lp = SpatialTypes.lenOf(closed); val lb = Lower.lenBounds(closed)
      for l <- histogram(eval(closed)).keys do
        assert(lp.lo <= l && l <= lp.hi, s"spatial len [${lp.lo}, ${lp.hi}] excludes $l for ${closed.show}")
      if !lp.isEmpty && !lb.isEmpty && (lp.lo > lb.lo || lp.hi < lb.hi) then tighterLen += 1
      checked += 1
    println(s"SPATIAL: $checked closed corpus instances — per-length sound; strictly tighter than " +
      s"tier-1 on size $tighterSize, on length $tighterLen")

    assume(SizeZ3.available, "z3 not on PATH")
    var szIn = 0; var lnIn = 0; var szOut = 0; var lnOut = 0; var n3 = 0
    val incomparable = collection.mutable.Buffer.empty[String]
    for (r, pi) <- recs.take(150).zipWithIndex do
      // (2') the SIZE projection vs the z3 space-size bounds
      val (zs, ss) = SizeZ3.boundsWithStatus(r.prog, timeoutSec = 5)
      if ss == SizeZ3.Status.Solved then
        val sp = SpatialTypes.sizeOf(r.prog)
        // both over-approximate the same value, so they must at least be CONSISTENT
        assert(sp.lo <= zs.hi && zs.lo <= sp.hi, s"spatial size $sp inconsistent with z3 $zs for ${r.prog.show}")
        if sp.lo >= zs.lo && sp.hi <= zs.hi then szIn += 1
        else
          szOut += 1
          if incomparable.size < 3 then
            incomparable += f"#$pi spatial=[${sp.lo}, ${sp.hi}] z3=[${zs.lo}, ${zs.hi}] :: ${r.prog.show.take(160)}"
        // the MEET dominates both, by construction
        val best = SpatialTypes.bestSize(r.prog, timeoutSec = 5)
        assert(best.lo >= (sp.lo max zs.lo) && best.hi <= (sp.hi min zs.hi), s"bestSize $best not the meet of $sp and $zs")
      // (3') the LENGTH projection vs the z3 path-length bounds
      val (zl, sl) = LenZ3.boundsWithStatus(r.prog, timeoutSec = 5)
      if sl == SizeZ3.Status.Solved then
        val lp = SpatialTypes.lenOf(r.prog)
        if !lp.isEmpty && !zl.isEmpty then
          assert(lp.lo <= zl.hi && zl.lo <= lp.hi, s"spatial len $lp inconsistent with z3 $zl for ${r.prog.show}")
          if lp.lo >= zl.lo && lp.hi <= zl.hi then lnIn += 1 else lnOut += 1
      n3 += 1
    println(s"SPATIAL-vs-Z3 ($n3 programs): size projection within z3 on $szIn (outside on $szOut); " +
      s"length projection within z3 on $lnIn (outside on $lnOut)")
    incomparable.foreach(x => println(s"    incomparable (z3 relational facts win): $x"))
    assert(szIn + lnIn > 0, "no comparisons ran — z3 tiers broken?")

    // the MEET of all tiers is sound on concrete values (the answer a consumer should use)
    for r <- recs.take(40) do
      val svs = Vector.fill(3)(randSV()); val pvs = Vector.fill(3)(randPath())
      val closed = subs(r.prog)(
        spre = { case Space.Mention(m) if sNames.contains(m) => Space.Literal(svs(sNames.indexOf(m))) },
        ppre = { case Path.Deref(pr) if pNames.contains(pr) => Path.Constant(pvs(pNames.indexOf(pr))) })
      val v = eval(closed)
      val bs = SpatialTypes.bestSize(closed, timeoutSec = 5)
      assert(bs.lo <= v.paths.size && v.paths.size <= bs.hi, s"bestSize $bs excludes ${v.paths.size}")
      val bl = SpatialTypes.bestLen(closed, timeoutSec = 5)
      for l <- histogram(v).keys do assert(bl.lo <= l && l <= bl.hi, s"bestLen $bl excludes $l")
  }
end SpatialTypeCheck
