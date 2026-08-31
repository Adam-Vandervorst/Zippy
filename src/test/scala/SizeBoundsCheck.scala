package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** The abstract result-size analysis ([[Lower.sizeBounds]]) must be SOUND — `lo ≤ |eval(s)| ≤ hi`
 *  and `loHeaded ≤ |{p ∈ eval(s) : p ≠ ε}|` for every space — and precise enough to decide the
 *  `s || g` control-flow operator's size behaviour (the motivating derivation).  The corpus test
 *  is the soundness gate; the others pin the transfer functions. */
class SizeBoundsCheck extends FunSuite:
  import Space.*

  def check(s: Space, name: String = "")(using sc: SpaceContext = SpaceContextMap(Map.empty),
                                          pc: PathContext = PathContextMap(Map.empty)): Unit =
    val b = Lower.sizeBounds(s)
    assert(0 <= b.loHeaded && b.loHeaded <= b.lo && b.lo <= b.hi, s"$name: malformed interval $b for ${s.show}")
    val v = eval(s)
    val n = v.paths.size.toLong
    val nHeaded = v.paths.count(_.items.nonEmpty).toLong
    assert(b.lo <= n && n <= b.hi, s"$name: |eval| = $n outside [${b.lo}, ${b.hi}] for ${s.show}")
    assert(b.loHeaded <= nHeaded, s"$name: headed count $nHeaded below ${b.loHeaded} for ${s.show}")

  test("soundness over the corpus: lo ≤ |eval| ≤ hi on closed programs (open bounds contain too)") {
    val recs = Corpus.load()
    val rng = new java.util.Random(4242)
    val A = SpaceFuzzer.alphabet
    def randPath(): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
    def randSV(): SpaceValue = SpaceValue((0 until rng.nextInt(6)).map(_ => randPath()).toSet)
    val sNames = (0 until 3).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until 3).map(j => PathRef("p" + j)).toVector
    var checked = 0
    for r <- recs; _ <- 0 until 5 do
      val svs = Vector.fill(3)(randSV()); val pvs = Vector.fill(3)(randPath())
      val closed = subs(r.prog)(
        spre = { case Space.Mention(m) if sNames.contains(m) => Space.Literal(svs(sNames.indexOf(m))) },
        ppre = { case Path.Deref(pr) if pNames.contains(pr) => Path.Constant(pvs(pNames.indexOf(pr))) })
      // closed bounds are tight-ish; open bounds must also contain (mentions widen to [0, ∞))
      val n = eval(closed).paths.size.toLong
      val cb = Lower.sizeBounds(closed)
      assert(cb.lo <= n && n <= cb.hi, s"closed: |eval| = $n outside [${cb.lo}, ${cb.hi}] for ${closed.show}")
      val ob = Lower.sizeBounds(r.prog)
      assert(ob.lo <= n && n <= ob.hi, s"open: |eval| = $n outside [${ob.lo}, ${ob.hi}] for ${r.prog.show}")
      // the reduced program denotes the same set: its bounds must contain the same size
      val rb = Lower.sizeBounds(SC.reduce(closed))
      assert(rb.lo <= n && n <= rb.hi, s"reduced: |eval| = $n outside [${rb.lo}, ${rb.hi}]")
      checked += 1
    println(s"SIZE-BOUNDS: $checked closed corpus instances, all inside their intervals")
  }

  // ---- the motivating example: the `s || g` control-flow operator -------------------------------
  //   s \/ (({"E"} \ Head("E"·s)).iter(_, _, g))   —  g if s is empty, s otherwise
  def cf(s: Space, g: Space): Space =
    s \/ Space.Iteration(
      Space.Subtraction(Space.Literal(SpaceValue(PathValue(List("E")))),
                        ("E" x s).iter(P"h", S"_", sP"h")),
      PathRef("_"), SpaceMention("_"), g)

  test("control-flow operator: ⌈s||g⌉ = ⌈s⌉ + ⌈g⌉ and ⌊s||g⌋ = ⌊s⌋ max relu(1−⌈s⌉)·⌊g⌋") {
    val g = Space.Literal(SpaceValue("g.1", "g.2", "g.3"))
    // s = {}: the estimate collapses to exactly |g| — ⌊{} || g⌋ = ⌈{} || g⌉ = |g|
    val empty = cf(Space.Literal(SpaceValue()), g)
    val be = Lower.sizeBounds(empty)
    assertEquals((be.lo, be.hi), (3L, 3L), "s = {}: interval must pin |g| exactly")
    assertEquals(eval(empty).paths.size, 3)
    // s = {x} ∪ s': ⌊s||g⌋ = |s| and ⌈s||g⌉ = |s| + |g|
    val s2 = Space.Literal(SpaceValue("x", "y.z"))
    val nonempty = cf(s2, g)
    val bn = Lower.sizeBounds(nonempty)
    assertEquals((bn.lo, bn.hi), (2L, 5L), "s nonempty: [|s|, |s|+|g|]")
    assertEquals(eval(nonempty).paths.size, 2)
    check(empty, "cf-empty"); check(nonempty, "cf-nonempty")
    // symbolic s: both branches stay possible — [⌊g⌋ min ⌊s⌋ = 0, ∞)
    val sym = cf(S"sym", g)
    val bs = Lower.sizeBounds(sym)
    assertEquals(bs.lo, 0L); assertEquals(bs.hi, Lower.SizeBounds.INF)
  }

  test("transfer functions on the tricky cases") {
    val ab = Space.Literal(SpaceValue("a", "a.a"))
    // composition collision: {a, a.a}·{a, a.a} has 3 paths, not 4 — the naive ⌊l⌋·⌊r⌋ = 4 is
    // unsound; the sound lower bound is max(⌊l⌋, ⌊r⌋) = 2
    val comp = Space.Composition(ab, ab)
    assertEquals(eval(comp).paths.size, 3)
    assertEquals(Lower.sizeBounds(comp).lo, 2L)
    assertEquals(Lower.sizeBounds(comp).hi, 4L)
    // subtraction of a provably-empty right side keeps the left interval whole
    val sub = Space.Subtraction(ab, Space.Intersection(Space.Empty, S"u"))
    assertEquals((Lower.sizeBounds(sub).lo, Lower.sizeBounds(sub).hi), (2L, 2L))
    // ε-only literal: nonempty but NOT headed — an iteration over it runs zero groups
    val epsOnly = Space.Literal(SpaceValue(PathValue(Nil)))
    val itEps = Space.Iteration(epsOnly, PathRef("h"), SpaceMention("t"), ab)
    assertEquals(Lower.sizeBounds(epsOnly).loHeaded, 0L)
    assertEquals(Lower.sizeBounds(itEps).lo, 0L, "ε-only source must not lower-bound the iteration")
    assertEquals(eval(itEps).paths.size, 0)
    // a headed literal source guarantees one group's body
    val itH = Space.Iteration(ab, PathRef("h"), SpaceMention("t"), Space.Literal(SpaceValue("q.q")))
    assertEquals(Lower.sizeBounds(itH).lo, 1L)
    check(itH, "iter-headed")
    // the emptiness guards are ⊆ {ε} in size terms: hi ≤ 1 even on unknowns
    assert(Lower.sizeBounds(Lower.headedGuard(S"u")).hi <= 1L)
    assert(Lower.sizeBounds(Lower.nonEmptyGuard(S"u")).hi <= 2L)  // ∩{ε} branch + range probe
    // Range windows: (0,k) and (−k,0) slice exactly min(size, k)
    assertEquals((Lower.sizeBounds(Space.Range(ab, 0, 1)).lo, Lower.sizeBounds(Space.Range(ab, 0, 1)).hi), (1L, 1L))
    assertEquals((Lower.sizeBounds(Space.Range(ab, -1, 0)).lo, Lower.sizeBounds(Space.Range(ab, -1, 0)).hi), (1L, 1L))
    // fixpoints only grow from init
    val fix = Space.Fixpoint(ab, SpaceMention("r"), S"r")
    assertEquals(Lower.sizeBounds(fix).lo, 2L)
    assertEquals(Lower.sizeBounds(fix).hi, Lower.SizeBounds.INF)
  }

  test("sizeHint: an exact-cardinality contract on a mention narrows both tiers") {
    val x5 = Space.Mention(SpaceMention("x").known(5))
    // hint is exact: [5, 5], of which at most one path is ε ⇒ ≥ 4 headed
    assertEquals(Lower.sizeBounds(x5), Lower.SizeBounds(5, 4, 5))
    // equality ignores the hint (an annotation, not identity) — contexts still resolve by name
    assertEquals(SpaceMention("x").known(5), SpaceMention("x"))
    val v = SpaceValue("a", "b.c", "d", "e.f.g", "h")
    check(x5, "hinted-mention")(using SpaceContextMap(Map(SpaceMention("x") -> v)))
    // flows through operators: hinted ∪ hinted is [5, 10]; hinted \ small keeps a real lower bound
    val u = Space.Union(x5, Space.Mention(SpaceMention("y").known(5)))
    assertEquals((Lower.sizeBounds(u).lo, Lower.sizeBounds(u).hi), (5L, 10L))
    val s = Space.Subtraction(x5, Space.Literal(SpaceValue("a")))
    assertEquals((Lower.sizeBounds(s).lo, Lower.sizeBounds(s).hi), (4L, 5L))
    // a hint ≥ 2 makes the mention provably headed, so guarded hoists can fire on open programs
    assert(Lower.provablyHeaded(x5))
    assert(!Lower.provablyHeaded(Space.Mention(SpaceMention("z").known(1))))  // the 1 path may be ε
    // tier 2 keeps dominance: z3 bounds sit inside the hinted baseline
    if SizeZ3.available then
      val (zb, st) = SizeZ3.boundsWithStatus(u, timeoutSec = 5)
      assert(zb.lo >= 5L && zb.hi <= 10L, s"z3 $zb outside hinted baseline [5, 10] ($st)")
  }

  test("lengthHint: head-binders are tagged everywhere (guards, DSL fold, graph round-trip)") {
    def binderHints(s: Space): List[Int] = s match
      case Space.Iteration(src, sym, _, b) => sym.lengthHint :: binderHints(src) ::: binderHints(b)
      case Space.Fold(src, _, _, sym, _, b, _) => sym.lengthHint :: binderHints(src) ::: binderHints(b)
      case Space.Union(a, b) => binderHints(a) ::: binderHints(b)
      case Space.Intersection(a, b) => binderHints(a) ::: binderHints(b)
      case Space.Range(a, _, _) => binderHints(a)
      case _ => Nil
    // the emptiness guards' probe binders
    assertEquals(binderHints(Lower.headedGuard(S"u")), List(1))
    assert(binderHints(Lower.nonEmptyGuard(S"u")).forall(_ == 1))
    // the fold DSL's head symbol
    val fo = Space.Literal(SpaceValue("a", "b")).fold(Path.ZERO, "acc", "h", "t", S"t", Path.ZERO)
    assertEquals(binderHints(fo), List(1))
    // untranspile restores the tag the op-graph encoding drops
    val prog = Space.Literal(SpaceValue("a", "b.c")).iter(P"h", S"t", Space.Singleton(P"h" x "w"))
    val g = transpile(R"rt"() := prog)
    val st = scala.collection.mutable.Stack(new Array[Path | Space | Null](g.nodes.length))
    untranspile(g, st)
    val round = st.top.last.asInstanceOf[Space]
    assertEquals(binderHints(round), List(1))
    assertEquals(eval(round), eval(prog))
  }

  test("SizeEmpty: a provably-empty interval rewrites to Empty through any nesting") {
    val dead = Space.Union(
      Space.Wrap(Space.Restriction(S"u", Space.Intersection(Space.Empty, S"v")), Path.Constant(PathValue(List("k")))),
      Space.Composition(Space.Literal(SpaceValue()), S"w"))
    assertEquals(Lower.SizeEmpty(dead), Space.Empty)
    // and through optimized(): the whole routine body folds away
    val r = (R"q"(S"u") := dead).optimized(using PartialFunction.empty)
    assertEquals(r.body, Space.Empty)
  }
end SizeBoundsCheck
