package morkl

import munit.FunSuite

/** EVERY BACKEND SLICES `Range` BY THE SAME ORDER AND THE SAME NORMALIZATION — differentially.
 *
 *  `Range` is the one operator whose result is not a function of membership: which paths survive
 *  depends on their RANK in the canonical order (`docs/TRUSTED.md` T5). So two backends can each be
 *  individually "correct" about set operations and still disagree here, and nothing in the pointwise
 *  algebra laws would notice.
 *
 *  TWO CLAIMS, AND THEY ARE NOT THE SAME KIND.
 *
 *  The NORMALIZATION claim is structural and needs no test: there is exactly one
 *  `RangeBounds.normalize`, and all three implementations call it —
 *  `MORKL.sliceRange` (`eval`, and `exec` through it), `IntTrie.range` (`evalI`, and `execT` through
 *  the same `ITrie` operation), and `Trie.range` (`evalT`). "Every backend uses the same
 *  normalization" therefore holds because there is only one to use, which is stronger than two
 *  implementations agreeing on the cases someone thought to try.
 *
 *  The ORDER claim is the checkable one. `pathValueOrdering` is defined once, but `ITrie` and
 *  `Trie` do NOT sort by it: they slice their own child-key order and each carries a comment
 *  claiming that order INDUCES `pathValueOrdering`. That is an implementation-correspondence claim
 *  — exactly the kind `scripts/proof_closure.py` reports it cannot see — so it is checked here, on
 *  the cases where an order disagreement actually shows: the boundary slices, and the shapes where
 *  key order and path order can come apart (differing lengths on a shared prefix, interning order
 *  deliberately opposed to lexicographic order).
 *
 *  The case list is the review's: empty inputs, singleton inputs, clamping, negative indices,
 *  mixed-sign bounds, and a nested call under a binder.
 */
class RangeOrderCheck extends FunSuite:
  import Space.*

  private def sv(xs: String*): SpaceValue =
    SpaceValue(xs.map(s => PathValue(s.split('.').toList)).toSet)

  /** every executor, on a CLOSED term, as one list of (name, answer) */
  private def allBackends(prog: Space): Vector[(String, SpaceValue)] =
    allBackendsWith(prog, PartialFunction.empty)

  /** the same with a routine table, so a term containing a `Call` reaches every backend too */
  private def allBackendsWith(prog: Space,
                              routines: PartialFunction[RoutinePtr, Routine]): Vector[(String, SpaceValue)] =
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map.empty)
    given PartialFunction[RoutinePtr, Routine] = routines
    val g = transpile(Routine(RoutinePtr("r"), Vector.empty, Vector.empty, prog))
    // THE GRAPH BACKENDS RESOLVE A CALL BY NAME, through a TRANSPILED routine graph, where the
    // interpreters take a `RoutinePtr => Routine`.  Passing only the latter is why the Call case
    // used to run on three executors: `exec` threw `MatchError: firstOf` on the fourth.
    val idx: Map[String, RecursiveOpGraph] =
      routines match
        case _ if routines == PartialFunction.empty => Map.empty
        case _ => calledRoutines(prog, routines).map(r => r.name.s -> transpile(r)).toMap
    Vector(
      "eval"             -> eval(prog),
      "evalT"            -> evalT(prog).toSpaceValue,
      "evalI"            -> evalI(prog).toSpaceValue,
      // execZ WAS MISSING, and its absence made "every backend" false: the zipper is the executable
      // whose `Range` is a fused cursor slice rather than a call into `ITrie.range`, so it is the
      // one most able to disagree about the ORDER -- precisely the backend this file exists to
      // check.  `CorpusValidation` runs seven executors; this ran six.
      "execZ"            -> execZ(prog).toSpaceValue,
      "exec"             -> runGraph(g, index = idx),
      "execT"            -> runGraphT(g, index = idx).toSpaceValue,
      "execT/optimized"  -> runGraphT(optimize(g), index = idx).toSpaceValue,
    )

  /** the routines a term calls, transitively, so each can be transpiled into the graph index */
  private def calledRoutines(s: Space,
                             rc: PartialFunction[RoutinePtr, Routine]): Vector[Routine] =
    val out = scala.collection.mutable.LinkedHashMap.empty[String, Routine]
    def go(x: Space): Unit = x match
      case Call(rp, refs, ms) =>
        ms.foreach(go)
        if !out.contains(rp.s) then rc.lift(rp).foreach { r => out(rp.s) = r; go(r.body) }
      case Union(a, b) => go(a); go(b)
      case Intersection(a, b) => go(a); go(b)
      case Subtraction(a, b) => go(a); go(b)
      case Restriction(a, b) => go(a); go(b)
      case Raffination(a, b) => go(a); go(b)
      case Composition(a, b) => go(a); go(b)
      case Wrap(a, _) => go(a)
      case Unwrap(a, _) => go(a)
      case TailsUnion(a) => go(a)
      case TailsIntersection(a) => go(a)
      case Range(a, _, _) => go(a)
      case Iteration(src, _, _, body) => go(src); go(body)
      case Fixpoint(init, _, body) => go(init); go(body)
      case Fold(src, _, _, _, _, body, _) => go(src); go(body)
      case GroundedSS(a, _) => go(a)
      case _ => ()
    go(s)
    out.values.toVector

  private def agree(label: String, prog: Space): SpaceValue =
    val rs = allBackends(prog)
    val distinct = rs.map(_._2).distinct
    assertEquals(distinct.length, 1,
      s"$label: the backends DISAGREE on a positional slice:\n  " +
      rs.map((n, v) => f"$n%-16s ${v.pretty}").mkString("\n  "))
    distinct.head

  // the sources: each is a shape where key order and path order could come apart
  private val sources: Vector[(String, SpaceValue)] = Vector(
    "empty"                  -> sv(),
    "singleton"              -> sv("a"),
    "singleton eps-only"     -> SpaceValue(Set(PathValue(Nil))),
    "flat 5"                 -> sv("a", "b", "c", "d", "e"),
    // SHORTER-IS-LESS ON A SHARED PREFIX: `pathValueOrdering` compares items then length, so
    // `a` < `a.a`, and a child-key order that ignored the terminal flag would get this wrong
    "prefix chain"           -> sv("a", "a.a", "a.a.a", "a.b"),
    // interning order OPPOSED to lexicographic: these are first seen in reverse
    "reverse-interned"       -> sv("z", "y", "x", "w"),
    "mixed depth"            -> sv("b", "a.z", "a.a", "c.m.n", "a"),
    "eps plus heads"         -> SpaceValue(sv("b", "a").paths + PathValue(Nil)),
  )

  // the bound forms: the review's list, plus the two endpoint slices it names
  private val bounds: Vector[(Int, Int)] = Vector(
    (0, 0),                    // full window: the identity
    (0, 1), (-1, 0),           // first / last
    (0, 3), (2, 4),            // ordinary
    (0, 99), (50, 99),         // CLAMPING past the end
    (-3, -1), (-99, -1),       // NEGATIVE indices, including clamping
    (2, -1), (-3, 5),          // MIXED SIGN, both directions
    (4, 2), (-1, -3),          // INVERTED: hi <= lo, must be empty
  )

  test("all backends agree on every (source, bound) pair — and the answer is a PREFIX-STABLE slice") {
    var n = 0
    for (sname, src) <- sources; (lo, hi) <- bounds do
      val got = agree(s"$sname / Range(_, $lo, $hi)", Range(Literal(src), lo, hi))
      n += 1
      // the answer must be the slice of the SORTED source, which is the specification
      val want = sliceRange(src.paths, lo, hi)
      assertEquals(got.paths, want, s"$sname / Range(_, $lo, $hi): not the canonical-order slice")
      // and a slice is always a SUBSET of its source (U61's first half, on the executors)
      assert(got.paths.subsetOf(src.paths), s"$sname / Range(_, $lo, $hi): not a subset")
    println(s"RANGE-ORDER: ${n} (source, bound) pairs x ${allBackends(Range(Literal(sv("a")), 0, 1)).length} " +
            "executors, all agreeing with the canonical-order slice")
  }

  test("the FULL window is the identity on every backend and every source") {
    for (sname, src) <- sources do
      val got = agree(s"$sname / full", Range(Literal(src), 0, 0))
      assertEquals(got.paths, src.paths, s"$sname: a full window is not the identity")
  }

  test("Range(x, 0, 1) and Range(x, -1, 0) select the ORDER MINIMUM and MAXIMUM") {
    for (sname, src) <- sources if src.paths.nonEmpty do
      val sorted = src.paths.toVector.sorted(using pathValueOrdering)
      assertEquals(agree(s"$sname / first", Range(Literal(src), 0, 1)).paths, Set(sorted.head),
                   s"$sname: Range(_,0,1) is not the order MINIMUM")
      assertEquals(agree(s"$sname / last", Range(Literal(src), -1, 0)).paths, Set(sorted.last),
                   s"$sname: Range(_,-1,0) is not the order MAXIMUM")
    // on an EMPTY source both are empty rather than undefined
    assertEquals(agree("empty / first", Range(Literal(sv()), 0, 1)).paths, Set.empty[PathValue])
    assertEquals(agree("empty / last", Range(Literal(sv()), -1, 0)).paths, Set.empty[PathValue])
  }

  test("an INVERTED window is empty, not wrapped") {
    for (sname, src) <- sources; (lo, hi) <- Vector((4, 2), (-1, -3), (3, 1)) do
      assertEquals(agree(s"$sname / inverted($lo,$hi)", Range(Literal(src), lo, hi)).paths,
                   Set.empty[PathValue], s"$sname: Range(_, $lo, $hi) should be empty")
  }

  test("NESTED UNDER A BINDER: a Range inside an iteration body, and inside a called routine") {
    val src = sv("h0.c", "h0.a", "h0.b", "h1.z", "h1.y")
    val h = PathRef("h").known(1)
    val t = SpaceMention("t")
    // per head group, take the FIRST tail in canonical order and re-tag by the head
    val loop: Space = Iteration(Literal(src), h, t, Wrap(Range(Mention(t), 0, 1), Path.Deref(h)))
    val got = agree("Range under an Iteration binder", loop)
    assertEquals(got.paths, sv("h0.a", "h1.y").paths,
                 "the per-group first tail, re-tagged by the head")
    // the same window reached through a CALL, so the binder and the call boundary compose
    val rp = RoutinePtr("firstOf")
    val m = SpaceMention("m")
    val routine = Routine(rp, Vector.empty, Vector(m), Range(Mention(m), 0, 1))
    val callProg: Space = Iteration(Literal(src), h, t,
                                    Wrap(Call(rp, Vector.empty, Vector(Mention(t))), Path.Deref(h)))
    // THROUGH EVERY BACKEND, not three hand-picked ones.  The review's differential case is
    // "nested calls under binders", and running it on eval/evalI/evalT only -- which this did --
    // leaves out exactly the graph and zipper paths where a call boundary is translated rather than
    // interpreted.
    val want = sv("h0.a", "h1.y").paths
    val rs = allBackendsWith(callProg, { case r if r == rp => routine })
    for (n, v) <- rs do
      assertEquals(v.paths, want, s"$n: a Range under a binder, reached through a Call")
  }

  extension [A](a: A) private def |>[B](f: A => B): B = f(a)
end RangeOrderCheck
