package morkl

import munit.FunSuite

/** THE RESIDUAL CUT IS A FUNCTION OF ITS ARGUMENTS — tested directly.
 *
 *  `terminating/REGISTRY.tsv` row O10c: `unrollControl` replaces a recursive call past depth `k`
 *  with a fresh free input, and the obligation the emitters then state is "the two k-unrollings
 *  agree FOR ALL values of that input". That is sound only if both sides cut the same routine, at
 *  the same depth, **with the same arguments**.
 *
 *  The symbol used to be `residual_<routine>_<depth>` with the arguments discarded, and the gate in
 *  `EquivPipelineTest` compared the two sides' residual NAME SETS — which carried no argument
 *  information, so two cuts with different recursive arguments shared one opaque set and a rewrite
 *  that changed an argument was hidden behind it. `AgnosticPipeline.ResidualCut` keys the symbol by
 *  a digest of the alpha-normalised arguments instead.
 *
 *  WHY THIS FILE EXISTS RATHER THAN LEAVING IT TO THE PIPELINE.  On the seven cornerstones the
 *  mechanism is exercised only trivially: `datalog-sn`'s `sn_tc` is the one self-recursive routine
 *  no `asFixpoint` lowering recognises, and its two agnostic sides come out syntactically identical
 *  after alpha-normalisation, so `SmtDiff` emits no obligation and no residual symbol reaches a
 *  file. The cut therefore aligns for a reason that has nothing to do with the argument keying. The
 *  discrimination the keying buys is tested here, on cuts built directly.
 */
class ResidualCutCheck extends FunSuite:
  import Space.*
  import AgnosticPipeline.{ResidualCut, alignCuts, residualsOf, unrollControl}

  private def sv(xs: String*): SpaceValue =
    SpaceValue(xs.map(s => PathValue(s.split('.').toList)).toSet)
  private val pA = Path.Constant(PathValue(List("a")))
  private val pB = Path.Constant(PathValue(List("b")))

  /** A self-recursion NO `asFixpoint` lowering recognises, so `unrollControl` really does reach the
   *  residual cut.  It changes TWO mentions at once, and `asFixpointGeneral` requires exactly one —
   *  the documented honest-residual case, and the shape `datalog-sn`'s `sn_tc` has (it changes both
   *  `all` and `delta`).  A single-changing-mention routine would be lowered to a `Space.Fixpoint`
   *  instead and no cut would be made at all, which is the desired behaviour and the reason the
   *  first draft of this test measured nothing. */
  private val twoMention: Routine =
    val (m, d) = (SpaceMention("all"), SpaceMention("delta"))
    val rp = RoutinePtr("sn_tc")
    Routine(rp, Vector.empty, Vector(m, d),
            Union(Mention(m), Call(rp, Vector.empty, Vector(TailsUnion(Mention(m)), TailsUnion(Mention(d))))))

  test("the probe routine is genuinely NOT lowerable — else no cut is made and this file tests nothing") {
    assert(asFixpointGeneral(twoMention.name, twoMention.refs, twoMention.mentions, twoMention.body).isEmpty,
           "asFixpointGeneral lowered the probe routine, so unrollControl will produce a Fixpoint " +
           "instead of a residual cut and every assertion below would be vacuous")
    assert(asFixpoint(twoMention).isEmpty, "asFixpoint lowered the probe routine")
  }

  test("equal routine, depth AND arguments give the SAME symbol") {
    val c1 = ResidualCut("tc", 2, Vector(pA), Vector(Literal(sv("x"))))
    val c2 = ResidualCut("tc", 2, Vector(pA), Vector(Literal(sv("x"))))
    assertEquals(c1.symbol, c2.symbol)
    assertEquals(c1.canonical, c2.canonical)
  }

  test("ALPHA-EQUAL arguments give the same symbol — the keying is not syntactic") {
    // the same body with different binder names must key identically, or the gate would report a
    // misalignment for two cuts that really do cut the same thing
    def body(rest: String, sym: String) =
      Iteration(Mention(SpaceMention("src")), PathRef(sym).known(1), SpaceMention(rest),
                Wrap(Mention(SpaceMention(rest)), Path.Deref(PathRef(sym).known(1))))
    val c1 = ResidualCut("tc", 1, Vector.empty, Vector(body("t1", "h1")))
    val c2 = ResidualCut("tc", 1, Vector.empty, Vector(body("t2", "h2")))
    assertNotEquals(body("t1", "h1"), body("t2", "h2"), "the two bodies must differ syntactically")
    assertEquals(c1.symbol, c2.symbol, s"alpha-equal arguments keyed differently:\n  ${c1.canonical}\n  ${c2.canonical}")
  }

  test("DIFFERENT arguments give DIFFERENT symbols — the discrimination the old naming lacked") {
    val c1 = ResidualCut("tc", 2, Vector.empty, Vector(Literal(sv("x"))))
    val c2 = ResidualCut("tc", 2, Vector.empty, Vector(Literal(sv("y"))))
    assertNotEquals(c1.symbol, c2.symbol,
      "two cuts of the same routine at the same depth with DIFFERENT arguments share a symbol — " +
      "this is exactly the gap `residual_<routine>_<depth>` had")
    // and a different PATH argument is discriminated too, not only a space argument
    val c3 = ResidualCut("tc", 2, Vector(pA), Vector(Literal(sv("x"))))
    val c4 = ResidualCut("tc", 2, Vector(pB), Vector(Literal(sv("x"))))
    assertNotEquals(c3.symbol, c4.symbol, "the path arguments are not part of the key")
    // routine and depth still discriminate
    assertNotEquals(ResidualCut("tc", 2, Vector.empty, Vector(Empty)).symbol,
                    ResidualCut("tc", 3, Vector.empty, Vector(Empty)).symbol, "depth")
    assertNotEquals(ResidualCut("tc", 2, Vector.empty, Vector(Empty)).symbol,
                    ResidualCut("sn", 2, Vector.empty, Vector(Empty)).symbol, "routine")
  }

  test("alignCuts: aligned when the cuts agree, MISALIGNED with both descriptors when they do not") {
    def cutIn(c: ResidualCut): Space =
      // register the symbol the way `unrollControl` does, by going through a real unrolling
      Union(Mention(SpaceMention(c.symbol)), Literal(sv("z")))
    val other = ResidualCut("tc", 2, Vector.empty, Vector(Literal(sv("y"))))
    // a real unrolling is what populates the descriptor table; do one so `residualsOf` can resolve
    given rc: PartialFunction[RoutinePtr, Routine] = { case r if r == twoMention.name => twoMention }
    val unrolled = unrollControl(Call(twoMention.name, Vector.empty,
                                      Vector(Literal(sv("p.q")), Literal(sv("p")))), 1)
    val cuts = residualsOf(unrolled)
    assert(cuts.nonEmpty, s"the unrolling produced no residual cut: ${unrolled.show}")
    for (sym, d) <- cuts do
      assertEquals(d.routine, "sn_tc", s"descriptor lost the routine: $d")
      assert(sym.startsWith("residual_sn_tc_"), s"unexpected symbol $sym")
      assert(d.canonical.contains("sn_tc@"), s"canonical form is not readable: ${d.canonical}")
    // a term against itself is aligned
    val self = alignCuts(unrolled, unrolled)
    assert(self.aligned, s"a term is misaligned against itself: ${self.report}")
    assertEquals(self.shared, cuts.keySet)
    assert(self.report.startsWith("aligned"), self.report)
    // and against a term whose cut carries a different argument it is not
    val bad = alignCuts(unrolled, cutIn(other))
    assert(!bad.aligned, "a differently-argued cut was reported as aligned")
    assert(bad.report.startsWith("MISALIGNED"), bad.report)
  }

  test("a real unrolling at two different depths keys the cuts apart") {
    given rc: PartialFunction[RoutinePtr, Routine] = { case r if r == twoMention.name => twoMention }
    val call = Call(twoMention.name, Vector.empty, Vector(Literal(sv("p.q.r")), Literal(sv("p"))))
    val at1 = residualsOf(unrollControl(call, 1))
    val at2 = residualsOf(unrollControl(call, 2))
    assert(at1.nonEmpty && at2.nonEmpty, s"k=1 gave ${at1.size} cuts, k=2 gave ${at2.size}")
    // the deeper unrolling cuts at a deeper depth AND with a further-transformed argument, so the
    // two must not share a symbol: the k=1 and k=2 certificates are about different free inputs
    assertEquals(at1.keySet intersect at2.keySet, Set.empty[String],
      s"the k=1 and k=2 unrollings share a residual symbol:\n  k=1 ${at1.values.map(_.canonical).mkString(", ")}" +
      s"\n  k=2 ${at2.values.map(_.canonical).mkString(", ")}")
    assert(!alignCuts(unrollControl(call, 1), unrollControl(call, 2)).aligned,
           "the k=1 and k=2 unrollings were reported as cutting the same thing")
  }
end ResidualCutCheck
