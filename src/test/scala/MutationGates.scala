package morkl

import munit.FunSuite
import morkl.Space.*

/** THE GATES DISCRIMINATE: for each property the analysis claims, one mutation that removes it
 *  and one assertion that fails under the mutation and passes without it.
 *
 *   dropped alias facts        → the same-object union must allocate nothing on the trie (exact `same` case)
 *   reversed range order       → the counted run must lie in the predicted interval / the value's size bound
 *   erased calls               → a called routine's bounds must be finite
 *   optimistic lower bounds    → the counted run must lie in the predicted interval
 *   missing widening records   → a widening past the alternatives budget must be in the certificate
 *   open proof dependencies    → `proof_closure.py --inject-open O6a` must reach its consumers (C4 gate)
 *   forged coverage links      → `check_coverage.py --selftest` must catch its five forgeries (D1 gate)
 *
 *  Plus an ADVERSARIAL FAMILY across depth, width, operand count, aliasing and prefix overlap: random
 *  programs from a fixed seed, every one's counted run on every executor inside its certificate. */
class MutationGates extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  val s = SpaceMention("s"); val k = SpaceMention("k"); val h = PathRef("h"); val r = SpaceMention("r")
  val sVal = sv(p("a", "x"), p("a", "y", "z"), p("b", "x"), p("c", "q", "r", "t"), p("b"), p("a", "x", "w"))
  val kVal = sv(p("x"), p("y", "z"), p("q", "r"), p("a", "x"), p("b"))
  val values = Map(s -> sVal, k -> kVal)
  val noRc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty

  def counted(prog: Space, b: Backend, rc: PartialFunction[RoutinePtr, Routine] = noRc): Events =
    Decisions.counted(Residual(prog, SC.materialize(prog, rc)), b, values).getOrElse(fail(s"${b.slug} did not run"))

  /** the assertion a gate makes; returns the failure message when it fails */
  def failing(body: => Unit): Option[String] =
    try { body; None } catch case e: AssertionError => Some(e.getMessage)

  /** THE SHAPE OF EVERY CASE: the gate passes without the mutation and fails with it */
  def discriminates(mutation: String, what: String)(gate: => Unit): Unit =
    assertEquals(failing(gate), None, s"$what: the gate fails even WITHOUT the mutation `$mutation`")
    val under = Mutation.withActive(mutation)(failing(gate))
    assert(under.isDefined, s"$what: the gate did NOT fail under the mutation `$mutation` — it does not discriminate")
    println(s"E1 $mutation: caught — ${under.get.linesIterator.next().take(160)}")

  test("dropped alias facts: a declared input's count is memoised by the warm run, and the certificate is exact") {
    // `Range` over a DECLARED input in the warm phase reads a memoised count (the object is the input's, by
    // its alias fact); without the alias the analysis must assume a count walk over the trie, and the
    // upper bounds widen past the counted run
    val prog = Range(Mention(s), 0, 2)
    discriminates("drop-alias", "memoised count on a declared input") {
      val rep = CostSem.analyze(prog, CostSem.Inputs(values = values), Backend.Trie, noRc)
      val ev = counted(prog, Backend.Trie)
      val v = rep.bounds.violations(ev)
      assert(v.isEmpty && rep.component(EffortComponent.Touch).hi == ev.touch && rep.component(EffortComponent.Work).hi == ev.work,
             s"${v.mkString("; ")} touch ${rep.component(EffortComponent.Touch).show} vs counted ${ev.touch}, work ${rep.component(EffortComponent.Work).show} vs counted ${ev.work}")
    }
  }

  test("reversed range order: the counted run and the result size leave the certificate") {
    val prog = Union(Range(Union(Mention(s), Mention(k)), 0, 2), Range(Mention(s), 1, 3))
    discriminates("reverse-range", "range window") {
      for b <- Vector(Backend.Reference, Backend.Trie) do
        val rep = CostSem.analyze(prog, CostSem.Inputs(values = values), b, noRc)
        val ev = counted(prog, b)
        val v = rep.bounds.violations(ev)
        val result = eval(prog)(using PathContextMap(Map.empty), SpaceContextMap(values), noRc).paths.size
        assert(v.isEmpty && rep.valueSize.lo <= result && result <= rep.valueSize.hi,
               s"${b.slug}: ${v.mkString("; ")} result $result paths, predicted size ${rep.valueSize.show}")
    }
  }

  test("erased calls: a called routine's bounds are finite") {
    val f = Routine(RoutinePtr("f"), Vector.empty, Vector(SpaceMention("m")), Wrap(Mention(SpaceMention("m")), Path.Constant(p("x"))))
    val rc: PartialFunction[RoutinePtr, Routine] = Map(f.name -> f)
    val prog = Union(Call(f.name, Vector.empty, Vector(Mention(s))), Mention(k))
    discriminates("erase-calls", "call summary") {
      val rep = CostSem.analyze(prog, CostSem.Inputs(values = values), Backend.Trie, rc)
      assert(rep.finite, s"not finite: ${rep.bounds.showComponents}")
    }
  }

  test("optimistic lower bounds: the counted run leaves the certificate") {
    val prog = Union(Iteration(Mention(s), h, r, Wrap(Intersection(Mention(r), Mention(k)), Path.Deref(h))), TailsUnion(Mention(k)))
    discriminates("optimistic-lower", "lower bounds") {
      for b <- Vector(Backend.Reference, Backend.Trie, Backend.Zipper) do
        val rep = CostSem.analyze(prog, CostSem.Inputs(values = values), b, noRc)
        val v = rep.bounds.violations(counted(prog, b))
        assert(v.isEmpty, s"${b.slug}: ${v.mkString("; ")}")
    }
  }

  test("missing widening records: a widening past the alternatives budget is in the certificate") {
    discriminates("no-widening-record", "widening record") {
      val d = new Domain(DomainBudget(alternatives = 3))
      val s0 = SpaceMention("s0")
      var acc = d.input(s0, sv(p("a"), p("b", "c")))
      for i <- 0 until 2 do acc = d.joinA(acc, d.literal(sv(p(s"q$i"))))
      acc = d.joinA(acc, d.literal(sv(p("q9"), p("q8", "r"))))
      // the fourth alternative crossed the budget: the result is a summary, and the certificate must say so
      assert(!d.certificate.exact && d.certificate.widenings.exists(_.reason == "alternatives-budget"),
             s"precision was lost without a record: ${d.certificate.show}")
    }
  }

  def sh(args: String*): (Int, String) =
    val pr = new ProcessBuilder(args*).redirectErrorStream(true).start()
    val out = scala.io.Source.fromInputStream(pr.getInputStream).mkString
    (pr.waitFor(), out)

  test("open proof dependencies: an injected open entry reaches its consumers, and a claim of no consumers fails") {
    val (rc1, out1) = sh("python3", "scripts/proof_closure.py", "--inject-open", "O6a", "--expect-consumers", "1")
    assertEquals(rc1, 0, out1.linesIterator.toVector.takeRight(5).mkString("\n"))
    // the discriminating half: demanding MORE consumers than the injection reaches must fail
    val (rc2, _) = sh("python3", "scripts/proof_closure.py", "--inject-open", "O6a", "--expect-consumers", "1000")
    assertEquals(rc2, 1, "an unreachable consumer count passed")
  }

  test("forged coverage links: the independent checker catches its five forgeries") {
    val (rc, out) = sh("python3", "scripts/check_coverage.py", "--selftest")
    assertEquals(rc, 0, out.linesIterator.toVector.takeRight(8).mkString("\n"))
    assert(out.linesIterator.count(_.contains("caught")) >= 5, out)
  }

  // ---- THE ADVERSARIAL FAMILY ---------------------------------------------------------------------------
  /** random programs over the ring, iteration and tails, with aliasing (the same input twice) and prefix
   *  overlap (restriction by a literal sharing heads with the input), from a fixed seed */
  def gen(rng: scala.util.Random, depth: Int, width: Int): Space =
    val leaves = Vector[Space](Mention(s), Mention(k), Mention(s), Literal(sv(p("a"), p("b", "x"))), Literal(sv(p("a", "x"), p("q"))))
    def go(d: Int): Space =
      if d == 0 then leaves(rng.nextInt(leaves.length))
      else rng.nextInt(9) match
        case 0 => Union(go(d - 1), go(d - 1))
        case 1 => Intersection(go(d - 1), go(d - 1))
        case 2 => Subtraction(go(d - 1), go(d - 1))
        case 3 => Restriction(go(d - 1), leaves(3 + rng.nextInt(2)))
        case 4 => Wrap(go(d - 1), Path.Constant(p(Vector("a", "b", "z")(rng.nextInt(3)))))
        case 5 => Unwrap(go(d - 1), Path.Constant(p(Vector("a", "b")(rng.nextInt(2)))))
        case 6 => TailsUnion(go(d - 1))
        case 7 => Iteration(go(d - 1), h, r, Wrap(Union(Mention(r), leaves(rng.nextInt(2))), Path.Deref(h)))
        case _ => (1 until width).foldLeft(go(d - 1))((acc, _) => Union(acc, go(d - 1)))
    go(depth)

  test("ADVERSARIAL FAMILY: depth 1..4, width 1..3, aliasing and prefix overlap — every counted run inside its certificate") {
    val rng = new scala.util.Random(2026)
    var n = 0; var infinite = 0
    for depth <- 1 to 4; width <- 1 to 3; _ <- 0 until 4 do
      val prog = gen(rng, depth, width)
      for b <- Vector(Backend.Reference, Backend.Trie, Backend.Zipper) do
        val rep = CostSem.analyze(prog, CostSem.Inputs(values = values), b, noRc)
        Decisions.counted(Residual(prog, Map.empty), b, values) match
          case Some(ev) =>
            val v = rep.bounds.violations(ev)
            assert(v.isEmpty, s"depth $depth width $width ${b.slug}: ${v.mkString("; ")}\n  ${prog.show.replace("\n", " ").take(300)}")
            n += 1
            if !rep.finite then infinite += 1
          case None => ()
    println(s"E1 adversarial family: $n (program, backend) pairs contained, $infinite with an infinite component (sound, not useful)")
    assert(n >= 100)
  }
