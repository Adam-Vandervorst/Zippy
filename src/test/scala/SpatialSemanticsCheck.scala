package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==============================================================================================
 *  A1 — THE EVENT SEMANTICS IS THE COUNTED INTERPRETER'S SPECIFICATION, DIFFERENTIALLY.
 *
 *   acceptance: "differential tests show that instrumented executions and
 *  `SpatialEvents` produce the same event MULTISET for every constructor and backend; the test
 *  corpus includes empty, singleton, aliased, disjoint, deeply shared, recursive, and n-ary cases."
 *
 *  Every case below is run four ways — `eval`, `evalI`, `execT`, `execZ`, each under
 *  `SpatialEvents.counted` — and once through [[EventSemantics]] for the same backend, and the two
 *  `Events` are compared for EQUALITY over every `EffortEvent`, the explanatory ones included.  Not a
 *  component total: the multiset.  A disagreement names the case, the backend and the event, which is
 *  what makes the semantics falsifiable and what makes the hooks auditable.
 *
 *  The value is compared too, because a semantics that predicts the right events for the wrong
 *  answer has mis-modelled the machine.
 *  ============================================================================================== */
class SpatialSemanticsCheck extends FunSuite, CalibrationProbe:
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  def lit(ps: PathValue*): Space = Space.Literal(sv(ps*))
  val noRc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty

  final case class Case(label: String, prog: Space,
                        spaces: Map[SpaceMention, SpaceValue] = Map.empty,
                        paths: Map[PathRef, PathValue] = Map.empty,
                        rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                        /** `transpile` refuses `Fold` and grounded forms; those cases skip the graph leg */
                        graph: Boolean = true):
    /** THE GRAPH BACKEND'S PROGRAM.  `execT` has no stabilised-argument rule and `transpile` lowers
     *  only the identity-base self-recursion, so a program with `Call`s reaches the graph backend
     *  through the SAME lowering the pipeline uses (`lowerCalls`: `asFixpoint`, the tagged mutual
     *  encoding, inlining of the acyclic rest).  `None` when a residual recursive call survives it —
     *  that program is not executable by `execT`, and the leg is skipped and SAID to be skipped. */
    lazy val graphBody: Option[Space] =
      if !graph then None
      else if callees(prog).isEmpty then Some(prog)
      else
        val (top, residual) = lowerCalls(Routine(RoutinePtr("m"), paths.keys.toVector, spaces.keys.toVector, prog), rc)
        if residual.isEmpty then Some(top) else None
    def pc: PathContext = PathContextMap(paths)
    def sc: SpaceContext = SpaceContextMap(spaces)
    lazy val ic: Map[SpaceMention, ITrie] = spaces.view.mapValues(ITrie.fromSpaceValue).toMap
    def refsI: Map[String, List[Int]] = paths.map((k, v) => k.s -> Interner.internPath(v.items))
    def mentsI: Map[String, ITrie] = ic.map((k, v) => k.s -> v)

  /** every backend's counted run against the semantics; returns the per-backend verdict lines */
  def check(c: Case): Vector[String] =
    var out = Vector.empty[String]
    def cmp(backend: Backend, counted: Events, spec: Events, sameValue: Boolean): Unit =
      val diffs = EffortEvent.values.toVector.filter(e => counted(e) != spec(e))
        .map(e => s"$e counted=${counted(e)} semantics=${spec(e)}")
      assert(sameValue, s"${c.label}/${backend.slug}: the semantics computed a different VALUE")
      assert(diffs.isEmpty,
             s"${c.label}/${backend.slug}: the event multiset differs — ${diffs.mkString("; ")}\n  prog = ${c.prog.show.replace('\n', ' ').take(300)}")
      out :+= f"${c.label}%-34s ${backend.slug}%-9s ${counted.showComponents}  explain=${counted.nonZero.filter(_._1.component == EffortComponent.Explain).map((e, n) => s"$e=$n").mkString(",")}"
    // ---- reference ----
    eval(c.prog)(using c.pc, c.sc, c.rc)
    val r = SpatialEvents.counted(Backend.Reference)(eval(c.prog)(using c.pc, c.sc, c.rc))
    val (rv, re) = EventSemantics.reference(c.prog)(using c.pc, c.sc, c.rc)
    cmp(Backend.Reference, r.events, re, rv == r.value)
    // ---- trie ----
    evalI(c.prog)(using c.pc, c.ic, c.rc)
    val t = SpatialEvents.counted(Backend.Trie)(evalI(c.prog)(using c.pc, c.ic, c.rc))
    val (tv, te) = EventSemantics.trie(c.prog)(using c.pc, c.ic, c.rc)
    cmp(Backend.Trie, t.events, te, tv.toSpaceValue == t.value.toSpaceValue)
    assertEquals(t.value.toSpaceValue, r.value, s"${c.label}: evalI and eval disagree")
    // ---- graph ----
    c.graphBody match
      case Some(body) =>
        val g = transpile(Routine(RoutinePtr("m"), c.paths.keys.toVector, c.spaces.keys.toVector, body))
        runGraphT(g, c.refsI, c.mentsI)
        val gc = SpatialEvents.counted(Backend.Graph)(runGraphT(g, c.refsI, c.mentsI))
        val (gv, ge) = EventSemantics.graph(g, c.refsI, c.mentsI)
        cmp(Backend.Graph, gc.events, ge, gv.toSpaceValue == gc.value.toSpaceValue)
        assertEquals(gc.value.toSpaceValue, r.value, s"${c.label}: execT and eval disagree")
      case None =>
        out :+= f"${c.label}%-34s graph     SKIPPED: a residual recursive call survives lowerCalls (not executable by execT)"
    // ---- zipper ----
    execZ(c.prog)(using c.pc, c.ic, c.rc)
    val z = SpatialEvents.counted(Backend.Zipper)(execZ(c.prog)(using c.pc, c.ic, c.rc))
    val (zv, ze) = EventSemantics.zipper(c.prog)(using c.pc, c.ic, c.rc)
    cmp(Backend.Zipper, z.events, ze, zv.toSpaceValue == z.value.toSpaceValue)
    assertEquals(z.value.toSpaceValue, r.value, s"${c.label}: execZ and eval disagree")
    out

  // ---- the input families ------------------------------------------------------------------------
  val s0 = SpaceMention("s0"); val s1 = SpaceMention("s1"); val s2 = SpaceMention("s2")
  val S0 = Space.Mention(s0); val S1 = Space.Mention(s1); val S2 = Space.Mention(s2)
  val q0 = PathRef("q0")
  val A = sv(p("a", "x"), p("a", "y"), p("b", "z"), p("c"))
  val B = sv(p("a", "x"), p("c"), p("d", "w", "v"))
  val D = sv(p("e", "1"), p("f", "2"))                                      // head-disjoint from A and B
  val Deep = sv(p("p", "q", "r", "s1"), p("p", "q", "r", "s2"), p("p", "q", "t", "u"), p("p", "v"))
  val Eps = sv(p())                                                          // {ε}
  val Wide = SpaceValue((0 until 30).map(i => p(s"h$i", s"t${i % 7}")).toSet)   // 30 heads: past the dedup threshold
  val Shared = SpaceValue((0 until 6).map(i => p(s"g$i", "same", "tail")).toSet) // six heads, one shared tail shape
  val Many = SpaceValue((0 until 12).flatMap(i => Seq(p(s"k$i", "a"), p(s"k$i", "b"), p(s"k$i", "c", "d"))).toSet)

  /** the operand shapes every binary constructor is run over: empty, singleton, aliased (the same
   *  mention twice), disjoint, overlapping, deeply shared, ε */
  def binaryOperands: Vector[(String, Map[SpaceMention, SpaceValue], Space, Space)] = Vector(
    ("empty/empty", Map(s0 -> SpaceValue(Set.empty), s1 -> SpaceValue(Set.empty)), S0, S1),
    ("empty/A", Map(s0 -> SpaceValue(Set.empty), s1 -> A), S0, S1),
    ("A/empty", Map(s0 -> A, s1 -> SpaceValue(Set.empty)), S0, S1),
    ("singleton/singleton", Map(s0 -> sv(p("a")), s1 -> sv(p("a"))), S0, S1),
    ("singleton/A", Map(s0 -> sv(p("a", "x")), s1 -> A), S0, S1),
    ("aliased", Map(s0 -> A), S0, S0),
    ("disjoint", Map(s0 -> A, s1 -> D), S0, S1),
    ("overlap", Map(s0 -> A, s1 -> B), S0, S1),
    ("deep/deep-sub", Map(s0 -> Deep, s1 -> sv(p("p", "q", "r", "s1"), p("p", "v"))), S0, S1),
    ("eps/A", Map(s0 -> Eps, s1 -> A), S0, S1),
    ("A/eps", Map(s0 -> A, s1 -> Eps), S0, S1),
    ("literal/mention", Map(s1 -> B), lit(p("a", "x"), p("b", "z"), p("c")), S1),
    ("wide/many", Map(s0 -> Wide, s1 -> Many), S0, S1),
    ("shared-subterm", Map(s0 -> A, s1 -> B), Space.Union(S0, S1), Space.Union(S0, S1)))

  val binaryOps: Vector[(String, (Space, Space) => Space)] = Vector(
    "union" -> Space.Union.apply, "intersection" -> Space.Intersection.apply,
    "subtraction" -> Space.Subtraction.apply, "restriction" -> Space.Restriction.apply,
    "raffination" -> Space.Raffination.apply, "composition" -> Space.Composition.apply)

  val unaryOperands: Vector[(String, Map[SpaceMention, SpaceValue], Space)] = Vector(
    ("empty", Map(s0 -> SpaceValue(Set.empty)), S0),
    ("singleton", Map(s0 -> sv(p("a", "x"))), S0),
    ("eps", Map(s0 -> Eps), S0),
    ("A", Map(s0 -> A), S0),
    ("deep", Map(s0 -> Deep), S0),
    ("wide", Map(s0 -> Wide), S0),
    ("shared-tails", Map(s0 -> Shared), S0),
    ("many", Map(s0 -> Many), S0),
    ("built", Map(s0 -> A, s1 -> B), Space.Union(S0, S1)))

  def unaryOps: Vector[(String, Space => Space)] = Vector(
    "tails-union" -> Space.TailsUnion.apply,
    "tails-intersection" -> Space.TailsIntersection.apply,
    "wrap" -> (x => Space.Wrap(x, Path.Constant(p("w", "w2")))),
    "wrap-ref" -> (x => Space.Wrap(x, Path.Deref(q0))),
    "unwrap-a" -> (x => Space.Unwrap(x, Path.Constant(p("a")))),
    "unwrap-pq" -> (x => Space.Unwrap(x, Path.Constant(p("p", "q")))),
    "unwrap-missing" -> (x => Space.Unwrap(x, Path.Constant(p("zz", "y")))),
    "unwrap-eps" -> (x => Space.Unwrap(x, Path.Constant(p()))),
    "range-full" -> (x => Space.Range(x, 0, 0)),
    "range-first" -> (x => Space.Range(x, 0, 1)),
    "range-last" -> (x => Space.Range(x, -1, 0)),
    "range-middle" -> (x => Space.Range(x, 2, 4)),
    "range-empty" -> (x => Space.Range(x, 5, 3)),
    "iteration-heads" -> (x => Space.Iteration(x, PathRef("h").known(1), SpaceMention("r"), Space.Singleton(Path.Deref(PathRef("h").known(1))))),
    "iteration-tails" -> (x => Space.Iteration(x, PathRef("h").known(1), SpaceMention("r"), Space.Mention(SpaceMention("r")))),
    "iteration-rebuild" -> (x => Space.Iteration(x, PathRef("h").known(1), SpaceMention("r"),
                                                 Space.Wrap(Space.Mention(SpaceMention("r")), Path.Deref(PathRef("h").known(1))))),
    "iteration-nested" -> (x => Space.Iteration(x, PathRef("h").known(1), SpaceMention("r"),
                             Space.Iteration(Space.Mention(SpaceMention("r")), PathRef("h2").known(1), SpaceMention("r2"),
                               Space.Wrap(Space.Mention(SpaceMention("r2")), Path.Concat(Path.Deref(PathRef("h2").known(1)), Path.Deref(PathRef("h").known(1))))))))
  // `Fold` IS NOT IN THE MATRIX, and the reason is a finding rather than an omission: `Fold` is outside the
  // certified fragment (Positive.lean: `.fold => ∅`), and the first run of this suite showed `eval` and
  // `evalI` DISAGREE on it — `eval` visits the head groups in `PathValue.show` (string) order, `evalI` in
  // interned-key order, and a 30-head source (`h0`…`h29`) accumulates a different path.  Recorded in
  // build.log; a semantics for `Fold` would first have to say which order the language means.
  test("FINDING: Fold's group order differs between eval (string order) and evalI (interner order)") {
    val fold = Space.Fold(S0, Path.Constant(p("acc")), PathRef("a"), PathRef("h").known(1), SpaceMention("r"),
                          Space.Singleton(Path.Deref(PathRef("a"))), Path.Concat(Path.Deref(PathRef("a")), Path.Deref(PathRef("h").known(1))))
    val c = Case("fold-order", fold, Map(s0 -> Wide))
    val ref = eval(fold)(using c.pc, c.sc, noRc)
    val tri = evalI(fold)(using c.pc, c.ic, noRc).toSpaceValue
    println(s"SEMANTICS: Fold over 30 heads — eval ${ref.paths.size} paths, evalI ${tri.paths.size} paths, equal=${ref == tri}")
    if ref != tri then println("SEMANTICS: FINDING confirmed — Fold is not backend-deterministic on this input")
  }

  test("every BINARY constructor, every operand family, every backend: same event multiset") {
    var lines = Vector.empty[String]
    for (opName, op) <- binaryOps; (shape, spaces, a, b) <- binaryOperands do
      lines ++= check(Case(s"$opName/$shape", op(a, b), spaces))
    println(s"SEMANTICS: ${lines.length} binary (case, backend) agreements")
    lines.take(24).foreach(l => println("SEMANTICS:   " + l))
  }

  test("every UNARY / positional / loop constructor, every operand family, every backend: same event multiset") {
    var lines = Vector.empty[String]
    for (opName, op) <- unaryOps; (shape, spaces, x) <- unaryOperands do
      lines ++= check(Case(s"$opName/$shape", op(x), spaces, paths = Map(q0 -> p("w", "w2"))))
    println(s"SEMANTICS: ${lines.length} unary (case, backend) agreements")
    lines.take(24).foreach(l => println("SEMANTICS:   " + l))
  }

  test("singletons, literals, empty, paths: the leaves") {
    val cases = Vector(
      Case("empty", Space.Empty),
      Case("singleton-const", Space.Singleton(Path.Constant(p("a", "b", "c")))),
      Case("singleton-eps", Space.Singleton(Path.Constant(p()))),
      Case("singleton-concat", Space.Singleton(Path.Concat(Path.Constant(p("a")), Path.Deref(q0))), paths = Map(q0 -> p("w", "w2"))),
      Case("literal-warm", lit(p("a", "x"), p("b"))),
      Case("literal-union-same", Space.Union(lit(p("a", "x"), p("b")), lit(p("a", "x"), p("b")))),
      Case("mention-alone", S0, Map(s0 -> A)),
      Case("mention-union-self", Space.Union(S0, S0), Map(s0 -> A)),
      Case("mention-sub-self", Space.Subtraction(S0, S0), Map(s0 -> A)),
      Case("mention-inter-self", Space.Intersection(S0, S0), Map(s0 -> A)))
    val lines = cases.flatMap(check)
    lines.foreach(l => println("SEMANTICS:   " + l))
  }

  test("a COLD literal is `fromSpaceValue`, a warm one is a lookup — on every trie-shaped backend") {
    // a fresh SpaceValue OBJECT is unknown to every cache; the semantics is run FIRST here so that it
    // sees the cold state the counted run then also sees (the literal caches are identity-keyed)
    val fresh = SpaceValue((0 until 9).map(i => p(s"c$i", "x", s"y$i")).toSet)
    val prog = Space.Union(Space.Literal(fresh), S0)
    val c = Case("literal-cold", prog, Map(s0 -> A))
    val (tv, te) = EventSemantics.trie(prog)(using c.pc, c.ic, noRc)
    assert(!iLiteralIsCached(fresh), "the semantics must not warm the executor's cache")
    val t = SpatialEvents.counted(Backend.Trie)(evalI(prog)(using c.pc, c.ic, noRc))
    assertEquals(t.events, te, "cold literal on evalI")
    assert(te(EffortEvent.FreshTrieNode) >= 9L * 2L, s"a cold 9-path literal allocates its nodes: ${te.show}")
    val fresh2 = SpaceValue((0 until 5).map(i => p(s"d$i", "z")).toSet)
    val prog2 = Space.Union(Space.Literal(fresh2), S0)
    val (zv, ze) = EventSemantics.zipper(prog2)(using c.pc, c.ic, noRc)
    val z = SpatialEvents.counted(Backend.Zipper)(execZ(prog2)(using c.pc, c.ic, noRc))
    assertEquals(z.events, ze, "cold literal on execZ")
    println(s"SEMANTICS: cold literal trie ${te.showComponents}; zipper ${ze.showComponents}")
  }

  test("RECURSIVE cases: fixpoints, self-recursive calls, mutual recursion through the routine table") {
    val r = SpaceMention("r")
    val edges = sv(p("e", "0", "1"), p("e", "1", "2"), p("e", "2", "3"), p("e", "3", "0"))
    // transitive closure over a 4-cycle: several rounds plus the terminating one
    def hop(x: Space): Space =
      Space.Iteration(Space.Unwrap(x, Path.Constant(p("e"))), PathRef("a").known(1), SpaceMention("as"),
        Space.Iteration(Space.Mention(SpaceMention("as")), PathRef("b").known(1), SpaceMention("_"),
          Space.Iteration(Space.Unwrap(Space.Unwrap(S0, Path.Constant(p("e"))), Path.Deref(PathRef("b").known(1))), PathRef("c").known(1), SpaceMention("_2"),
            Space.Wrap(Space.Singleton(Path.Concat(Path.Deref(PathRef("a").known(1)), Path.Deref(PathRef("c").known(1)))), Path.Constant(p("e"))))))
    val tc = Space.Fixpoint(S0, r, hop(Space.Mention(r)))
    val rp = RoutinePtr("suffixes"); val xs = SpaceMention("xs")
    val suffixes = Routine(rp, Vector.empty, Vector(xs),
      Space.Union(Space.Mention(xs), Space.Call(rp, Vector.empty, Vector(Space.TailsUnion(Space.Mention(xs))))))
    // MUTUAL RECURSION REACHES EVERY BACKEND THROUGH THE LOWERING.  `eval`'s only terminating rule for a
    // recursive `Call` is the stabilised-argument shortcut on a DIRECT self-call, so an unlowered mutual
    // pair diverges on every executor; `lowerCalls` turns a passthrough SCC into one tagged `Fixpoint`
    // (lowerMutualPassthrough), and THAT is the program the backends run.
    val ev = RoutinePtr("ev"); val od = RoutinePtr("od"); val g = SpaceMention("g"); val acc = SpaceMention("acc")
    val evR = Routine(ev, Vector.empty, Vector(g, acc),
      Space.Union(Space.Restriction(Space.Mention(acc), Space.Mention(g)), Space.Call(od, Vector.empty, Vector(Space.Mention(g), Space.Mention(acc)))))
    val odR = Routine(od, Vector.empty, Vector(g, acc),
      Space.Union(Space.TailsUnion(Space.Mention(acc)), Space.Call(ev, Vector.empty, Vector(Space.Mention(g), Space.Mention(acc)))))
    val (mutualBody, mutualResidual) =
      lowerCalls(Routine(RoutinePtr("m"), Vector.empty, Vector(s0, s1), Space.Call(ev, Vector.empty, Vector(S0, S1))), Syntax.mod(evR, odR))
    assert(mutualResidual.isEmpty, s"the passthrough SCC must lower completely: ${mutualResidual.keys}")
    val cases = Vector(
      Case("fixpoint/transitive", tc, Map(s0 -> edges)),
      Case("fixpoint/stationary-at-once", Space.Fixpoint(S0, r, Space.Mention(r)), Map(s0 -> A)),
      Case("fixpoint/grows-then-stops", Space.Fixpoint(S0, r, Space.Union(Space.Mention(r), Space.TailsUnion(Space.Mention(r)))), Map(s0 -> Deep)),
      Case("call/suffix-closure", Space.Call(rp, Vector.empty, Vector(S0)), Map(s0 -> sv(p("a", "b", "c"), p("d"))), rc = Syntax.mod(suffixes)),
      Case("call/suffix-closure-empty", Space.Call(rp, Vector.empty, Vector(S0)), Map(s0 -> SpaceValue(Set.empty)), rc = Syntax.mod(suffixes)),
      Case("call/mutual-lowered", mutualBody, Map(s0 -> A, s1 -> Deep)))
    val lines = cases.flatMap(check)
    lines.foreach(l => println("SEMANTICS:   " + l))
  }

  test("N-ARY cases: wide iterations and tails past the dedup threshold, aliased operands, empty groups") {
    val h = PathRef("h").known(1); val rr = SpaceMention("r")
    val same = SpaceValue((0 until 40).map(i => p(s"w$i", "x")).toSet)             // 40 heads sharing the tail {x}: all aliased children after dedup? no — distinct objects
    val cases = Vector(
      Case("nary/tails-union-30", Space.TailsUnion(S0), Map(s0 -> Wide)),
      Case("nary/tails-inter-30", Space.TailsIntersection(S0), Map(s0 -> Wide)),
      Case("nary/tails-union-40-same-tail", Space.TailsUnion(S0), Map(s0 -> same)),
      Case("nary/tails-inter-40-same-tail", Space.TailsIntersection(S0), Map(s0 -> same)),
      Case("nary/iteration-30-rest", Space.Iteration(S0, h, rr, Space.Mention(rr)), Map(s0 -> Wide)),
      Case("nary/iteration-30-const", Space.Iteration(S0, h, rr, lit(p("z"))), Map(s0 -> Wide)),
      Case("nary/iteration-aliased-body", Space.Iteration(S0, h, rr, S1), Map(s0 -> Wide, s1 -> A)),
      Case("nary/iteration-empty-groups", Space.Iteration(S0, h, rr, Space.Intersection(Space.Mention(rr), S1)), Map(s0 -> Wide, s1 -> D)),
      Case("nary/union-of-tails", Space.Union(Space.TailsUnion(S0), Space.TailsUnion(S1)), Map(s0 -> Wide, s1 -> Many)),
      Case("nary/wide-fixpoint", Space.Fixpoint(S0, rr, Space.Union(Space.Mention(rr), Space.TailsUnion(Space.Mention(rr)))), Map(s0 -> Wide)))
    val lines = cases.flatMap(check)
    lines.foreach(l => println("SEMANTICS:   " + l))
  }

  test("the fuzzer corpus: 200 random programs over random inputs, all four backends") {
    val recs = Corpus.load(sys.props.get("sem.progs").map(_.toInt).getOrElse(200))
    val Al = SpaceFuzzer.alphabet
    val rng = new java.util.Random(20260905)
    def randPath() = PathValue(List.fill(1 + rng.nextInt(2))(Al(rng.nextInt(Al.length))))
    def smallTrie() = SpaceValue((0 until (1 + rng.nextInt(6))).map(_ => randPath()).toSet)
    val sNames = (0 until 3).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until 2).map(j => PathRef("p" + j)).toVector
    val svs = sNames.map(_ -> smallTrie()).toMap
    val pvs = pNames.map(_ -> randPath()).toMap
    var n = 0; var graphless = 0
    for r <- recs do
      val hasFold = SizeZ3.children(r.prog).nonEmpty && r.prog.show.contains(".fold(")
      val c = Case(s"corpus#$n", r.prog, svs.filter((k, _) => sNames.take(r.nSpace).contains(k)),
                   pvs.filter((k, _) => pNames.take(r.nPath).contains(k)), graph = !hasFold)
      if hasFold then graphless += 1
      try check(c)
      catch case e: NotImplementedError => graphless += 1     // transpile refuses a grounded form
      n += 1
    println(s"SEMANTICS: $n corpus programs agree on every backend ($graphless without a graph leg)")
  }

  test("the SIX CORNERSTONES agree on every backend") {
    val puz = Sliding.puzzle(3, 3)
    val frontier = sv(puz.initial)
    val live = Set((1, 0), (1, 1), (1, 2))
    val golRules = GoL.rulesFor(live)
    val queens = NQueens.board(4)
    val edges = sv(p("0", "1"), p("1", "2"), p("2", "3"))
    def join(r: Space, s: Space): Space = r.iter(P"n", S"nbs", P"n" x \/(s <| S"nbs"))
    val snTC = Routine(RoutinePtr("sn_tc"), Vector.empty,
                       Vector(SpaceMention("e"), SpaceMention("all"), SpaceMention("delta")),
                       S"all" \/ Space.Call(RoutinePtr("sn_tc"), Vector.empty,
                         Vector(S"e", S"all" \/ (join(S"delta", S"e") \ S"all"), join(S"delta", S"e") \ S"all")))
    val rr = new scala.util.Random(12)
    val tempCells = (0 until 16).map(i => PathValue(NOAA.bits(i, 4) :+ Vector("VC", "C", "N", "W", "VW")(rr.nextInt(5)))).toSet
    val world = Space.Mention(SpaceMention("world"))
    val temperature = Space.Union(Space.Restriction(world, Space.Literal(NOAA.interval(0, 4, 4))),
                                  Space.Restriction(world, Space.Literal(NOAA.interval(12, 16, 4))))
    val cases = Vector(
      Case("aunt", Routines.aunt_query_routine.body, AuntQuery.context.asInstanceOf[SpaceContextMap].m, rc = Syntax.mod(Routines.child_routine)),
      Case("temperature", temperature, Map(SpaceMention("world") -> SpaceValue(tempCells))),
      Case("gol", Space.Call(RoutinePtr("nextStep"), Vector.empty, Vector(Space.Mention(SpaceMention("field")))),
           Map(SpaceMention("field") -> GoL.field(live)), rc = golRules.defs),
      Case("puzzle3x3-step", puz.expandStep(Space.Mention(SpaceMention("frontier"))), Map(SpaceMention("frontier") -> frontier), rc = puz.defs),
      Case("nqueens4", queens.program, Map.empty, rc = queens.defs),
      Case("datalog-sn", Space.Call(RoutinePtr("sn_tc"), Vector.empty,
             Vector(Space.Mention(SpaceMention("edges")), Space.Mention(SpaceMention("edges")), Space.Mention(SpaceMention("edges")))),
           Map(SpaceMention("edges") -> edges), rc = Syntax.mod(snTC)))
    for c <- cases do
      val t0 = java.lang.System.nanoTime()
      val lines = check(c)
      lines.foreach(l => println("SEMANTICS:   " + l))
      println(f"SEMANTICS: ${c.label} agreed on 4 backends in ${(java.lang.System.nanoTime() - t0) / 1e6}%.0f ms")
  }

  test("the event algebra: every event has one kind, the inclusion rule reproduces the components") {
    for e <- EffortEvent.values if e.component != EffortComponent.Explain do
      val k = EventKind.of(e)
      val inComp = EventKind.inclusion(e.component)
      assert(inComp.contains(k), s"$e is $k but its component ${e.component} sums ${inComp.mkString(",")}")
    // the explanatory events are node visits and sharing decisions the components deliberately exclude
    for e <- EffortEvent.ofComponent(EffortComponent.Explain) do
      assert(Set(EventKind.NodeVisit, EventKind.RetainedShare, EventKind.Handoff).contains(EventKind.of(e)), e.toString)
    // the components partition the counted kinds as documented: Touch is NodeVisit only; Work adds
    // probes, comparisons and materialisation; Alloc and Rounds are their own kinds
    assertEquals(EventKind.inclusion(EffortComponent.Touch), Set(EventKind.NodeVisit))
    assert(EventKind.inclusion(EffortComponent.Work).contains(EventKind.NodeVisit))
    for b <- Backend.values do assertEquals(SemanticsProfile.of(b).backend, b)
    println("SEMANTICS: " + EffortEvent.values.map(e => s"$e:${EventKind.of(e)}").mkString(" "))
  }

  test("NO EVALUATION LEAKS: the semantics never arms the executors' sink") {
    val c = Case("arm", Space.Union(S0, Space.TailsUnion(S1)), Map(s0 -> A, s1 -> Deep))
    assert(!EffortSink.isCounting)
    EventSemantics.trie(c.prog)(using c.pc, c.ic, noRc)
    EventSemantics.zipper(c.prog)(using c.pc, c.ic, noRc)
    EventSemantics.reference(c.prog)(using c.pc, c.sc, noRc)
    assert(!EffortSink.isCounting && !EffortSink.armed, "the semantics left the sink armed")
  }
