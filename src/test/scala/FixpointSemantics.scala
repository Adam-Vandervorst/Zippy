package morkl

import munit.FunSuite

/** WHAT `Space.Fixpoint` DENOTES — the regression that pins the one premise the tree used to be
 *  missing.
 *
 *  `terminating/fixpoint_is_lfp.smt2` (O1) proves that a Kleene iteration reaches
 *  `lfp_{⊇init} F` under TWO hypotheses: **monotone `F`** and **`init ⊆ F(init)`**.  The second is
 *  called load-bearing there and asserted at :182, and the file carries a MACHINE-CHECKED
 *  monotone-but-non-inflationary counterexample at :47-50:
 *
 *      F(X) = {b if a ∈ X} ∪ {c if a ∈ X and b ∈ X},    init = {a}
 *
 *  `F` is monotone, so every syntactic monotonicity gate in the tree (`monotoneInMention`,
 *  `MORKL.mono`, `MORKL.monoIn`) accepts it — yet
 *
 *      iterating F and accumulating       ⋃_{j≤n} Fʲ(init) = {a, b}
 *      the least post-fixpoint above init                  = {a, b, c}
 *
 *  and the emitted FOL/egg models are the SECOND value.  Before this was fixed, five executors
 *  computed the FIRST while the certificates asserted the second, and the only gate in front of
 *  the gap was monotonicity — which the counterexample satisfies.
 *
 *  THE FIX, AND WHAT THIS FILE CHECKS.  Every executor now iterates the INFLATIONARY operator
 *  `cur := cur ∪ F(cur)`.  Its chain ascends whatever `F` is, so `init ⊆ (init ∪ F(init))` holds by
 *  construction and monotonicity — which is what buys LEASTNESS — becomes the one real side
 *  condition.  Concretely:
 *
 *    1. the counterexample is LIVE: it passes every monotonicity gate, and the old loop shape and
 *       the specification really do disagree on it (so this is not a vacuous regression);
 *    2. the least post-fixpoint is computed HERE, INDEPENDENTLY, by brute force over the finite
 *       universe — "the least `Y ⊇ init` with `F(Y) ⊆ Y`", straight from the definition, with no
 *       iteration of any kind;
 *    3. all five executors (`eval`, `exec`, `execT`, `evalT`, `evalI`) return that value;
 *    4. the emitted FOL model agrees with the executors and DISTINGUISHES them from the old
 *       accumulator answer: z3/vampire prove `Fixpoint ≡ {a,b,c}` and REFUTE `Fixpoint ≡ {a,b}`.
 *       (4) is what makes this a differential and not a restatement: the same file, run against
 *       the pre-fix executor output, is refutable.
 *    5. termination is not an accident of this example: iterating `F` alone DIVERGES on a plain
 *       transitive closure over a 2-cycle, and the inflationary loop converges.
 */
class FixpointSemantics extends FunSuite:
  import Space.*
  // the FOL leg runs four prover invocations with real budgets
  override val munitTimeout = scala.concurrent.duration.Duration(10, "min")

  // ------------------------------------------------------------------------------------------
  // the counterexample, as a Space program
  // ------------------------------------------------------------------------------------------
  private def pv(s: String): PathValue = PathValue(List(s))
  private def lit(xs: String*): Space = Literal(SpaceValue(xs.map(pv).toSet))
  private def sv(xs: String*): SpaceValue = SpaceValue(xs.map(pv).toSet)
  private val a = Path.Constant(pv("a"))
  private val b = Path.Constant(pv("b"))
  private val c = Path.Constant(pv("c"))

  private val rec = SpaceMention("X")
  private val X: Space = Mention(rec)

  /** `{ε}` when `k ∈ X`, `∅` otherwise — `Intersection` then `Unwrap` is the set-algebra `if`. */
  private def has(k: Path, key: String): Space = Unwrap(Intersection(X, Literal(sv(key))), k)

  /** F(X) = {b if a∈X} ∪ {c if a∈X ∧ b∈X}.  Every occurrence of `X` sits under
   *  Intersection/Unwrap/Wrap only, so `F` is syntactically MONOTONE in `X`. */
  private val body: Space =
    Union(Wrap(has(a, "a"), b),
          Wrap(Intersection(has(a, "a"), has(b, "b")), c))

  private val prog: Space = Fixpoint(lit("a"), rec, body)

  private val universe = List("a", "b", "c")
  private val initV = sv("a")

  /** `F` as a plain function on `SpaceValue`, by evaluating the body with `X` bound. */
  private def F(x: SpaceValue): SpaceValue =
    eval(body)(using PathContextMap(Map.empty), SpaceContextMap(Map(rec -> x)), PartialFunction.empty)

  /** THE SPECIFICATION, BRUTE-FORCED.  The least `Y ⊇ init` with `F(Y) ⊆ Y`, found by enumerating
   *  every subset of the universe — no iteration, no chain, no accumulator: this is the definition
   *  the FOL axioms and the egg `Fix` rules encode, computed a completely different way. */
  private lazy val leastPostFixpoint: SpaceValue =
    val subsets = universe.toSet.subsets().map(s => SpaceValue(s.map(pv))).toList
    val post = subsets.filter(y => initV.paths.subsetOf(y.paths) && F(y).paths.subsetOf(y.paths))
    assert(post.nonEmpty, "the counterexample has no post-fixpoint above init — the model is wrong")
    val least = post.minBy(_.paths.size)
    // "least" must mean BELOW EVERY post-fixpoint, not merely smallest — check it, do not assume it
    assert(post.forall(y => least.paths.subsetOf(y.paths)),
           s"no LEAST post-fixpoint exists among $post — the counterexample is not a lattice example")
    least

  /** THE OLD LOOP SHAPE, kept here on purpose: iterate `F`, accumulate on the side, stop at the
   *  first repeat.  This is what `eval`/`exec`/`execT`/`evalT`/`evalI` all used to do. */
  private def accumulateIteratingF(init: SpaceValue): SpaceValue =
    var cur = init
    var acc = init
    var stop = false
    var guard = 0
    while !stop && guard < 1000 do
      guard += 1
      val nxt = F(cur)
      if nxt == cur then stop = true else { acc = SpaceValue(acc.paths union nxt.paths); cur = nxt }
    assert(stop, "the old loop shape did not converge on the counterexample")
    acc

  // ------------------------------------------------------------------------------------------
  // (1) the counterexample is LIVE
  // ------------------------------------------------------------------------------------------
  test("the counterexample passes EVERY syntactic monotonicity gate in the tree") {
    assert(AgnosticPipeline.monotoneInMention(body, rec),
           "monotoneInMention rejects the counterexample — then it is not a counterexample to " +
           "'monotonicity is sufficient' and fixpoint_is_lfp.smt2:47-50 needs a different witness")
    // the same judgement as made by the two lowering gates, so no gate is a hidden extra premise
    val r = Routine(RoutinePtr("cx"), Vector.empty, Vector(rec), Union(X, Call(RoutinePtr("cx"), Vector.empty, Vector(body))))
    assert(asFixpointGeneral(r.name, r.refs, r.mentions, r.body).isDefined,
           "asFixpointGeneral's monoIn rejects the counterexample body")
  }

  test("F is NOT inflationary at init — the missing premise, exhibited") {
    assert(!initV.paths.subsetOf(F(initV).paths),
           s"init ⊆ F(init) actually holds here (F(init) = ${F(initV)}), so the second premise of " +
           "fixpoint_is_lfp.smt2 is not being exercised")
  }

  test("the old loop shape and the SPECIFICATION disagree: {a,b} vs {a,b,c}") {
    assertEquals(leastPostFixpoint, sv("a", "b", "c"), "brute-forced least post-fixpoint")
    assertEquals(accumulateIteratingF(initV), sv("a", "b"), "the pre-fix executors' answer")
    assertNotEquals(accumulateIteratingF(initV), leastPostFixpoint,
                    "if these agreed there would be nothing to regress")
  }

  // ------------------------------------------------------------------------------------------
  // (3) every executor denotes the least post-fixpoint
  // ------------------------------------------------------------------------------------------
  test("all five executors return the least post-fixpoint (not the accumulator)") {
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map.empty)
    given PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
    val want = leastPostFixpoint
    assertEquals(eval(prog), want, "MORKL.eval")
    assertEquals(evalT(prog).toSpaceValue, want, "Trie.evalT")
    assertEquals(evalI(prog).toSpaceValue, want, "IntTrie.evalI")
    val g = transpile(Routine(RoutinePtr("cx"), Vector.empty, Vector.empty, prog))
    assertEquals(runGraph(g), want, "MORKL.exec (op-graph, Space values)")
    assertEquals(runGraphT(g).toSpaceValue, want, "GraphExec.execT (op-graph, ITrie values)")
    assertEquals(runGraphT(optimize(g)).toSpaceValue, want, "GraphExec.execT after optimize")
  }

  // ------------------------------------------------------------------------------------------
  // (5) the inflationary loop TERMINATES where iterating F alone cycles forever
  // ------------------------------------------------------------------------------------------
  /** G(X) = {b if a∈X} ∪ {a if b∈X} — monotone, and its pure-F chain from {a} is the 2-CYCLE
   *  {a}, {b}, {a}, {b}, … with NO stationary point at all.  Part (iv) of fixpoint_is_lfp.smt2
   *  says a stationary index must exist over a finite universe; it does so for the INFLATIONARY
   *  chain, and this is the witness that the claim is false for the pure-F chain.  Iterating F
   *  alone does not merely give a wrong answer here — it does not terminate. */
  private val swapBody: Space =
    Union(Wrap(has(a, "a"), b), Wrap(has(b, "b"), a))
  private val swap: Space = Fixpoint(lit("a"), rec, swapBody)

  test("a monotone body whose pure-F chain CYCLES: the executors still converge") {
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map.empty)
    given PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
    assert(AgnosticPipeline.monotoneInMention(swapBody, rec), "the swap body must be monotone too")
    // the pure-F chain has NO stationary point: it alternates forever
    def step(x: SpaceValue) =
      eval(swapBody)(using PathContextMap(Map.empty), SpaceContextMap(Map(rec -> x)), PartialFunction.empty)
    val chain = List.iterate(sv("a"), 8)(step)
    assert(chain.sliding(2).forall { case List(x, y) => x != y; case _ => true },
           s"expected a chain with no stationary point, got $chain")
    assertEquals(chain(1), sv("b")); assertEquals(chain(2), sv("a"))   // it really is the 2-cycle
    // the inflationary loop converges, and to the least post-fixpoint {a,b}
    val want = sv("a", "b")
    assertEquals(eval(swap), want, "MORKL.eval")
    assertEquals(evalI(swap).toSpaceValue, want, "IntTrie.evalI")
    assertEquals(evalT(swap).toSpaceValue, want, "Trie.evalT")
    val g = transpile(Routine(RoutinePtr("swap"), Vector.empty, Vector.empty, swap))
    assertEquals(runGraph(g), want, "MORKL.exec")
    assertEquals(runGraphT(g).toSpaceValue, want, "GraphExec.execT")
  }

  // ------------------------------------------------------------------------------------------
  // (4) the emitted FOL model agrees with the executors and REFUTES the old answer
  // ------------------------------------------------------------------------------------------
  test("the emitted FOL fixpoint model proves ≡{a,b,c} and REFUTES ≡{a,b}") {
    val z3 = Tools.z3.path
    val vampire = Tools.vampire.path
    Loaders.note(s"[fixpoint-gate] tools: ${Tools.report}")
    assume(z3.isDefined || vampire.isDefined,
           s"neither prover available — ${Tools.z3.missing}; ${Tools.vampire.missing}")
    val dir = new java.io.File(Loaders.repoRoot, "proofs/pipeline/fixpoint-gate")
    dir.mkdirs()

    // THROUGH THE SINK (0.3).  The returned file is the one the provers are pointed at, so in
    // VERIFY mode they check exactly the bytes that were compared against the committed artifact.
    def emit(name: String, other: Space, header: String): java.io.File =
      ArtifactSink.write(new java.io.File(dir, name),
        header + AgnosticPipeline.smtAgnostic(s"fixpoint_is_lfp counterexample — $name", prog, other))

    def z3Says(f: java.io.File): String =
      z3.map { bin =>
        val p = new ProcessBuilder(bin, "-T:60", f.getPath).redirectErrorStream(true).start()
        val out = new String(p.getInputStream.readAllBytes()); p.waitFor()
        out.linesIterator.map(_.trim).filter(l => l == "unsat" || l == "sat" || l == "unknown" || l == "timeout")
          .toList.lastOption.getOrElse(out.take(200))
      }.getOrElse("ABSENT")

    def vampireSays(f: java.io.File): String =
      vampire.map { bin =>
        val p = new ProcessBuilder(bin, "--input_syntax", "smtlib2", "-t", "60s", f.getPath)
          .redirectErrorStream(true).start()
        val out = new String(p.getInputStream.readAllBytes()); p.waitFor()
        if out.contains("Refutation found") then "refuted"
        else if out.contains("Satisfiable") || out.contains("Finite Model Found") then "model"
        else "no-verdict"
      }.getOrElse("ABSENT")

    val good = emit("lfp_agrees.smt2", Literal(leastPostFixpoint),
      """; THE POSITIVE SIDE of the fixpoint_is_lfp.smt2:47-50 differential.  The FIRST-CLASS
        |; `Fixpoint` denotation (post-fixpoint axioms + Park induction, EquivPipeline.AgSmt.fixSym)
        |; is asked to equal {a,b,c} — the brute-forced least post-fixpoint above init, which is
        |; ALSO what every executor now returns.  Expected: unsat / Refutation found.
        |""".stripMargin)
    val bad = emit("accumulator_refuted.smt2", Literal(accumulateIteratingF(initV)),
      """; THE NEGATIVE SIDE.  The same denotation is asked to equal {a,b} — the value the PRE-FIX
        |; executors returned (iterate F, accumulate on the side, stop at the first repeat).  This
        |; must NOT be provable: it is the exact gap monotonicity alone does not close.  Expected:
        |; NOT unsat (z3 sat/unknown, vampire no refutation).  Were an executor to go back to
        |; iterating F alone, THIS file would be the certificate it violates.
        |""".stripMargin)

    val (gz, gv) = (z3Says(good), vampireSays(good))
    val (bz, bv) = (z3Says(bad), vampireSays(bad))
    Loaders.note(s"[fixpoint-gate] lfp_agrees: z3=$gz vampire=$gv | accumulator_refuted: z3=$bz vampire=$bv")

    assert(gz == "unsat" || gv == "refuted",
           s"the first-class Fixpoint model does NOT prove equality with the least post-fixpoint " +
           s"{a,b,c} (z3=$gz, vampire=$gv) — the encoding and the executors have drifted apart")
    assert(bz != "unsat" && bv != "refuted",
           s"the first-class Fixpoint model PROVES equality with the accumulator answer {a,b} " +
           s"(z3=$bz, vampire=$bv) — the differential is vacuous, so it cannot catch a regression")

    statusRows ++= Vector(
      s"lfp_agrees.smt2\t$gz\t$gv\tunsat/refuted\t${if gz == "unsat" || gv == "refuted" then "PROVED" else "FAILED"}",
      s"accumulator_refuted.smt2\t$bz\t$bv\tNOT unsat/refuted\t${if bz != "unsat" && bv != "refuted" then "SEPARATED" else "FAILED"}")
    writeGateStatus()
  }

  // ------------------------------------------------------------------------------------------
  // (4b) THE DECIDABLE TWIN — a countermodel, not a timeout
  // ------------------------------------------------------------------------------------------
  /** The ∀-path FOL files above give the RIGHT verdicts, but the negative one comes back `timeout`
   *  rather than `sat`: models of an extensional infinite path set are not something either prover
   *  builds (the same limitation `unroll_vs_kleene.smt2` records, and the reason its fourth section
   *  re-runs its claims in a decidable `(_ BitVec 3)` encoding).  A timeout is the ABSENCE of a
   *  proof, not a semantic separation, so the differential is repeated here over the FINITE universe
   *  the counterexample actually lives in — a 3-bit set over {a,b,c}, one bit per element — where
   *  everything is decidable and the verdicts are decisive:
   *
   *    (i)   axioms ∧ fix ≠ {a,b,c}   UNSAT     the axioms PIN the least post-fixpoint;
   *    (ii)  axioms ∧ fix =  {a,b}    UNSAT     the pre-fix executors' answer is REFUTED by the very
   *                                             axioms the certificates use — it is not merely
   *                                             unproven, it is inconsistent with them;
   *    (iii) axioms alone             SAT       and the model is fix = {a,b,c}: the axiom set is
   *                                             NON-VACUOUS, so (i) and (ii) mean what they say.
   *
   *  This is hand-written on purpose: it is a second, independent encoding of the same claim, so a
   *  bug in the Space→SMT emitter cannot make both agree. */
  test("decidable (BitVec 3) twin: the accumulator answer is REFUTED and the axioms are non-vacuous") {
    val z3 = Tools.z3.path
    assume(z3.isDefined, Tools.z3.missing)
    val dir = new java.io.File(Loaders.repoRoot, "proofs/pipeline/fixpoint-gate"); dir.mkdirs()

    // sets over {a,b,c} as (_ BitVec 3): bit 0 = a, bit 1 = b, bit 2 = c.  subset(x,y) := x|y = y.
    val common =
      """; DECIDABLE TWIN of the fixpoint_is_lfp.smt2:47-50 counterexample.  A set over {a,b,c} is a
        |; 3-bit vector (bit0=a, bit1=b, bit2=c); `subset x y` is `x|y = y`.  EVERYTHING here is
        |; decidable and quantifier-free apart from one bounded ∀ over BitVec 3, so a `sat` answer
        |; comes with a MODEL and an `unsat` answer is a refutation — no timeouts, no `unknown`.
        |;
        |;   F(X) = {b if a∈X} ∪ {c if a∈X and b∈X}          init = {a}
        |;
        |; F is MONOTONE and NOT inflationary at init, which is exactly the configuration in which
        |; monotonicity alone fails to make an iteration reach the least post-fixpoint.
        |(define-fun sub ((x (_ BitVec 3)) (y (_ BitVec 3))) Bool (= (bvor x y) y))
        |(define-fun hasA ((x (_ BitVec 3))) Bool (= (bvand x #b001) #b001))
        |(define-fun hasB ((x (_ BitVec 3))) Bool (= (bvand x #b010) #b010))
        |(define-fun F ((x (_ BitVec 3))) (_ BitVec 3)
        |  (bvor (ite (hasA x) #b010 #b000) (ite (and (hasA x) (hasB x)) #b100 #b000)))
        |(define-fun init () (_ BitVec 3) #b001)
        |(declare-const fx (_ BitVec 3))
        |; the two POST-FIXPOINT axioms the emitter writes (AgSmt.fixSym).  In this DECIDABLE twin the
        |; three clauses DEFINE `fx` as the least post-fixpoint (the domain is finite, so the definition
        |; is a constraint z3 decides) — hence the DEFINITION markers scripts/check_asserts.py reads.
        |; DEFINITION
        |(assert (sub init fx))
        |; DEFINITION
        |(assert (sub (F fx) fx))
        |; PARK INDUCTION, with the candidate UNIVERSALLY quantified — so `least` really is least
        |; DEFINITION
        |(assert (forall ((y (_ BitVec 3))) (=> (and (sub init y) (sub (F y) y)) (sub fx y))))
        |""".stripMargin

    def ask(name: String, goal: String, header: String): String =
      val f = ArtifactSink.write(new java.io.File(dir, name), header + common + goal)
      val p = new ProcessBuilder(z3.get, "-T:30", f.getPath).redirectErrorStream(true).start()
      val out = new String(p.getInputStream.readAllBytes()); p.waitFor()
      out.linesIterator.map(_.trim).filter(l => Set("sat", "unsat", "unknown", "timeout")(l))
        .toList.headOption.getOrElse(out.take(300))

    val pinned = ask("bv_lfp_pinned.smt2",
      "(assert (not (= fx #b111)))   ; is {a,b,c} FORCED?\n(check-sat)\n",
      "; (i) the axioms PIN fix = {a,b,c}.  Expected: unsat.\n")
    val refuted = ask("bv_accumulator_refuted.smt2",
      "(assert (= fx #b011))         ; the PRE-FIX executors' answer {a,b}\n(check-sat)\n",
      "; (ii) the pre-fix accumulator answer {a,b} is INCONSISTENT with the axioms.  Expected: unsat.\n" +
      "; This is the decisive form of the differential: not `we cannot prove {a,b}`, but `{a,b} is\n" +
      "; refuted`.  It fails the moment an executor goes back to iterating F alone.\n")
    val nonvacuous = ask("bv_nonvacuity.smt2",
      "(check-sat)\n(get-value (fx))   ; expect #b111\n",
      "; (iii) NON-VACUITY: the axiom set has a MODEL, so (i) and (ii) are not artefacts of an\n" +
      "; inconsistent theory.  Expected: sat, with fx = #b111.\n")

    Loaders.note(s"[fixpoint-gate] decidable twin: pinned=$pinned refuted=$refuted nonvacuous=$nonvacuous")
    assertEquals(pinned, "unsat",
      "the decidable axioms do NOT force fix = {a,b,c} — the encoding is weaker than the executors")
    assertEquals(refuted, "unsat",
      "the decidable axioms ADMIT fix = {a,b} — then the pre-fix executor answer is consistent with " +
      "the certificates and the whole differential is empty")
    assertEquals(nonvacuous, "sat",
      "the decidable axiom set is UNSATISFIABLE — every verdict above would then be vacuous")

    statusRows ++= Vector(
      s"bv_lfp_pinned.smt2\t$pinned\t-\tunsat\t${if pinned == "unsat" then "PROVED" else "FAILED"}",
      s"bv_accumulator_refuted.smt2\t$refuted\t-\tunsat\t${if refuted == "unsat" then "REFUTED" else "FAILED"}",
      s"bv_nonvacuity.smt2\t$nonvacuous\t-\tsat\t${if nonvacuous == "sat" then "NON-VACUOUS" else "FAILED"}")
    writeGateStatus()
  }

  // 0.3 — THE GOLDEN-FILE GATE, last so both prover legs above have written.
  test("every committed fixpoint-gate artifact matches what this suite produces") {
    ArtifactSink.assertClean("morkl.FixpointSemantics")
  }

  // the gate's own status table, appended to by both prover legs above
  private val statusRows = scala.collection.mutable.ArrayBuffer.empty[String]
  private def writeGateStatus(): Unit =
    val dir = new java.io.File(Loaders.repoRoot, "proofs/pipeline/fixpoint-gate")
    ArtifactSink.write(new java.io.File(dir, "STATUS.tsv"),
      "file\tz3\tvampire\texpected\tverdict\n" + statusRows.sorted.mkString("\n") + "\n")
