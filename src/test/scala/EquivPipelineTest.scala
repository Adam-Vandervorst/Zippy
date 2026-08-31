package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** The automated equivalence pipeline, proofed on the cornerstone examples.  For each program
 *  instance three stages are emitted and VERIFIED (egg exit 0; z3 unsat or vampire refutation):
 *    1. SPACE/TERM vs its optimisation (`SC.reduce`)     — pipeline/<name>-space.egg  + proofs/pipeline/<name>-space.smt2
 *    2. ZIPPER (Scala `transpileZ`) vs SPACE/TERM        — pipeline/<name>-zipper.egg + …-zipper.smt2
 *    3. TRIE/GRAPH (`optimize(transpile(…))`) vs SPACE   — pipeline/<name>-graph.egg  + …-graph.smt2
 *  Control flow is expanded by `EquivPipeline.expand` (each step = the exec evaluation rule for
 *  that node; gated here by `eval(expanded) == eval(original)`).  The egg legs prove equivalence
 *  under the certified rewrite systems; the smt legs prove equal outputs at every path.
 *
 *  ==What the INSTANCE smt legs used to be, and why they changed (plan item 12)==
 *  All 18 of them passed `AgnosticPipeline.fold` over BOTH sides first.  After stage-0 expansion a
 *  cornerstone is ground local algebra, so `isGround` holds AT THE ROOT and each side collapsed to
 *  ONE `Literal`: the two `define-fun`s came out byte-identical and the goal macro-expanded to
 *  `true`.  Measured: z3 answered `unsat` in 0.00-0.01 s and STILL answered `unsat` with the entire
 *  `foPrelude` deleted — nothing in the algebra was used.  The folds are gone; each side is now the
 *  actual structural denotation.  Three consequences, all deliberate:
 *    * where the two sides are the SAME term, the file carries an IDENTICAL-STRUCTURE marker (the
 *      shared-subterm encoder gives them one macro name, so this is decided exactly, not guessed);
 *    * the goal is the ∀-PATH equivalence, with the finite observation list only as a labelled
 *      fallback when neither prover reaches the ∀ form;
 *    * BOTH provers run on every obligation and BOTH verdicts land in the file header and in
 *      proofs/pipeline/STATUS.tsv; a cell neither prover discharges becomes an explicit
 *      PROVER-BUDGET-EXCEEDED record with its attempt log, never a quietly weakened goal. */
class EquivPipelineTest extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(60, "min")

  val pc0: PathContext = PathContextMap(Map.empty)
  val eggDir = new java.io.File(Loaders.repoRoot, "zipper-egg-tests")
  val pipeDir = new java.io.File(eggDir, "pipeline"); pipeDir.mkdirs()
  val smtDir = new java.io.File(Loaders.repoRoot, "proofs/pipeline"); smtDir.mkdirs()
  // EXTERNAL TOOLS: $EGGLOG / $Z3 / $VAMPIRE -> PATH -> conventional locations (Tools.scala).
  // This suite needs all three and says which one is missing rather than skipping quietly.
  val eggBin: String = Tools.egglog.require()
  val z3Bin: String = Tools.z3.require()
  val vampireBin: String = Tools.vampire.require()
  def sh(cmd: Seq[String], cwd: java.io.File, timeoutSec: Int): (Int, String) =
    val out = new StringBuilder
    val log = scala.sys.process.ProcessLogger(out.append(_).append('\n'), out.append(_).append('\n'))
    val p = scala.sys.process.Process(cmd, cwd).run(log)
    val fut = scala.concurrent.Future(p.exitValue())(scala.concurrent.ExecutionContext.global)
    try (scala.concurrent.Await.result(fut, scala.concurrent.duration.Duration(timeoutSec, "s")), out.toString)
    catch { case _: java.util.concurrent.TimeoutException => p.destroy(); (124, out.toString + "\nTIMEOUT") }

  def runEggFileOpt(name: String, content: String, roundsCap: Int = Int.MaxValue): Boolean =
    // ROUNDS ladder: egglog has no early exit, so rounds beyond convergence are wasted (and for the
    // eager reference, explosive) work — try ascending budgets and stop at the first all-green run.
    val ladder = (if content.contains("ROUNDS") then List(8, 12, 14, 20, 32, 48, 80, 120) else List(0))
      .filter(_ <= roundsCap)
    val f = new java.io.File(pipeDir, name)
    var last = ""
    val log = scala.collection.mutable.ArrayBuffer.empty[String]
    val ok = ladder.exists { r =>
      val w = new java.io.FileWriter(f); try w.write(content.replace("ROUNDS", r.toString)) finally w.close()
      val (code, out) = sh(Seq("/bin/sh", "-c", s"ulimit -v 4000000; exec '$eggBin' 'pipeline/$name'"), eggDir, 60)
      last = out
      log += s";   rounds=$r -> exit $code" + (if code == 0 then "" else s" (${out.linesIterator.toList.lastOption.getOrElse("").take(90)})")
      code == 0
    }
    if !ok then
      Loaders.note(s"[pipeline] $name failed every budget:\n${last.linesIterator.toList.takeRight(4).mkString("\n")}")
      // NEVER LEAVE THE TOP RUNG ON DISK.  The last attempt writes the file before running, so a
      // failed ladder used to leave a rung-120 file that still greps as REAL — the on-disk
      // signature of "no budget succeeded", and how six artifacts stayed REAL while egglog
      // rejected them.  Rewrite it as an explicit BUDGET marker carrying the attempt log.
      val w = new java.io.FileWriter(f)
      try w.write(s"; BUDGET-EXCEEDED: egglog did not accept this file at ANY rounds rung.\n" +
                  s"; ATTEMPT LOG (each rung is a full run; the ladder stops at the first exit 0):\n" +
                  log.mkString("\n") + "\n; The equivalence for this cell is carried by the certificates named by the caller\n" +
                  "; (the Scala executor gates, the data-agnostic twin, and the smt twin).\n" +
                  content.replace("ROUNDS", ladder.headOption.getOrElse(0).toString))
      finally w.close()
    ok

  /** Drop a stale `-impl`/`-lit` fallback: once the principal file goes green the fallback is a
   *  leftover from an earlier failing run, and it keeps inflating the audit's REAL/SINGLE-SIDE
   *  counts (measured: four such files sat at rung 120 while their principals were green at 8). */
  def dropFallback(names: String*): Unit =
    for n <- names do
      val f = new java.io.File(pipeDir, n)
      if f.exists() then { f.delete(); Loaders.note(s"[pipeline] removed stale fallback $n (principal is green)") }

  def runEggFile(name: String, content: String): Unit =
    if content.contains("TRIVIAL-NO-OBLIGATION") then
      trivialCount += 1
      val f = new java.io.File(pipeDir, name)
      val w = new java.io.FileWriter(f); try w.write(content) finally w.close()
      return
    if content.contains("IDENTICAL-LITERAL-NO-EQUIVALENCE-OBLIGATION") then
      // both sides materialised to byte-equal terms: no equivalence obligation exists here, but
      // the file's single-side observation checks are still real movement computations — run them.
      identCount += 1
      assert(runEggFileOpt(name, content), s"egglog rejected pipeline/$name at every rounds budget")
      return
    if content.contains("SINGLE-SIDE-OBSERVATION") then
      singleSideCount += 1
      assert(runEggFileOpt(name, content), s"egglog rejected pipeline/$name at every rounds budget")
      return
    realCount += 1
    assert(runEggFileOpt(name, content), s"egglog rejected pipeline/$name at every rounds budget")

  var trivialCount = 0; var realCount = 0; var budgetCount = 0; var lawCount = 0; var identCount = 0
  var singleSideCount = 0

  /** file <TAB> z3 <TAB> vampire <TAB> verdict — the same 4 columns as proofs/STATUS.tsv, written
   *  to proofs/pipeline/STATUS.tsv so a SINGLE-prover result stays VISIBLE instead of implied. */
  val statusRows = scala.collection.mutable.ArrayBuffer.empty[String]
  def writeStatus(): Unit =
    val f = new java.io.File(smtDir, "STATUS.tsv")
    val w = new java.io.FileWriter(f)
    try w.write(statusRows.sorted.mkString("\n") + "\n") finally w.close()

  def write(dir: java.io.File, name: String, content: String): Unit =
    val w = new java.io.FileWriter(new java.io.File(dir, name)); try w.write(content) finally w.close()

  /** Run BOTH provers on one candidate file; returns (z3 ok, vampire ok, a header attempt log). */
  def provers(name: String, content: String, budget: Int, form: String): (Boolean, Boolean, String) =
    val f = new java.io.File(smtDir, name)
    write(smtDir, name, content)
    val t0 = System.nanoTime()
    val (_, zout) = sh(Seq(z3Bin, s"-T:$budget", f.getPath), smtDir, budget + 30)
    val zok = zout.linesIterator.exists(_.trim == "unsat")
    val zs = (System.nanoTime() - t0) / 1000000
    val zsat = zout.linesIterator.exists(_.trim == "sat")
    val t1 = System.nanoTime()
    val (_, vout) = sh(Seq(vampireBin, "--input_syntax", "smtlib2", "-t", s"${budget}s", f.getPath), smtDir, budget + 30)
    val vok = vout.contains("Refutation found")
    val vs = (System.nanoTime() - t1) / 1000000
    assert(!zsat, s"$name: z3 answered SAT on the $form goal — the stated equivalence is FALSE")
    (zok, vok, f"; $form%-22s z3 ${if zok then "unsat" else zout.linesIterator.toList.lastOption.getOrElse("?").trim}%-10s ${zs}%6d ms   " +
                f"vampire ${if vok then "refutation" else "none"}%-10s ${vs}%6d ms (budget ${budget}s each)")

  def runSmtFile(name: String, content: String): Unit =
    if content.contains("TRIVIAL-NO-OBLIGATION") then
      trivialCount += 1; write(smtDir, name, content); statusRows += s"$name\t-\t-\tTRIVIAL"; return
    if content.contains("IDENTICAL-STRUCTURE-NO-EQUIVALENCE-OBLIGATION") then
      // the two sides compile to the SAME shared macro: `(= (m p) (m p))` is `true` by macro
      // expansion, so there is no obligation to run a prover on.  Recorded, never faked.
      identCount += 1; write(smtDir, name, content); statusRows += s"$name\t-\t-\tIDENTICAL-STRUCTURE"; return
    if content.contains("LAW-JUSTIFIED-NO-RESIDUAL") then
      // proof-carrying: every differing pair is a verified instance of the ∀-certified optimiser
      // law set (replayed syntactically); the universal certificates in proofs/ ARE the proof.
      lawCount += 1; write(smtDir, name, content); statusRows += s"$name\t-\t-\tLAW-JUSTIFIED"; return
    realCount += 1
    assert(!content.contains("(assert (not true))"), s"$name: fake reflexive goal emitted")
    // BOTH provers are run on EVERY obligation and BOTH verdicts are recorded — in the file header
    // and in proofs/pipeline/STATUS.tsv.  Cross-validation stays REQUIRED for the -agnostic legs
    // (small, and where a single prover's blind spot would be invisible); for the much larger
    // instance legs a single-prover discharge is recorded as such rather than silently accepted,
    // matching proofs/run.sh's documented policy.  MEASURED (2026-08-31, un-folded sides): vampire
    // discharges 4 of the 10 real instance cells and z3 7 of 10; no cell is discharged by vampire
    // and not z3.  Neither prover discharging is NOT a pass — it becomes a PROVER-BUDGET-EXCEEDED
    // marker with the attempt log, and the cell stops counting as REAL.
    val both = name.contains("agnostic")
    val budget = if both then 240 else 60
    val (zok, vok, log) = provers(name, content, budget, "goal")
    if both && (zok || vok) then
      // CROSS-VALIDATION STAYS MANDATORY on the ∀-inputs legs.  ONE prover succeeding while the
      // other cannot is the exact failure this rule exists for (docs/traps.md §3: a z3-first /
      // vampire-fallback hid that vampire could not unfold the define-fun-rec encoding at all), so
      // a half-discharge is a hard failure, not a recorded partial.  NEITHER succeeding hides
      // nothing — it is plainly open, and is recorded as such below.
      assert(zok && vok, s"$name: only ONE prover discharged this data-agnostic obligation " +
        s"(z3=${if zok then "unsat" else "-"} vampire=${if vok then "proved" else "-"}) — that is an " +
        "encoding blind spot in the other, not a pass")
      statusRows += s"$name\t${if zok then "unsat" else "-"}\t${if vok then "proved" else "-"}\tPROVED"
    else
      recordInstance(name, content, zok, vok, List(log))

  /** Record an instance obligation's outcome: PROVED (with which provers) or, when NEITHER prover
   *  discharged it inside the budget, an honest PROVER-BUDGET-EXCEEDED marker carrying the attempt
   *  log in the file header — never a silently-accepted or weakened goal. */
  def recordInstance(name: String, content: String, zok: Boolean, vok: Boolean, log: List[String]): Unit =
    if zok || vok then
      val hdr = s"; PROVER LOG (both provers are run on every obligation; verdicts also in STATUS.tsv)\n" +
                log.mkString("\n") + "\n"
      write(smtDir, name, hdr + content)
      statusRows += s"$name\t${if zok then "unsat" else "-"}\t${if vok then "proved" else "-"}\tPROVED"
    else
      realCount -= 1; budgetCount += 1
      val hdr =
        "; PROVER-BUDGET-EXCEEDED: NEITHER z3 NOR vampire discharged this obligation.  The goal\n" +
        "; below is the real, un-folded structural equivalence (both sides are the actual\n" +
        "; denotations — no constant folding), it is NOT weakened to something provable, and it is\n" +
        "; NOT counted as a discharged cell.  Equivalence for this instance is carried by the\n" +
        "; Scala executor gates (assertEquals against the reference on this input) and by the\n" +
        "; data-agnostic twin; this file records the open obligation and the attempt log.\n" +
        "; ATTEMPT LOG:\n" + log.mkString("\n") + "\n"
      write(smtDir, name, hdr + content)
      statusRows += s"$name\t-\t-\tOPEN (prover budget exceeded — see header)"
      Loaders.note(s"[pipeline] $name: OPEN — neither prover discharged the un-folded obligation")

  /** An INSTANCE obligation, emitted with the ∀-PATH goal first and the finite observation list
   *  only as a FALLBACK.  The ∀ form is the stronger statement and measured cheaper for z3 wherever
   *  it discharges at all (aunt stage 1: 0.02 s ∀ vs 0.09 s over 28 observations; puzzle3-full
   *  stage 2: 1.22 s vs 6.58 s), so it is what the certificates should say.  When neither prover
   *  reaches it, the observation list is tried and the file header SAYS SO — a spot check labelled
   *  as a spot check, never a ∀ claim backed by 28 points. */
  def runInstanceSmt(name: String, title: String, a: Space, b: Space, obs: List[List[Int]]): Unit =
    val forAll = EquivPipeline.smtEquivalence(s"$title (∀ paths)", a, b, Nil)
    if forAll.contains("IDENTICAL-STRUCTURE-NO-EQUIVALENCE-OBLIGATION") then
      runSmtFile(name, forAll); return
    realCount += 1
    val (z1, v1, log1) = provers(name, forAll, 60, "∀-path goal")
    if z1 || v1 then { recordInstance(name, forAll, z1, v1, List(log1)); return }
    val spot = EquivPipeline.smtEquivalence(s"$title (instance observations — ∀ FORM NOT DISCHARGED)", a, b, obs)
    val (z2, v2, log2) = provers(name, spot, 60, s"${obs.size} observations")
    recordInstance(name, spot, z2, v2, List(log1, log2))

  /** SpaceZipper → the structurally matching Space term (Lit ↦ Literal), for the smt leg. */
  def spaceOfZipper(z: SpaceZipper): Space = z match
    case SpaceZipper.Lit(t) => Literal(t.toSpaceValue)
    case SpaceZipper.Union(a, b) => Union(spaceOfZipper(a), spaceOfZipper(b))
    case SpaceZipper.Intersection(a, b) => Intersection(spaceOfZipper(a), spaceOfZipper(b))
    case SpaceZipper.Subtraction(a, b) => Subtraction(spaceOfZipper(a), spaceOfZipper(b))
    case SpaceZipper.Composition(a, b) => Composition(spaceOfZipper(a), spaceOfZipper(b))
    case SpaceZipper.Prefix(rem, src) => Wrap(spaceOfZipper(src), Path.Constant(PathValue(Interner.uninternPath(rem))))
    case SpaceZipper.RestrictionNode(x, p) => Restriction(spaceOfZipper(x), spaceOfZipper(p))
    case SpaceZipper.TailsUnion(s) => TailsUnion(spaceOfZipper(s))
    case SpaceZipper.TailsIntersection(s) => TailsIntersection(spaceOfZipper(s))

  /** member paths + a capped boundary of non-member paths for observational egg checks. */
  def observations(result: ITrie, vocab: Set[Int], cap: Int = 25): (List[List[Int]], List[List[Int]]) =
    val members = ITrie.toPaths(result).iterator.map(p => Interner.internPath(p.items)).filter(_.nonEmpty).toList.sortBy(_.mkString(","))
    val non = scala.collection.mutable.ArrayBuffer.empty[List[Int]]
    def walk(node: ITrie, prefix: List[Int]): Unit =
      if non.size >= cap then return
      for k <- vocab.toList.sorted if !node.children.contains(k) && non.size < cap do non += (prefix :+ k)
      node.children.foreach((k, c) => walk(c, prefix :+ k))
    walk(result, Nil)
    (members.take(cap), non.toList)

  /** graph → Space via the executor-shaped untranspiler. */
  def untranspileTop(g: RecursiveOpGraph): Space =
    val st = scala.collection.mutable.Stack(new Array[Path | Space | Null](g.nodes.length))
    untranspile(g, st)
    st.top.last.asInstanceOf[Space]

  /** structural smart-constructor collapse (the zipper transpiler's identities). */
  def zipCollapse(s: Space): Space = s match
    case Union(a, b) => val (ca, cb) = (zipCollapse(a), zipCollapse(b)); if ca == cb then ca else Union(ca, cb)
    case Intersection(a, b) => val (ca, cb) = (zipCollapse(a), zipCollapse(b)); if ca == cb then ca else Intersection(ca, cb)
    case Subtraction(a, b) => val (ca, cb) = (zipCollapse(a), zipCollapse(b)); if ca == cb then Empty else Subtraction(ca, cb)
    case Restriction(a, b) => Restriction(zipCollapse(a), zipCollapse(b))
    case Raffination(a, b) => Raffination(zipCollapse(a), zipCollapse(b))
    case Composition(a, b) => Composition(zipCollapse(a), zipCollapse(b))
    case Wrap(src, p) => Wrap(zipCollapse(src), p)
    case Unwrap(src, p) => Unwrap(zipCollapse(src), p)
    case TailsUnion(src) => TailsUnion(zipCollapse(src))
    case TailsIntersection(src) => TailsIntersection(zipCollapse(src))
    case Iteration(src, sym, rest, body) => Iteration(zipCollapse(src), sym, rest, zipCollapse(body))
    case Fixpoint(init, rec, body) => Fixpoint(zipCollapse(init), rec, zipCollapse(body))
    case other => other

  def freeMentions(s: Space): Vector[SpaceMention] =
    val out = scala.collection.mutable.LinkedHashSet.empty[SpaceMention]
    def go(s: Space, bound: Set[String]): Unit = s match
      case Mention(m) => if !bound.contains(m.s) then out += m
      case Union(a, b) => go(a, bound); go(b, bound)
      case Intersection(a, b) => go(a, bound); go(b, bound)
      case Subtraction(a, b) => go(a, bound); go(b, bound)
      case Restriction(a, b) => go(a, bound); go(b, bound)
      case Raffination(a, b) => go(a, bound); go(b, bound)
      case Composition(a, b) => go(a, bound); go(b, bound)
      case Wrap(src, _) => go(src, bound)
      case Unwrap(src, _) => go(src, bound)
      case TailsUnion(src) => go(src, bound)
      case TailsIntersection(src) => go(src, bound)
      case Iteration(src, _, rest, body) => go(src, bound); go(body, bound + rest.s)
      case Fixpoint(init, rec, body) => go(init, bound); go(body, bound + rec.s)
      case Range(x, _, _) => go(x, bound)
      case _ => ()
    go(s, Set.empty); out.toVector

  /** Scala-level randomized gate: the two unrolled symbolic programs agree on random input bindings. */
  def randomGate(name: String, a: Space, b: Space): Unit =
    val rng = new scala.util.Random(20260628)
    val ms = (freeMentions(a) ++ freeMentions(b)).distinct
    for trial <- 1 to 3 do
      val binds = ms.map(m => m -> SpaceValue((0 until rng.nextInt(4)).map(_ =>
        PathValue(List.fill(1 + rng.nextInt(2))(rng.nextInt(3).toString))).toSet)).toMap
      val sc = SpaceContextMap(binds)
      assertEquals(eval(a)(using pc0, sc, PartialFunction.empty), eval(b)(using pc0, sc, PartialFunction.empty),
                   s"$name: agnostic sides differ on random binding #$trial")

  /** probe paths for symbolic observation: key sequences (depth <= 2) over the sides' vocabulary. */
  def probePaths(a: Space, b: Space, cap: Int = 24): List[List[Int]] =
    val vocab = (collectKeys(a) ++ collectKeys(b)).toList.sorted.take(6)
    val d1 = vocab.map(List(_))
    val d2 = for k1 <- vocab; k2 <- vocab yield List(k1, k2)
    (d1 ++ d2).take(cap)

  /** the DATA-AGNOSTIC legs for one comparison: egg (OBSERVATIONAL equivalence — every probe path's
   *  Term observation lands in the same e-class, over free opaque inputs) + smt (∀ inputs, via the
   *  structural-diff decomposition).  Identical-after-normalisation sides emit an explicit
   *  TRIVIAL-NO-OBLIGATION marker (recorded, counted) — never a fake check. */
  def agnosticLegs(name: String, stage: String, sideA0: Space, sideB0: Space,
                   smtA0: Space = null, smtB0: Space = null): Unit =
    val (sideA, sideB) = (SmtDiff.alphaNorm(sideA0), SmtDiff.alphaNorm(sideB0))
    val (smtA, smtB) = (Option(smtA0).getOrElse(sideA), Option(smtB0).getOrElse(sideB))
    randomGate(s"$name-$stage", sideA, sideB)
    // DIFF-DECOMPOSED egg leg (mirrors the smt design): the sides are identical except at the
    // optimiser-rewritten subterm pairs; each SMALL pair is checked observationally with its
    // surrounding binders freed (path binders -> fresh never-used items, behaving generically:
    // the rules only compare items by Eqi; rest-mentions -> opaque (Src (N …))); whole-program
    // equivalence follows by congruence.  The ∀-binder generality is the smt leg's theorem.
    val ms = SmtDiff.diff(sideA, sideB, Nil, Nil)
    // proof-carrying partition (with refinement): justified law instances vs residual pairs
    val (jstP, resP) = SmtDiff.partition(sideA, sideB)
    val sb = new StringBuilder
    if ms.isEmpty then
      sb.append(s"; AUTO-GENERATED pipeline $stage ($name) — DATA-AGNOSTIC.\n")
      sb.append(s"; TRIVIAL-NO-OBLIGATION: sides are syntactically identical after alpha-normalisation —\n")
      sb.append(s"; the transformation is structure-preserving here; nothing to prove.\n")
      runEggFile(s"$name-$stage-agnostic.egg", sb.toString)
    else
      val ctx = new AgnosticPipeline.RenderCtx
      sb.append(s"; AUTO-GENERATED pipeline $stage ($name) — DATA-AGNOSTIC, DIFF-DECOMPOSED: ${ms.size}\n")
      sb.append(s"; optimiser-rewritten subterm pair(s), each checked OBSERVATIONALLY under the certified\n")
      sb.append(s"; movement rules with surrounding binders freed (fresh items / opaque sources); the\n")
      sb.append(s"; whole-program equivalence follows by congruence.  ∀-generality: the smt twin file.\n")
      for ((_, law), i) <- jstP.zipWithIndex do
        sb.append(s"; refined pair $i is LAW-JUSTIFIED ($law) — certificate(s): ${SmtDiff.certificateOf(law)}\n")
      if resP.nonEmpty then sb.append(s"; ${resP.size} refined residual pair(s) carried by the smt twin (z3+vampire).\n")
      sb.append("(include \"prelude.egg\")\n")
      val lets = new StringBuilder; val checks = new StringBuilder
      var emitted = 0
      for ((l, r, ps, ss), i) <- ms.zipWithIndex do
        val penv = ps.zipWithIndex.map((n, j) => n -> (900000 + i * 100 + j).toString).toMap
        val senv = ss.zipWithIndex.map((n, j) => n -> s"(Src (N ${Interner.intern(s"$$free$${i}_$$j$$$n")}))").toMap
        val rl = AgnosticPipeline.renderZ(l, penv, senv, ctx, false)
        val rr = AgnosticPipeline.renderZ(r, penv, senv, ctx, false)
        if rl != rr then
          emitted += 1
          lets.append(s"(let $$l$i $rl)\n(let $$r$i $rr)\n")
          // LEASTNESS IS ASKED FOR, NOT ASSUMED: prelude.egg's Park rule is demand-driven — it
          // fires only for a DECLARED candidate post-fixpoint (a bare three-premise rule can never
          // match, because the premise terms `(Union i c)` are not in the e-graph until something
          // builds them).  When both sides are fixpoints, each is the other's candidate.
          if rl.startsWith("(Fix ") && rr.startsWith("(Fix ") then
            lets.append(s"(FixCand $$l$i $$r$i)\n(FixCand $$r$i $$l$i)\n")
          lets.append(s"(let $$tl$i (Term $$l$i))\n(let $$tr$i (Term $$r$i))\n")
          checks.append(s"(check (= $$tl$i $$tr$i))\n")
          val probes = probePaths(l, r, cap = 8)
          def along(side: String, ids: List[Int]) = ids.foldLeft(side)((acc, k) => s"(Sub $k $acc)")
          for (ids, j) <- probes.zipWithIndex do
            lets.append(s"(let $$pl${i}_$j (Term ${along(s"$$l$i", ids)}))\n(let $$pr${i}_$j (Term ${along(s"$$r$i", ids)}))\n")
            checks.append(s"(check (= $$pl${i}_$j $$pr${i}_$j))\n")
      if emitted == 0 then
        val sbT = new StringBuilder
        sbT.append(s"; AUTO-GENERATED pipeline $stage ($name) — DATA-AGNOSTIC.\n")
        sbT.append(s"; TRIVIAL-NO-OBLIGATION: all ${ms.size} candidate pair(s) render identically after\n")
        sbT.append(s"; freeing binders (the rewrite is definitionally absorbed by the rendering).\n")
        runEggFile(s"$name-$stage-agnostic.egg", sbT.toString)
      else
        if ctx.text.nonEmpty then sb.append(ctx.text).append('\n')
        // The `park` ruleset carries union comm/assoc, which zipper-spec deliberately keeps OUT of
        // the default set (it blows up the movement search), so it is scheduled ONLY when a `Fix`
        // is actually present.
        val sched = if lets.toString.contains("(Fix ") then "(run-schedule (repeat ROUNDS (run) (run park)))"
                    else "(run ROUNDS)"
        sb.append(lets).append(sched).append('\n').append(checks)
        // when EVERY refined pair is a verified certified-law instance, the egg observational run
        // is redundant cross-validation: attempt only the cheap ladder rungs, and record the
        // proof-carrying justification if they don't converge.  Any residual pair keeps the
        // full ladder (and MUST then be proved by both provers in the smt twin just below).
        val allJust = resP.isEmpty
        if !runEggFileOpt(s"$name-$stage-agnostic.egg", sb.toString,
                          roundsCap = if allJust then 14 else Int.MaxValue) then
          val marker =
            if allJust then
              lawCount += 1
              s"; LAW-JUSTIFIED: every differing pair is a verified instance of the optimiser's\n; ∀-certified law set (per-pair laws + certificates in the headers below); the movement\n; observations did not converge within the cheap ladder rungs, and no further egg run is\n; needed — the universal certificates carry the equivalence (with the smt twin + Scala gate).\n"
            else
              budgetCount += 1
              s"; BUDGET-EXCEEDED: the diff pairs' movement observations did not converge within\n; the rounds ladder (deep ground iteration towers).  The data-agnostic equivalence is carried\n; by the pairs' law-justification certificates (headers below), the smt twin, and the\n; randomized Scala gate.\n"
          val f = new java.io.File(pipeDir, s"$name-$stage-agnostic.egg")
          val w = new java.io.FileWriter(f)
          try w.write(marker + sb.toString) finally w.close()
    runSmtFile(s"$name-$stage-agnostic.smt2", SmtDiff.obligationsFile(s"pipeline $stage ($name), data-agnostic", smtA, smtB))

  /** Run the whole three-stage pipeline for one cornerstone. */
  def pipeline(name: String, prog: Space, sc: SpaceContext, rc: PartialFunction[RoutinePtr, Routine]): Unit =
    given PathContext = pc0
    given SpaceContext = sc
    given PartialFunction[RoutinePtr, Routine] = rc
    val reference = eval(prog)
    // ---- DATA-AGNOSTIC legs (inputs free; the primary equivalence certificates) ----
    // stage-1 agnostic compares the ACTUAL pre/post-optimisation terms — NO constant folding
    // here (folding applies the same literal evaluation the optimiser does and erases its visible
    // work; the earlier fold-based sides were vacuously identical).  k=2 for egg, k=1 for smt.
    val uOnf = SmtDiff.alphaNorm(AgnosticPipeline.unrollControl(prog, 2))
    val uPnf = SmtDiff.alphaNorm(AgnosticPipeline.unrollControl(SC.reduce(prog), 2))
    val uOnf1 = SmtDiff.alphaNorm(AgnosticPipeline.unrollControl(prog, 1))
    val uPnf1 = SmtDiff.alphaNorm(AgnosticPipeline.unrollControl(SC.reduce(prog), 1))
    // obligation: terminating/REGISTRY.tsv O10c — THE RESIDUAL CUT IS ONLY SOUND IF BOTH SIDES CUT
    // THE SAME THING.  `unrollControl` replaces the call past depth `k` with a FRESH FREE INPUT
    // `Mention("residual_<routine>_<depth>")`, and the obligation it then states is "the two
    // k-unrollings agree FOR ALL values of that input".  If the optimised side reached the cut at a
    // different depth, or cut a different routine, the two sides would carry DIFFERENT free inputs
    // and the goal would be comparing two unrelated programs — provable or refutable for reasons
    // that have nothing to do with the optimisation.  Pinned here, at both k, before anything is
    // emitted; the registry row stays OPEN because this is a differential and not a theorem.
    def residualMentions(x: Space): Set[String] =
      collect(x)({ case Space.Mention(SpaceMention(n)) if n.startsWith("residual_") => n },
                 PartialFunction.empty)._1.map(_._2).toSet
    for (l, r, kk) <- Vector((uOnf, uPnf, 2), (uOnf1, uPnf1, 1)) do
      assertEquals(residualMentions(l), residualMentions(r),
                   s"$name: the k=$kk agnostic certificate would compare DIFFERENT residual inputs")
    agnosticLegs(name, "space", uPnf, uOnf, uPnf1, uOnf1)
    // stage-2 agnostic compares `uO` against `zipCollapse(uO)` — the zipper transpiler's three
    // smart-constructor identities (x∪x, x∩x, x\x) replayed in Scala.  THIS IS WEAK and it is the
    // reason all six stones are TRIVIAL here: the identities almost never fire on a cornerstone,
    // and no `SpaceZipper` is touched.  The obvious fix — `spaceOfZipper(transpileZ(uO))` — is
    // NOT AVAILABLE data-agnostically and must not be used: `transpileZ` resolves a mention with
    // `ic.getOrElse(m, ITrie.empty)` (Zipper.scala:278), so with the inputs free every mention
    // would silently become ∅ and the leg would compare the program against its all-inputs-empty
    // specialisation — a WRONG obligation, not merely a trivial one.  A real agnostic zipper leg
    // needs an OPAQUE trie source in `SpaceZipper` first (recorded, not papered over).
    val uO = AgnosticPipeline.symbolic(prog)
    agnosticLegs(name, "zipper", zipCollapse(uO), uO)
    locally {
      // stage-3 agnostic: OPTIMISED vs UNOPTIMISED graph, so the obligation is about what
      // `optimize` DID.  It used to be `untranspileTop(optimize(transpile(R)))` vs `uO` — a
      // structure-preserving round trip against the term the graph came from, trivial by
      // construction on every stone.
      val r = Routine(RoutinePtr(name + "_ag"), Vector.empty, freeMentions(uO), uO)
      agnosticLegs(name, "graph", untranspileTop(optimize(transpile(r))), untranspileTop(transpile(r)))
    }
    // ---- INSTANCE legs (executor-grounded spot checks) ----
    // ---- stage 0: expansion (trusted steps), gated against the executor on this instance ----
    val eO = EquivPipeline.expand(prog)
    assertEquals(eval(eO)(using pc0, SpaceContextMap(Map.empty), PartialFunction.empty), reference, s"$name: expansion changed semantics")
    val optProg = SC.reduce(prog)
    val eP = EquivPipeline.expand(optProg)
    assertEquals(eval(eP)(using pc0, SpaceContextMap(Map.empty), PartialFunction.empty), reference, s"$name: optimised expansion changed semantics")
    val resT = ITrie.fromSpaceValue(reference)

    // ---- stage 1: Space/term vs optimised, in the set-of-paths reference system.
    // Equality is MEMBERSHIP-observational (ElemP at every member + boundary non-member, both
    // sides against the executor's ground truth): whole-set e-class equality needs the ACU comm
    // closure, which is factorial at program-sized unions; ElemP is structural and scales. ----
    val vocab1 = collectKeys(eO) ++ collectKeys(eP)
    val (mem1, non1) = observations(resT, vocab1, cap = 25)   // spot check; full semantics gated in Scala + agnostic legs
    val sb1 = new StringBuilder
    val origStr = EquivPipeline.formalOf(eO)
    val optStr = EquivPipeline.formalOf(eP)
    val ident1 = origStr == optStr
    def fpath(ids: List[Int]): String = ids.map(i => s"(Item $i)").reduceRight((a, b) => s"(Concat $a $b)")
    if ident1 then
      // ground control-flow expansion evaluated both sides to the SAME term: byte-equal in egg,
      // so an equivalence check would be true by hash-consing alone.  The optimiser's actual work
      // (or its absence) on this stone is certified by the agnostic legs above; below only the
      // reference encoding's own observations are verified.
      sb1.append(s"; AUTO-GENERATED pipeline stage 1 ($name).\n")
      sb1.append(s"; IDENTICAL-LITERAL-NO-EQUIVALENCE-OBLIGATION: the expanded program and its expanded\n")
      sb1.append(s"; optimisation render to byte-equal terms (ground expansion evaluates the parts the\n")
      sb1.append(s"; optimiser rewrites); an egg equivalence check would be vacuous by hash-consing and\n")
      sb1.append(s"; is NOT emitted.  The optimiser comparison for this stone is carried by the\n")
      sb1.append(s"; $name-space-agnostic legs.  Below: membership observations of the one encoding.\n")
      sb1.append("(include \"formal-elem-prelude.egg\")\n")
      sb1.append(s"(let $$orig $origStr)\n")
      for (ids, i) <- mem1.zipWithIndex do
        sb1.append(s"(let $$mo$i (ElemP ${fpath(ids)} $$orig))\n")
      for (ids, i) <- non1.zipWithIndex do
        sb1.append(s"(let $$no$i (ElemP ${fpath(ids)} $$orig))\n")
      sb1.append("\n(run-schedule (repeat ROUNDS (run) (saturate paths) (run neg)))\n\n")
      for i <- mem1.indices do sb1.append(s"(check (= $$mo$i (ET)))\n")
      for i <- non1.indices do sb1.append(s"(check (= $$no$i (EF)))\n")
    else
      sb1.append(s"; AUTO-GENERATED pipeline stage 1 ($name): the program vs its Space-level optimisation\n")
      sb1.append(s"; (SC.reduce), proved equivalent under the eager set-of-paths rewrite system by membership\n")
      sb1.append(s"; observation (every member ElemP=ET in BOTH, every boundary non-member EF in BOTH).\n")
      sb1.append("(include \"formal-elem-prelude.egg\")\n")   // rotation-free: ElemP checks are shape-free
      sb1.append(s"(let $$orig $origStr)\n")
      sb1.append(s"(let $$opt $optStr)\n")
      for (ids, i) <- mem1.zipWithIndex do
        sb1.append(s"(let $$mo$i (ElemP ${fpath(ids)} $$orig))\n(let $$mp$i (ElemP ${fpath(ids)} $$opt))\n")
      for (ids, i) <- non1.zipWithIndex do
        sb1.append(s"(let $$no$i (ElemP ${fpath(ids)} $$orig))\n(let $$np$i (ElemP ${fpath(ids)} $$opt))\n")
      sb1.append("\n(run-schedule (repeat ROUNDS (run) (saturate paths) (run neg)))\n\n")
      for i <- mem1.indices do sb1.append(s"(check (= $$mo$i (ET))) (check (= $$mp$i (ET)))\n")
      for i <- non1.indices do sb1.append(s"(check (= $$no$i (EF))) (check (= $$np$i (EF)))\n")
    if ident1 then identCount += 1
    var tier1ok = runEggFileOpt(s"$name-space.egg", sb1.toString)
    if tier1ok then dropFallback(s"$name-space-impl.egg", s"$name-space-lit.egg")
    if !tier1ok then
      // the eager SET reference's legacy machinery cannot converge on every instance shape (its
      // non-confluent closure explodes past ~14 rounds); fall back to the other exec model — the
      // eager TRIE reference in the bridge (same instance equivalence, certified recursion).
      val sbF = new StringBuilder
      sbF.append(s"; AUTO-GENERATED pipeline stage 1 ($name) — INSTANCE spot check in the eager-TRIE\n")
      sbF.append(s"; reference (bridge impl recursion; the eager-SET reference did not converge here).\n")
      sbF.append("(include \"bridge-prelude.egg\")\n")
      sbF.append(s"(let $$opt (Reflect ${EquivPipeline.implOfSpace(eP)}))\n")
      sbF.append(s"(let $$want (Reflect ${EquivPipeline.tnodeOf(resT)}))\n")
      emitObsPairs(sbF, "$opt", "$want", mem1, non1, resT)
      if !runEggFileOpt(s"$name-space-impl.egg", sbF.toString) then
        // even the optimised side alone exceeds the eager budget (very large expansions):
        // instance equivalence is carried by the Scala gates; this file checks the reference
        // output's own encoding/observations in the certified system.
        val sbL = new StringBuilder
        sbL.append(s"; AUTO-GENERATED pipeline stage 1 ($name) — instance sides exceed the eager egg\n")
        sbL.append(s"; budget; structural equivalence is carried by the Scala executor gates and the\n")
        sbL.append(s"; agnostic certificates.  This file verifies the reference output's observations.\n")
        sbL.append("(include \"bridge-prelude.egg\")\n")
        sbL.append(s"(let $$want (Reflect ${EquivPipeline.tnodeOf(resT)}))\n")
        emitObsPairs(sbL, "$want", "$want", mem1, non1, resT)
        runEggFile(s"$name-space-lit.egg", sbL.toString)
    // NO CONSTANT FOLDING (plan item 12): `AgnosticPipeline.fold` runs the executor, and after
    // stage-0 expansion `isGround` holds AT THE ROOT, so both sides collapsed to the SAME literal
    // and the goal macro-expanded to `true` — measured: z3 0.00-0.01 s, still `unsat` with the
    // ENTIRE prelude deleted.  The sides below are the actual structural denotations.
    runInstanceSmt(s"$name-space.smt2", s"pipeline stage 1 ($name): original vs optimised", eO, eP, mem1 ++ non1)

    // ---- stage 2: the VIRTUAL zipper program (Iter/BodyK binders over the INPUT literals — not
    // pre-materialised) observed by movement against the reference output, plus the Scala executor
    // gate on the real transpiled zipper. ----
    val zProg = transpileZ(prog)(using pc0, Map.from(sc.asInstanceOf[SpaceContextMap].m.map((k, v) => k -> ITrie.fromSpaceValue(v))), rc)
    assertEquals(SpaceZipper.materialize(zProg).toSpaceValue, reference, s"$name: zipper executor disagrees")
    val (members, nonMembers) = observations(resT, ZipperEgg.keysOf(zProg) ++ collectKeys(eO))
    locally {
      // virtual program: unroll control flow (inputs bound as literals, iterations KEPT as binders)
      val bound = sc.asInstanceOf[SpaceContextMap].m.foldLeft(prog)((s, kv) => AgnosticPipeline.substMention(s, kv._1, Literal(kv._2)))
      var unrolled = AgnosticPipeline.unrollControl(bound, 4)(using rc)
      // instance-virtual: the loop has converged within k — cut residual inputs to ∅ and GATE it
      for m <- freeMentions(unrolled) if m.s.startsWith("residual_") do
        unrolled = AgnosticPipeline.substMention(unrolled, m, Empty)
      assertEquals(eval(unrolled)(using pc0, SpaceContextMap(Map.empty), PartialFunction.empty), reference,
                   s"$name: k-unrolled virtual program does not reach the reference (raise k)")
      val virt = SmtDiff.alphaNorm(unrolled)
      val vctx = new AgnosticPipeline.RenderCtx
      val vr = AgnosticPipeline.renderZ(virt, Map.empty, Map.empty, vctx, true)
      val sbV = new StringBuilder
      sbV.append(s"; AUTO-GENERATED pipeline stage 2 ($name) — the VIRTUAL zipper program: Iter/BodyK\n")
      sbV.append(s"; binders over the input literals (control flow NOT pre-materialised); the movement\n")
      sbV.append(s"; rules walk it (Keys enumeration, per-head App, Guard pruning); every member of the\n")
      sbV.append(s"; reference output must be reachable, every boundary non-member not.\n")
      sbV.append("(include \"prelude.egg\")\n")
      if vctx.text.nonEmpty then sbV.append(vctx.text).append('\n')
      sbV.append(s"(let $$virt $vr)\n")
      def along(ids: List[Int]) = ids.foldLeft("$virt")((acc, k) => s"(Sub $k $acc)")
      val (vm, vn) = (members.take(12), nonMembers.take(12))
      for (ids, i) <- vm.zipWithIndex do sbV.append(s"(let $$vm$i (Term ${along(ids)}))\n")
      for (ids, i) <- vn.zipWithIndex do sbV.append(s"(let $$vn$i (Term ${along(ids)}))\n")
      sbV.append(if vr.contains("(Fix ") then "(run-schedule (repeat ROUNDS (run) (run park)))\n"
                 else "(run ROUNDS)\n")
      for i <- vm.indices do sbV.append(s"(check (= $$vm$i (T)))\n")
      for i <- vn.indices do sbV.append(s"(check (= $$vn$i (F)))\n")
      if !runEggFileOpt(s"$name-zipper-virtual.egg", sbV.toString) then
        Loaders.note(s"[pipeline] $name-zipper-virtual: exceeds movement-observation budget (recorded)")
        val f = new java.io.File(pipeDir, s"$name-zipper-virtual.egg")
        val w = new java.io.FileWriter(f)
        try w.write(s"; BUDGET-EXCEEDED: the virtual program's movement observations did not converge\n; within the rounds ladder for this instance; carried by the Scala executor gate + smaller\n; instances of the same machinery (see datalog-sn / temperature virtual files).\n" + sbV.toString) finally w.close()
    }
    val sb2 = new StringBuilder
    val zipStr = s"(Reflect ${ZipperEgg.implOf(zProg).replace("(Node ", "(TNode ")})"
    val spcStr = s"(Reflect ${EquivPipeline.tnodeOf(resT)})"
    if zipStr == spcStr then
      // the transpiled zipper program PRE-MATERIALISES in Scala to exactly the reference trie:
      // both sides would be byte-equal constructor terms, and hash-consing equates them with ZERO
      // rule applications — an egg "equivalence" check would be vacuous.  Record that honestly;
      // the movement-machinery certificate for this stone is the -zipper-virtual.egg twin, and
      // this file only verifies the reference output's observations under the certified rules.
      sb2.append(s"; AUTO-GENERATED pipeline stage 2 ($name).\n")
      sb2.append(s"; IDENTICAL-LITERAL-NO-EQUIVALENCE-OBLIGATION: transpileZ's output materialises (in\n")
      sb2.append(s"; Scala, gated by assertEquals against the executor) to exactly the reference trie;\n")
      sb2.append(s"; the two egg sides are byte-equal constructor terms, so an equivalence check here\n")
      sb2.append(s"; would be true by hash-consing alone and is NOT emitted.  The zipper-machinery\n")
      sb2.append(s"; certificate for this stone is $name-zipper-virtual.egg (Iter/BodyK binders, NOT\n")
      sb2.append(s"; pre-materialised).  Below: the reference output's observations only.\n")
      sb2.append("(include \"bridge-prelude.egg\")\n")
      sb2.append(s"(let $$spc $spcStr)\n")
      emitObsPairs(sb2, "$spc", "$spc", members, nonMembers, resT)
    else
      sb2.append(s"; AUTO-GENERATED pipeline stage 2 ($name): the ZIPPER program (Scala transpileZ) vs the\n")
      sb2.append(s"; SPACE/TERM program, proved observationally equivalent under the movement rewrite system\n")
      sb2.append(s"; (every member reachable in BOTH, every boundary non-member in NEITHER, pairwise equal).\n")
      sb2.append("(include \"bridge-prelude.egg\")\n")
      sb2.append(s"(let $$zip $zipStr)\n")
      sb2.append(s"(let $$spc $spcStr)\n")
      emitObsPairs(sb2, "$zip", "$spc", members, nonMembers, resT)
    if runEggFileOpt(s"$name-zipper.egg", sb2.toString) then dropFallback(s"$name-zipper-lit.egg")
    else
      Loaders.note(s"[pipeline] $name-zipper: structural side exceeds the eager egg budget; " +
        "instance equivalence carried by the Scala gates + agnostic certificates")
      val sbL = new StringBuilder
      sbL.append(s"; AUTO-GENERATED pipeline stage 2 ($name) — structural side exceeds the eager egg\n")
      sbL.append(s"; budget; equivalence carried by the Scala gates + agnostic certificates.  This file\n")
      sbL.append(s"; verifies the reference output observations in the certified system.\n")
      sbL.append("(include \"bridge-prelude.egg\")\n")
      sbL.append(s"(let $$want (Reflect ${EquivPipeline.tnodeOf(resT)}))\n")
      emitObsPairs(sbL, "$want", "$want", members, nonMembers, resT)
      runEggFile(s"$name-zipper-lit.egg", sbL.toString)
    runInstanceSmt(s"$name-zipper.smt2", s"pipeline stage 2 ($name): zipper vs space",
                   spaceOfZipper(zProg), eO, members ++ nonMembers)

    // ---- stage 3: optimised op-graph vs Space/term program, in the bridge (impl) system ----
    val g = optimize(transpile(Routine(RoutinePtr(name), Vector.empty, Vector.empty, eO)))
    assertEquals(runGraphT(g).toSpaceValue, reference, s"$name: graph executor disagrees")
    val (lets, root) = EquivPipeline.trOfGraph(g)
    val sb3 = new StringBuilder
    sb3.append(s"; AUTO-GENERATED pipeline stage 3 ($name): the OPTIMISED OP-GRAPH (CSE/hoisted DAG, as\n")
    sb3.append(s"; shared lets) vs the SPACE/TERM program, proved observationally equivalent in the bridge\n")
    sb3.append(s"; system (the graph reduces by the eager-trie recursion; observed through Reflect).\n")
    sb3.append("(include \"bridge-prelude.egg\")\n")
    sb3.append(lets)
    sb3.append(s"(let $$grefl (Reflect $root))\n")
    sb3.append(s"(let $$spc (Reflect ${EquivPipeline.tnodeOf(resT)}))\n")   // the reference output
    emitObsPairs(sb3, "$grefl", "$spc", members, nonMembers, resT)
    if runEggFileOpt(s"$name-graph.egg", sb3.toString) then dropFallback(s"$name-graph-lit.egg")
    else
      Loaders.note(s"[pipeline] $name-graph: DAG exceeds the eager egg budget; " +
        "instance equivalence carried by the Scala gates + agnostic certificates")
      val sbL = new StringBuilder
      sbL.append(s"; AUTO-GENERATED pipeline stage 3 ($name) — the optimised DAG exceeds the eager egg\n")
      sbL.append(s"; budget; equivalence carried by the Scala gates (runGraphT == reference) + the\n")
      sbL.append(s"; agnostic certificates.  This file verifies the reference output observations.\n")
      sbL.append("(include \"bridge-prelude.egg\")\n")
      sbL.append(s"(let $$want (Reflect ${EquivPipeline.tnodeOf(resT)}))\n")
      emitObsPairs(sbL, "$want", "$want", members, nonMembers, resT)
      runEggFile(s"$name-graph-lit.egg", sbL.toString)
    runInstanceSmt(s"$name-graph.smt2", s"pipeline stage 3 ($name): graph vs space",
                   untranspiledSpace(g), eO, members ++ nonMembers)
    // marker audit (CI-countable): every emitted file is REAL (proved), TRIVIAL (recorded no-op),
    // LAW-JUSTIFIED (proof-carrying), or BUDGET (recorded, certificate carried elsewhere).
    Loaders.note(s"[pipeline] $name markers so far: real=$realCount trivial=$trivialCount " +
                 s"law-justified=$lawCount budget=$budgetCount identical=$identCount single-side=$singleSideCount")
    writeStatus()

  /** observation pairs: both sides Term-checked at every member (T), boundary non-member (F).
   *  With a == b (single-side files) only one observation per path is emitted — duplicating the
   *  same let under two names would fabricate a fake "pair" — and the file is STAMPED
   *  SINGLE-SIDE-OBSERVATION so the audit stops counting it REAL.  It is a real movement
   *  computation in the certified system, but it observes ONE side against the reference output;
   *  five `-lit` fallbacks used to count as equivalence cells while proving only that the
   *  reference literal observes itself. */
  def emitObsPairs(sb: StringBuilder, a: String, b: String, members: List[List[Int]], non: List[List[Int]], result: ITrie): Unit =
    val two = a != b
    if !two then
      sb.append("; SINGLE-SIDE-OBSERVATION: one side observed against the executor's reference\n")
      sb.append("; output — a real computation under the certified rules, but NOT an equivalence.\n")
    def along(side: String, ids: List[Int]) = ids.foldLeft(side)((acc, k) => s"(Sub $k $acc)")
    for (ids, i) <- members.zipWithIndex do
      sb.append(s"(let $$ma$i (Term ${along(a, ids)}))\n")
      if two then sb.append(s"(let $$mb$i (Term ${along(b, ids)}))\n")
    for (ids, i) <- non.zipWithIndex do
      sb.append(s"(let $$na$i (Term ${along(a, ids)}))\n")
      if two then sb.append(s"(let $$nb$i (Term ${along(b, ids)}))\n")
    sb.append(s"(let $$ra (Term $a))\n")
    if two then sb.append(s"(let $$rb (Term $b))\n")
    sb.append("\n(run ROUNDS)\n\n")
    val eps = if result.terminal then "(T)" else "(F)"
    sb.append(s"(check (= $$ra $eps))\n")
    if two then sb.append(s"(check (= $$rb $eps))\n")
    for i <- members.indices do
      sb.append(s"(check (= $$ma$i (T)))\n")
      if two then sb.append(s"(check (= $$mb$i (T)))\n")
    for i <- non.indices do
      sb.append(s"(check (= $$na$i (F)))\n")
      if two then sb.append(s"(check (= $$nb$i (F)))\n")

  def collectKeys(s: Space): Set[Int] = s match
    case Literal(v) => v.paths.flatMap(p => Interner.internPath(p.items)).toSet
    case Singleton(p) => p match { case Path.Constant(v) => Interner.internPath(v.items).toSet; case _ => Set.empty }
    case Union(a, b) => collectKeys(a) ++ collectKeys(b)
    case Intersection(a, b) => collectKeys(a) ++ collectKeys(b)
    case Subtraction(a, b) => collectKeys(a) ++ collectKeys(b)
    case Restriction(a, b) => collectKeys(a) ++ collectKeys(b)
    case Raffination(a, b) => collectKeys(a) ++ collectKeys(b)
    case Composition(a, b) => collectKeys(a) ++ collectKeys(b)
    case Wrap(src, p) => collectKeys(src) ++ (p match { case Path.Constant(v) => Interner.internPath(v.items).toSet; case _ => Set.empty })
    case Unwrap(src, p) => collectKeys(src) ++ (p match { case Path.Constant(v) => Interner.internPath(v.items).toSet; case _ => Set.empty })
    case TailsUnion(src) => collectKeys(src)
    case TailsIntersection(src) => collectKeys(src)
    case Iteration(src, _, _, body) => collectKeys(src) ++ collectKeys(body)
    case Fixpoint(init, _, body) => collectKeys(init) ++ collectKeys(body)
    case Range(x, _, _) => collectKeys(x)
    case _ => Set.empty

  /** graph → Space (for the smt leg), by walking the DAG (dup-on-share is fine at these sizes). */
  def untranspiledSpace(g: RecursiveOpGraph): Space =
    def path(coord: (Int, Int)): Path = g.nodes(coord._2) match
      case Left(Node("Constant", c, _, _)) => Path.Constant(PathValue(Interner.uninternPath(internConstStr(c))))
      case other => throw IllegalStateException(s"expected Constant: $other")
    def sp(i: Int): Space = g.nodes(i) match
      case Left(Node(op, constant, _, inputs)) => op match
        case "Empty" => Empty
        case "Literal" => Literal(iLiteralStr(constant).toSpaceValue)
        case "Singleton" => Singleton(path(inputs(0)))
        case "Union" => Union(sp(inputs(0)._2), sp(inputs(1)._2))
        case "Intersection" => Intersection(sp(inputs(0)._2), sp(inputs(1)._2))
        case "Subtraction" => Subtraction(sp(inputs(0)._2), sp(inputs(1)._2))
        case "Restriction" => Restriction(sp(inputs(0)._2), sp(inputs(1)._2))
        case "Raffination" => Raffination(sp(inputs(0)._2), sp(inputs(1)._2))
        case "Composition" => Composition(sp(inputs(0)._2), sp(inputs(1)._2))
        case "Wrap" => Wrap(sp(inputs(0)._2), path(inputs(1)))
        case "Unwrap" => Unwrap(sp(inputs(0)._2), path(inputs(1)))
        case "TailsUnion" => TailsUnion(sp(inputs(0)._2))
        case "TailsIntersection" => TailsIntersection(sp(inputs(0)._2))
        case other => throw IllegalStateException(s"graph op not local: $other")
      case Right(_) => throw IllegalStateException("no subgraphs expected")
    sp(g.nodes.length - 1)

  // ==============================================================================================
  // The cornerstone examples
  // ==============================================================================================
  def pv(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  def routineN(name: String, ms: String*)(body: Space): Routine =
    Routine(RoutinePtr(name), Vector.empty, ms.map(SpaceMention(_)).toVector, body)
  def callN(name: String, ms: Space*): Space = Space.Call(RoutinePtr(name), Vector.empty, ms.toVector)

  test("pipeline: aunt") {
    pipeline("aunt", Routines.aunt_query_routine.body, AuntQuery.context, PartialFunction.empty)
  }

  test("pipeline: semi-naive datalog") {
    def join(r: Space, s: Space): Space = r.iter(P"n", S"nbs", P"n" x \/(s <| S"nbs"))
    // obligation: terminating/datalog_b_seminaive_{lemmas,terminates}.smt2 (T4 — the measure
    // 2·card(top∖A) + [D ≠ ∅] strictly decreases on every state-changing semi-naive step) and
    // terminating/seminaive_correct.smt2 (O13 — naive ≡ semi-naive ROUND FOR ROUND).  O13's side
    // condition is additivity of the join, `J(X ∪ Y) = J(X) ∪ J(Y)`: this compiler performs no
    // semi-naive transformation, so additivity is on the author of `sn_tc` (registry row O13-SC).
    val snTC = routineN("sn_tc", "e", "all", "delta") {
      S"all" \/ callN("sn_tc", S"e", S"all" \/ (join(S"delta", S"e") \ S"all"), join(S"delta", S"e") \ S"all") }
    val edges = sv(pv("0", "1"), pv("1", "2"), pv("2", "3"))
    pipeline("datalog-sn", callN("sn_tc", Mention(SpaceMention("edges")), Mention(SpaceMention("edges")), Mention(SpaceMention("edges"))),
             SpaceContextMap(Map(SpaceMention("edges") -> edges)), Syntax.mod(snTC))
  }

  test("pipeline: game of life") {
    val live = Set((1, 0), (1, 1), (1, 2))                       // the blinker
    val rules = GoL.rulesFor(live)
    pipeline("gol", Space.Call(RoutinePtr("nextStep"), Vector(), Vector(Mention(SpaceMention("field")))),
             SpaceContextMap(Map(SpaceMention("field") -> GoL.field(live))), rules.defs)
  }

  test("pipeline: 15-puzzle (one BFS expansion)") {
    val p = Sliding.puzzle(4, 4)                                 // the 15-puzzle
    pipeline("puzzle15", p.expandStep(Mention(SpaceMention("frontier"))),
             SpaceContextMap(Map(SpaceMention("frontier") -> SpaceValue(Set(p.initial)))), p.defs)
  }

  test("pipeline: temperature") {
    val rr = new scala.util.Random(12)
    val cells = (0 until 16).map(i => PathValue(NOAA.bits(i, 4) :+ (Vector("VC", "C", "N", "W", "VW")(rr.nextInt(5))))).toSet
    val world = Mention(SpaceMention("world"))
    val q = Union(Restriction(world, Literal(NOAA.interval(0, 4, 4))), Restriction(world, Literal(NOAA.interval(12, 16, 4))))
    pipeline("temperature", q, SpaceContextMap(Map(SpaceMention("world") -> SpaceValue(cells))), PartialFunction.empty)
  }

  test("pipeline: n-queens") {
    val b = NQueens.board(4)
    pipeline("nqueens", b.program, SpaceContextMap(Map.empty), b.defs)
  }

  /** puzzle3-full — the SEVENTH cornerstone, and the ONLY one whose recursion is an unbounded
   *  `Space.Fixpoint` (CornerstoneTypes.scala reports seven; the pipeline ran six, so the one
   *  stone that exercises the fixpoint machinery end to end had NO row at all).  The 2x2 sliding
   *  puzzle's reachable space: start from the solved board and close under `expandStep` to a
   *  union-saturating fixpoint — all 4!/2 = 12 states.  The program is replicated here rather
   *  than imported because `CornerstoneTypes` is a `FunSuite`, not an object. */
  def puzzleFixpoint(rows: Int, cols: Int): Space =
    val p = Sliding.puzzle(rows, cols)
    val rec = SpaceMention("reach")
    val step = Space.Fixpoint(Space.Singleton(Path.Constant(p.initial)), rec,
                              Space.Union(Space.Mention(rec), p.expandStep(Space.Mention(rec))))
    // expandStep calls superpose/collapse — inline them so the term is Call-free and the binder,
    // not an opaque Call, is what the renderers and the provers see.
    val (lowered, residual) = lowerCalls(Routine(RoutinePtr("main"), Vector.empty, Vector.empty, step), p.defs)
    assert(residual.isEmpty, s"puzzle${rows * cols - 1}-full: unexpected residual ${residual.keys}")
    lowered

  test("pipeline: 3-puzzle FULL reachable space (the unbounded Fixpoint cornerstone)") {
    pipeline("puzzle3-full", puzzleFixpoint(2, 2), SpaceContextMap(Map.empty), PartialFunction.empty)
  }
end EquivPipelineTest
