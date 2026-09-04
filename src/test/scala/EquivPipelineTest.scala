package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** The automated equivalence pipeline, proofed on the cornerstone examples (review item 4).
 *
 *  ==THE MATRIX (plan.md 2A.1 — proofs/pipeline/CLAIMS.tsv is the declaration this suite is measured
 *  against)==  Seven cornerstones × three boundaries × two forms, one artifact per cell:
 *
 *    space   the program vs `SC.reduce(program)`, discharged by THE TRACE (`SC.reduceTraced`, 2A.3):
 *            every step is a re-applied instance of a certified optimiser law, composed end to end.
 *            `<name>-space.smt2` (instance) records the chain and the per-step executor differential on
 *            this input; `<name>-space-agnostic.egg` re-derives each step's differing subterm pairs in
 *            egglog under the certified movement rules, and cites each step's ∀-certificate where the
 *            ladder does not converge — never a BUDGET marker (2A.5).
 *    zipper  `transpileZ(program)` vs the program, an INSTANCE of the universal refinement theorem
 *            (proofs/zipper_refinement.smt2; proofs/lean/Zippy/Zipper.lean#Zippy.Zip.refinement): the
 *            materialising subterms become opaque holes, the SHELL is transpiled with every source
 *            opaque (`SpaceZipper.Opaque`, 2A.4) and read back through `spaceOfZipper`; the theorem does
 *            the semantics.  `<name>-zipper-agnostic.smt2` and `<name>-zipper.smt2` (+ the materialize
 *            differential).
 *    graph   `untranspile(optimize(transpile(P)))` vs `P` on the SYMBOLIC program (binders kept): the
 *            differing pairs law-justified, residual pairs proved on the pair.  `<name>-graph-agnostic.smt2`
 *            and `<name>-graph.smt2` (+ the `runGraphT == eval` differential).
 *
 *  Every artifact opens with the `; TRUSTS:` header (`Certified.trustsHeader`, docs/TRUSTED.md) naming
 *  what its claim rests on, and `scripts/audit_pipeline_markers.py --accept` holds each cell to its
 *  CLAIMS.tsv row: kind, permitted trusts, artifact present.
 *
 *  ==WHAT THIS REPLACED, AND WHY (plan.md's fourth correction)==
 *  Eleven of the twelve REAL `.egg` cells compared one program against `Reflect(tnodeOf(resT))` — the
 *  executor's own output — and the stage-1 instance cells compared two materialised expansions, so a
 *  prover was asked to re-derive, on a 174 MB literal, an equivalence the optimiser had produced by a
 *  dozen named rewrites.  The trace states which rewrites; the refinement theorem states what the
 *  zipper preserves; nothing compares a program to a trie any more.  The `-lit`/`-impl`/`-virtual`
 *  single-side files and the observational `.egg` cells are deleted at their source. */
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
    val committed = new java.io.File(pipeDir, name)
    var last = ""
    val log = scala.collection.mutable.ArrayBuffer.empty[String]
    val ok = ladder.exists { r =>
      // 0.3 — THROUGH THE SINK.  Each rung's bytes go to the sink's path (the committed file only
      // under ZIPPY_REGENERATE=1, a scratch twin otherwise) and egglog is pointed at THAT path while
      // still running FROM `eggDir`, because it resolves `(include "prelude.egg")` against its
      // WORKING DIRECTORY rather than the file's directory (measured).  Only the rung the ladder
      // settles on is the artifact, and the sink keeps the last write per path for that reason.
      val f = ArtifactSink.write(committed, content.replace("ROUNDS", r.toString))
      val (code, out) = sh(Seq("/bin/sh", "-c", s"ulimit -v 4000000; exec '$eggBin' '${f.getAbsolutePath}'"), eggDir, 60)
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
      ArtifactSink.write(committed,
        s"; BUDGET-EXCEEDED: egglog did not accept this file at ANY rounds rung.\n" +
        s"; ATTEMPT LOG (each rung is a full run; the ladder stops at the first exit 0):\n" +
        log.mkString("\n") + "\n; The equivalence for this cell is carried by the certificates named by the caller\n" +
        "; (the Scala executor gates, the data-agnostic twin, and the smt twin).\n" +
        content.replace("ROUNDS", ladder.headOption.getOrElse(0).toString))
    ok

  /** Drop a stale `-impl`/`-lit` fallback: once the principal file goes green the fallback is a
   *  leftover from an earlier failing run, and it keeps inflating the audit's REAL/SINGLE-SIDE
   *  counts (measured: four such files sat at rung 120 while their principals were green at 8). */
  def dropFallback(names: String*): Unit =
    for n <- names do
      val f = new java.io.File(pipeDir, n)
      // 0.3 — THROUGH THE SINK.  "this committed file should not exist" is exactly as much of an
      // artifact change as a content edit, so in VERIFY mode nothing is removed and the intent is
      // recorded as a finding; only ZIPPY_REGENERATE=1 actually deletes.
      if ArtifactSink.delete(f) then Loaders.note(s"[pipeline] removed stale fallback $n (principal is green)")
      else if f.exists() then Loaders.note(s"[pipeline] stale fallback $n would be removed (principal is green)")

  def runEggFile(name: String, content: String): Unit =
    Certified.trustsOf(content, name)   // 2E.5: required on every artifact, egg included
    if content.contains("TRIVIAL-NO-OBLIGATION") then
      trivialCount += 1
      ArtifactSink.write(new java.io.File(pipeDir, name), content)
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
  /** which stones reached the renderers with their control flow INTACT, and which fell back to the
   *  executed form — printed at the end, so "the binders survived" is a measured claim per stone
   *  rather than a property of the code path. */
  val binderKept = scala.collection.mutable.Set.empty[String]
  val binderFallback = scala.collection.mutable.Set.empty[String]
  /** cells whose sides carry a residual cut, so their claim is about the k-unrollings and not about
   *  the recursion (O10b).  Printed at the end and stamped into each file. */
  val boundedUnrolled = scala.collection.mutable.Set.empty[String]
  private var ident1Last = false

  /** file <TAB> z3 <TAB> vampire <TAB> verdict — the same 4 columns as proofs/STATUS.tsv, written
   *  to proofs/pipeline/STATUS.tsv so a SINGLE-prover result stays VISIBLE instead of implied. */
  val statusRows = scala.collection.mutable.ArrayBuffer.empty[String]
  def writeStatus(): Unit =
    ArtifactSink.write(new java.io.File(smtDir, "STATUS.tsv"), statusRows.sorted.mkString("\n") + "\n")

  /** every `.smt2` this suite emits goes through the sink; the returned file is what the provers are
   *  pointed at, so in VERIFY mode they check exactly the bytes that were compared against the tree */
  def write(dir: java.io.File, name: String, content: String): java.io.File =
    ArtifactSink.write(new java.io.File(dir, name), content)

  /** Run BOTH provers on one candidate file; returns (z3 ok, vampire ok, a header attempt log). */
  def provers(name: String, content: String, budget: Int, form: String): (Boolean, Boolean, String) =
    val f = write(smtDir, name, content)
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
    // THE VERDICT GOES IN THE FILE; THE WALL CLOCK GOES TO THE LOG.
    //
    // This line used to read `z3 unsat  9 ms  vampire refutation  6 ms`, and the milliseconds were
    // written into a COMMITTED artifact.  0.3's golden-file gate made the consequence unmissable:
    // 12 of the 42 `proofs/pipeline` artifacts came back CHANGED on every run with `6 ms` against
    // `7 ms`, `60012 ms` against `60491 ms`.  A wall clock cannot live in a file whose content is
    // supposed to be a function of the tree — it makes the artifact unstable by construction, and a
    // golden-file gate over it could never be green, which turns the gate into noise a reader learns
    // to ignore.  (The same defect, in the same shape, as the `OPTIMIZED in 836 ms` figure that was
    // inside `SpatialEventsCheck`'s `CALIBRATION:` channel; see `scripts/check_determinism.sh`.)
    //
    // NOTHING A READER NEEDS IS LOST.  The header keeps both VERDICTS and the BUDGET, which are the
    // two facts a reader of a proof artifact acts on: `timeout` already says the budget was
    // exhausted, and the budget says what it was.  The timings are PRINTED, so the run log — which
    // is where a performance question belongs — still has them per obligation.
    println(f"[pipeline] $name%-40s $form%-22s z3 ${if zok then "unsat" else "-"}%-6s ${zs}%7d ms   " +
            f"vampire ${if vok then "refutation" else "-"}%-11s ${vs}%7d ms (budget ${budget}s each)")
    (zok, vok, f"; $form%-22s z3 ${if zok then "unsat" else zout.linesIterator.toList.lastOption.getOrElse("?").trim}%-10s " +
                f"vampire ${if vok then "refutation" else "none"}%-10s (budget ${budget}s each; " +
                "timings are in the run log, not here — a wall clock in a committed artifact makes " +
                "it differ from itself on every run)")

  def runSmtFile(name: String, content: String): Unit =
    // 2E.5: the `; TRUSTS:` header is REQUIRED and read here, before any row is written; a row's
    // verdict is qualified by what the header trusts (`Certified.qualify`), so a cell resting on an
    // open row or an outside construct cannot be written as an unqualified PROVED.
    val trusts = Certified.trustsOf(content, name)
    if content.contains("TRIVIAL-NO-OBLIGATION") then
      trivialCount += 1; write(smtDir, name, content); statusRows += s"$name\t-\t-\tTRIVIAL"; return
    if content.contains("IDENTICAL-STRUCTURE-NO-EQUIVALENCE-OBLIGATION") then
      // the two sides compile to the SAME shared macro: `(= (m p) (m p))` is `true` by macro
      // expansion, so there is no obligation to run a prover on.  Recorded, never faked.
      identCount += 1; write(smtDir, name, content); statusRows += s"$name\t-\t-\tIDENTICAL-STRUCTURE"; return
    if content.contains("LAW-JUSTIFIED-NO-RESIDUAL") then
      // proof-carrying: every differing pair is a verified instance of the ∀-certified optimiser
      // law set (replayed syntactically); the universal certificates in proofs/ ARE the proof.
      lawCount += 1; write(smtDir, name, content)
      statusRows += s"$name\t-\t-\t${Certified.qualify("LAW-JUSTIFIED", trusts)}"; return
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
      statusRows += s"$name\t${if zok then "unsat" else "-"}\t${if vok then "proved" else "-"}\t${Certified.qualify("PROVED", trusts)}"
    else
      recordInstance(name, content, zok, vok, List(log), trusts)

  /** THE ONE SIZE CAP ON A COMMITTED OBLIGATION, and the reason it is not a weakening.
   *
   *  `puzzle15-space` renders to 174 MB — two denotations of ~10^8 characters on two lines.  That is
   *  past GitHub's 100 MB per-file limit, so the artifact cannot be pushed at all, and it is past
   *  what any prover consumed: z3 and vampire both hit the 60 s budget on it, which is why the cell
   *  is OPEN in the first place.  A blob that size is not review material either — it cannot be
   *  opened, and it is a deterministic function of the corpus and this emitter.
   *
   *  So an oversized body is replaced by an ELIDED-GOAL record naming its exact byte count and
   *  SHA-256, and NOTHING ELSE CHANGES.  In particular: the provers ran on the FULL text (that is
   *  what the attempt log in the header reports), the goal was NOT weakened to something provable,
   *  the cell is still OPEN, and it still does not count as discharged.  The full body is written to
   *  `target/pipeline-elided/` on every run — git-ignored, so a reader who wants the bytes has them
   *  locally without the tree carrying them.
   *
   *  The cap is 2 MB against a largest legitimate artifact of 828 KB (`puzzle3-full-space`), so it
   *  fires on exactly the one cell that cannot be committed and leaves every other byte-identical.
   *  A cell that CROSSES the cap will show up as a golden-file change, which is the intent: the
   *  emitter growing an artifact past what a repository can hold is a fact worth surfacing. */
  val bodyCapBytes = 2 * 1024 * 1024

  def cappedBody(name: String, body: String): String =
    if body.length <= bodyCapBytes then body
    else
      val bytes = body.getBytes("UTF-8")
      val sha = java.security.MessageDigest.getInstance("SHA-256").digest(bytes)
                  .map(b => f"$b%02x").mkString
      val spill = new java.io.File(RunEnvironment.repoRoot, "target/pipeline-elided")
      spill.mkdirs()
      java.nio.file.Files.write(new java.io.File(spill, name).toPath, bytes)
      Loaders.note(s"[pipeline] $name: goal body ELIDED (${bytes.length} B > $bodyCapBytes B); " +
                   s"full text at target/pipeline-elided/$name")
      "; ELIDED-GOAL: THE OBLIGATION IS NOT IN THIS FILE.  It is too large to commit, and is recorded\n" +
      "; by identity instead.  IT WAS RENDERED IN FULL AND BOTH PROVERS WERE RUN ON IT — the ATTEMPT\n" +
      "; LOG above is that run.  The goal was NOT weakened, NOT folded, and is NOT counted as\n" +
      "; discharged; this cell is OPEN exactly as the header says.\n" +
      s"; rendered size   ${bytes.length} bytes\n" +
      s"; sha256          $sha\n" +
      "; regenerate      ZIPPY_REGENERATE=1 sbt --server 'testOnly morkl.EquivPipelineTest'\n" +
      "; full text       target/pipeline-elided/" + name + " (git-ignored; written on every run)\n" +
      "; WHY: 174 MB of rendered denotation is past GitHub's 100 MB per-file limit and past what\n" +
      "; either prover consumed.  See `bodyCapBytes` in EquivPipelineTest for the whole argument.\n"

  /** Record an instance obligation's outcome: PROVED (with which provers) or, when NEITHER prover
   *  discharged it inside the budget, an honest PROVER-BUDGET-EXCEEDED marker carrying the attempt
   *  log in the file header — never a silently-accepted or weakened goal. */
  def recordInstance(name: String, content: String, zok: Boolean, vok: Boolean, log: List[String],
                     trusts: Vector[Certified.Trust] = Vector.empty): Unit =
    if zok || vok then
      val hdr = s"; PROVER LOG (both provers are run on every obligation; verdicts also in STATUS.tsv)\n" +
                log.mkString("\n") + "\n"
      write(smtDir, name, hdr + cappedBody(name, content))
      statusRows += s"$name\t${if zok then "unsat" else "-"}\t${if vok then "proved" else "-"}\t${Certified.qualify("PROVED", trusts)}"
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
      write(smtDir, name, hdr + cappedBody(name, content))
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

  /** SpaceZipper → the structurally matching Space term: `Lit ↦ Literal`, `Opaque ↦ Mention`,
   *  `Subtraction(x, RestrictionNode(x, y))` with the SAME `x` object ↦ `Raffination` (that sharing is
   *  how `SpaceZipper.raffination` builds it), `Descend ↦ Unwrap`.  Total over every node. */
  def spaceOfZipper(z: SpaceZipper): Space = z match
    case SpaceZipper.Opaque(m) => Mention(m)
    case SpaceZipper.Lit(t) => Literal(t.toSpaceValue)
    case SpaceZipper.Union(a, b) => Union(spaceOfZipper(a), spaceOfZipper(b))
    case SpaceZipper.Intersection(a, b) => Intersection(spaceOfZipper(a), spaceOfZipper(b))
    case SpaceZipper.Subtraction(a, SpaceZipper.RestrictionNode(x, y)) if x eq a =>
      Raffination(spaceOfZipper(a), spaceOfZipper(y))
    case SpaceZipper.Subtraction(a, b) => Subtraction(spaceOfZipper(a), spaceOfZipper(b))
    case SpaceZipper.Composition(a, b) => Composition(spaceOfZipper(a), spaceOfZipper(b))
    case SpaceZipper.Prefix(rem, src) => Wrap(spaceOfZipper(src), Path.Constant(PathValue(Interner.uninternPath(rem))))
    case SpaceZipper.RestrictionNode(x, p) => Restriction(spaceOfZipper(x), spaceOfZipper(p))
    case SpaceZipper.Descend(src, ks) => Unwrap(spaceOfZipper(src), Path.Constant(PathValue(Interner.uninternPath(ks))))
    case SpaceZipper.TailsUnion(src) => TailsUnion(spaceOfZipper(src))
    case SpaceZipper.TailsIntersection(src) => TailsIntersection(spaceOfZipper(src))

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
                   smtA0: Space = null, smtB0: Space = null,
                   withEgg: Boolean = true, extraTrusts: Vector[Certified.Trust] = Vector.empty): String =
    val (sideA, sideB) = (SmtDiff.alphaNorm(sideA0), SmtDiff.alphaNorm(sideB0))
    val (smtA, smtB) = (Option(smtA0).getOrElse(sideA), Option(smtB0).getOrElse(sideB))
    // O10b — WHAT A CELL WITH A RESIDUAL CUT ACTUALLY CLAIMS.
    //
    // `unrollControl` cuts a recursive call it cannot lower past depth `k` and replaces it with a
    // fresh free input, so the obligation such a cell states is "the two k-UNROLLINGS agree for all
    // values of that input" — NOT "the two recursions agree".  Getting from one to the other needs
    // k-unrolling equivalence for ALL k plus omega-continuity, which is registry row O10b and is
    // OPEN: the pipeline emits k = 1 and k = 2 only, so the antecedent is never established.
    //
    // The claim was correct in the registry and OVERSTATED everywhere else — such a cell counted as
    // REAL and fed the end-to-end wording in README.md.  It is now stamped in the file, given its own
    // kind in proofs/pipeline/DECLARED.tsv, and excluded from any end-to-end equivalence claim.
    val cuts = AgnosticPipeline.residualsOf(smtA) ++ AgnosticPipeline.residualsOf(smtB)
    // THE CUT IS LIFTED, NOT STAMPED AS BOUNDED (plan.md 2E.1, O10b mechanized).  The two sides cut the
    // SAME routine at the same depth with the same arguments (`alignCuts` asserted it in graphCells), so
    // the recursion is identical on both sides and the cut stands for the same free input `X` in both.
    // A claim that holds for EVERY value of that input is then a claim about the recursion itself:
    // proofs/lean/Zippy/Positive.lean#Zippy.Space.fixpoint_denT_eq_of_step_eq — one-step agreement
    // for every value of the recursion variable gives agreement of the fixpoints, no `k` involved.
    val boundedNote =
      if cuts.isEmpty then ""
      else
        val ks = cuts.values.map(_.depth).toVector.distinct.sorted
        val descs = cuts.values.map(_.canonical).toVector.sorted.mkString("\n;   ")
        s"; RESIDUAL CUT (k=${ks.mkString(",")}) LIFTED: the sides carry ${cuts.size} residual cut(s), the SAME on both sides:\n" +
        s";   $descs\n" +
        "; so this cell's claim is quantified over the cut's free input, and holds for EVERY value of it;\n" +
        "; the recursion is identical on both sides, so by proofs/lean/Zippy/Positive.lean#\n" +
        "; Zippy.Space.fixpoint_denT_eq_of_step_eq (2E.1) the claim about the unrollings IS the claim\n" +
        "; about the recursion.  (Formerly stamped BOUNDED-UNROLLING under O10b, which is now mechanized.)\n"
    randomGate(s"$name-$stage", sideA, sideB)
    // DIFF-DECOMPOSED egg leg (mirrors the smt design): the sides are identical except at the
    // optimiser-rewritten subterm pairs; each SMALL pair is checked observationally with its
    // surrounding binders freed (path binders -> fresh never-used items, behaving generically:
    // the rules only compare items by Eqi; rest-mentions -> opaque (Src (N …))); whole-program
    // equivalence follows by congruence.  The ∀-binder generality is the smt leg's theorem.
    val ms = SmtDiff.diff(sideA, sideB, Nil, Nil)
    // proof-carrying partition (with refinement): justified law instances vs residual pairs
    val (jstP, resP) = SmtDiff.partition(sideA, sideB)
    // what this cell's claim rests on: the laws that justify its pairs, plus what the caller knows
    // a TRIVIAL cell (no differing pair) is a statement about syntax and rests on nothing; every other
    // cell rests on the laws that justify its pairs plus what the caller knows about the rendering
    val trusts: Vector[Certified.Trust] =
      if ms.isEmpty then Vector.empty
      else (jstP.flatMap((_, law) => lawNames(law)).distinct.sorted.map(Certified.Trust.Law(_)).toVector ++ extraTrusts).distinct
    val sb = new StringBuilder
    if !withEgg then ()
    else if ms.isEmpty then
      sb.append(s"; AUTO-GENERATED pipeline $stage ($name) — DATA-AGNOSTIC.\n")
      sb.append(boundedNote)
      sb.append(s"; TRIVIAL-NO-OBLIGATION: sides are syntactically identical after alpha-normalisation —\n")
      sb.append(s"; the transformation is structure-preserving here; nothing to prove.\n")
      runEggFile(s"$name-$stage-agnostic.egg", sb.toString)
    else
      val ctx = new AgnosticPipeline.RenderCtx
      sb.append(boundedNote)
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
          ArtifactSink.write(new java.io.File(pipeDir, s"$name-$stage-agnostic.egg"), marker + sb.toString)
    val smtText = Certified.trustsHeader(trusts) + s"\n; BOUNDARY: $stage\n" + boundedNote +
      SmtDiff.obligationsFile(s"pipeline $stage ($name), data-agnostic", smtA, smtB)
    runSmtFile(s"$name-$stage-agnostic.smt2", smtText)
    smtText

  /** the law NAMES inside a justification string (`unwrap-merge`, `replay: a + b`, `reduce-join: …`) */
  def lawNames(just: String): Vector[String] =
    just.stripPrefix("replay: ").stripPrefix("reduce-join: ").stripPrefix("join: ").split(" \\+ ").map(_.trim).filter(_.nonEmpty).toVector

  /** a DETERMINISTIC fingerprint of a term.  `Space.show` prints a `Literal`'s `Set` in hash order,
   *  which differs between JVM runs (measured: nqueens' step hashes changed on a verify run with
   *  nothing else different); `LeanRender.space` sorts literal paths, so its text is stable. */
  def sha12(s: Space): String =
    // every Literal becomes a Mention whose name is its SORTED path list, so `show` is order-free
    // (a grounded node makes LeanRender.space throw, so it is not the fallback either)
    val canon = subs(SmtDiff.alphaNorm(s))(spost = { case Literal(v) =>
      Mention(SpaceMention("lit:" + v.paths.toList.map(_.items.mkString(".")).sorted.mkString("|"))) })
    val d = java.security.MessageDigest.getInstance("SHA-256").digest(canon.show.getBytes("UTF-8"))
    d.take(6).map(b => f"$b%02x").mkString

  def ctorName(x: Space): String = x.getClass.getSimpleName.stripSuffix("$")

  def binderNames(x: Space): Vector[String] =
    collect(x)({ case _: Iteration => "Iteration"; case _: Fixpoint => "Fixpoint"; case _: Fold => "Fold" })._1.map(_._2).distinct
  def callNames(x: Space): Vector[String] =
    collect(x)({ case c: Space.Call => c.r.s })._1.map(_._2).distinct

  /** every Space/Path constructor name occurring in a term, in encounter order */
  def shellCtors(x: Space): Vector[String] =
    val out = scala.collection.mutable.LinkedHashSet.empty[String]
    def gp(p: Path): Unit =
      out += p.getClass.getSimpleName.stripSuffix("$")
      p match
        case Path.Concat(l, r) => gp(l); gp(r)
        case Path.GroundedPP(q, _) => gp(q)
        case Path.GroundedSP(s, _) => go(s)
        case _ => ()
    def go(s: Space): Unit =
      out += ctorName(s)
      s match
        case Union(a, b) => go(a); go(b)
        case Intersection(a, b) => go(a); go(b)
        case Subtraction(a, b) => go(a); go(b)
        case Restriction(a, b) => go(a); go(b)
        case Raffination(a, b) => go(a); go(b)
        case Composition(a, b) => go(a); go(b)
        case Wrap(src, p) => go(src); gp(p)
        case Unwrap(src, p) => go(src); gp(p)
        case Singleton(p) => gp(p)
        case TailsUnion(src) => go(src)
        case TailsIntersection(src) => go(src)
        case Iteration(src, _, _, body) => go(src); go(body)
        case Fixpoint(init, _, body) => go(init); go(body)
        case Fold(src, ini, _, _, _, body, upd) => go(src); gp(ini); go(body); gp(upd)
        case Call(_, refs, ms) => refs.foreach(gp); ms.foreach(go)
        case Range(a, _, _) => go(a)
        case GroundedPS(p, _) => gp(p)
        case GroundedSS(a, _) => go(a)
        case Empty | Literal(_) | Mention(_) => ()
    go(x); out.toVector

  def constPath(p: Path): Boolean = p match
    case Path.Constant(_) => true
    case Path.Concat(l, r) => constPath(l) && constPath(r)
    case _ => false

  // ==============================================================================================
  // THE HOLE ABSTRACTION for the zipper boundary (plan.md 2A.4)
  // ==============================================================================================
  /** The maximal subterms `transpileZ` MATERIALISES — `traversal(evalI(...))` for control flow, `Range`,
   *  `Call` and grounded nodes, the trie-level meet for `TailsIntersection`, and any `Singleton`/`Wrap`/
   *  `Unwrap` whose path is not constant — replaced by fresh opaque mentions, so that the remaining SHELL
   *  is exactly the fragment the refinement theorem covers with its `lit` boundaries.  Returns the shell
   *  and the holes in encounter order. */
  def abstractHoles(s: Space): (Space, Vector[(SpaceMention, Space)]) =
    val holes = scala.collection.mutable.ArrayBuffer.empty[(SpaceMention, Space)]
    def hole(x: Space): Space =
      val m = SpaceMention(s"#hole${holes.size}"); holes += ((m, x)); Mention(m)
    def go(x: Space): Space = x match
      case Empty | Literal(_) | Mention(_) => x
      case Singleton(p) => if constPath(p) then x else hole(x)
      case Union(a, b) => Union(go(a), go(b))
      case Intersection(a, b) => Intersection(go(a), go(b))
      case Subtraction(a, b) => Subtraction(go(a), go(b))
      case Restriction(a, b) => Restriction(go(a), go(b))
      case Raffination(a, b) => Raffination(go(a), go(b))
      case Composition(a, b) => Composition(go(a), go(b))
      case Wrap(src, p) => if constPath(p) then Wrap(go(src), p) else hole(x)
      case Unwrap(src, p) => if constPath(p) then Unwrap(go(src), p) else hole(x)
      case TailsUnion(src) => TailsUnion(go(src))
      case _ => hole(x)   // TailsIntersection, Range, Iteration, Fixpoint, Fold, Call, grounded
    (go(s), holes.toVector)

  /** Run the whole matrix for one cornerstone: two space cells, two zipper cells, two graph cells. */
  def pipeline(name: String, prog: Space, sc: SpaceContext, rc: PartialFunction[RoutinePtr, Routine]): Unit =
    given PathContext = pc0
    given SpaceContext = sc
    given PartialFunction[RoutinePtr, Routine] = rc
    val reference = eval(prog)
    // the artifacts the previous matrix wrote and this one does not: gone at the source (2A.2)
    dropFallback(s"$name-space.egg", s"$name-space-impl.egg", s"$name-space-lit.egg",
                 s"$name-zipper.egg", s"$name-zipper-lit.egg", s"$name-zipper-virtual.egg",
                 s"$name-zipper-agnostic.egg", s"$name-graph.egg", s"$name-graph-lit.egg",
                 s"$name-graph-agnostic.egg")
    for stale <- Seq(s"$name-space-agnostic.smt2") do
      val f = new java.io.File(smtDir, stale)
      if ArtifactSink.delete(f) then Loaders.note(s"[pipeline] removed $stale (the space-agnostic cell is the .egg)")
    spaceCells(name, prog, reference)
    zipperCells(name, prog, sc, rc, reference)
    graphCells(name, prog, reference)
    binderCensus(name, prog)
    coverage(name, prog, SC.reduceTraced(prog)._2, abstractHoles(prog)._2)
    writeCoverage()
    Loaders.note(s"[pipeline] $name markers so far: real=$realCount trivial=$trivialCount " +
                 s"law-justified=$lawCount budget=$budgetCount identical=$identCount single-side=$singleSideCount")
    writeStatus()

  // ==============================================================================================
  // SPACE — the trace (plan.md 2A.3, 2A.5)
  // ==============================================================================================
  def spaceCells(name: String, prog: Space, reference: SpaceValue)
                (using PathContext, SpaceContext, PartialFunction[RoutinePtr, Routine]): Unit =
    val (reduced, steps) = SC.reduceTraced(prog)
    val bad = SC.verifyTrace(steps)
    assert(bad.isEmpty, s"$name: the reduction trace is not an honest derivation: ${bad.mkString("; ")}")
    assertEquals(eval(reduced), reference, s"$name: SC.reduce changed the denotation on this input")
    // PER-STEP EXECUTOR DIFFERENTIAL: every step's result denotes the reference on this input.  Each
    // step is a ∀-law, so this is cross-validation of the law's implementation on one instance, not
    // the proof; the proof is the certificate the step names.
    var checked = 0
    for st <- steps do
      assertEquals(eval(st.after), reference, s"$name: step `${st.law}` changed the denotation on this input")
      checked += 1
    val laws = steps.map(_.law).distinct.sorted
    val trusts = laws.map(Certified.Trust.Law(_))
    if steps.isEmpty then
      assert(SmtDiff.alphaNorm(prog) == SmtDiff.alphaNorm(reduced),
             s"$name: no trace step fired yet SC.reduce returned a different term")
      def trivial(form: String, art: String) =
        Certified.trustsHeader(Vector.empty) + "\n; BOUNDARY: space\n" +
        s"; AUTO-GENERATED pipeline stage 1 ($name) — $form.\n" +
        s"; TRIVIAL-NO-OBLIGATION: SC.reduce is the IDENTITY on this program — no source law fires\n" +
        s"; (SC.reduceTraced recorded 0 steps) and the sides are alpha-equal; nothing to prove.  This\n" +
        s"; is a statement about the optimiser on this stone, not a certificate of anything it did.\n" +
        (if art.endsWith(".egg") then "" else "")
      runSmtFile(s"$name-space.smt2", trivial("INSTANCE", "smt2"))
      runEggFile(s"$name-space-agnostic.egg", trivial("DATA-AGNOSTIC", "egg"))
      return
    // ---- the instance record: the chain, composed, with the differential
    val sb = new StringBuilder
    sb.append(Certified.trustsHeader(trusts)).append("\n; BOUNDARY: space\n")
    sb.append(s"; AUTO-GENERATED pipeline stage 1 ($name) — INSTANCE: the program vs SC.reduce(program).\n")
    sb.append(s"; LAW-JUSTIFIED-NO-RESIDUAL: the two sides are joined by ${steps.size} TRACE STEP(S), each a\n")
    sb.append(s"; re-applied instance of a certified optimiser law (SC.verifyTrace: 0 failure(s); the laws'\n")
    sb.append(s"; ∀-certificates are in proofs/laws/REGISTRY.tsv), composed end to end: the `after` of every\n")
    sb.append(s"; step is the `before` of the next.  A step is a whole-term congruence (one law may rewrite\n")
    sb.append(s"; several positions at once); the ∀-certificate covers every instance.\n")
    sb.append(s"; INSTANCE-DIFFERENTIAL: $checked of ${steps.size} step results evaluate to the reference on this input.\n")
    sb.append(s"; laws used: ${laws.mkString(", ")}\n")
    for (st, i) <- steps.zipWithIndex do
      sb.append(f"; STEP $i%3d  ${st.law}%-28s  ${sha12(st.before)} -> ${sha12(st.after)}   certificate(s): ${SmtDiff.certificateOf(st.law)}\n")
    sb.append(s"; endpoints: ${sha12(prog)} (program) -> ${sha12(reduced)} (SC.reduce)\n")
    runSmtFile(s"$name-space.smt2", sb.toString)
    // ---- the agnostic egg: each step's differing pairs re-derived under the certified movement rules
    val ctx = new AgnosticPipeline.RenderCtx
    val lets = new StringBuilder; val checks = new StringBuilder
    var emitted = 0
    val stepNotes = new StringBuilder
    // ONE let per distinct rendered term: two positions rewritten to the SAME result share a name,
    // so no two lets ever bind byte-identical terms (the audit's vacuity detector rejects that
    // shape, and it is right to — measured on nqueens step 0, two of four pairs had one right side).
    val named = scala.collection.mutable.LinkedHashMap.empty[String, String]
    def nameOf(rendered: String, hint: String): String =
      named.getOrElseUpdate(rendered, { lets.append(s"(let $hint (Term $rendered))\n"); hint })
    for (st, i) <- steps.zipWithIndex do
      val l = SmtDiff.alphaNorm(AgnosticPipeline.unrollControl(st.before, 2))
      val r = SmtDiff.alphaNorm(AgnosticPipeline.unrollControl(st.after, 2))
      val ms = SmtDiff.diff(l, r, Nil, Nil)
      var pairs = 0
      for ((a, b, ps, ss), j) <- ms.zipWithIndex do
        val penv = ps.zipWithIndex.map((n, k) => n -> (900000 + i * 1000 + j * 10 + k).toString).toMap
        val senv = ss.zipWithIndex.map((n, k) => n -> s"(Src (N ${Interner.intern(s"$$free$${i}_$${j}_$$k$$$n")}))").toMap
        val ra = AgnosticPipeline.renderZ(a, penv, senv, ctx, false)
        val rb = AgnosticPipeline.renderZ(b, penv, senv, ctx, false)
        if ra != rb then
          emitted += 1; pairs += 1
          val na = nameOf(ra, s"$$s${i}_$j"); val nb = nameOf(rb, s"$$t${i}_$j")
          checks.append(s"(check (= $na $nb))\n")
      stepNotes.append(f"; STEP $i%3d  ${st.law}%-28s  $pairs differing pair(s)   certificate(s): ${SmtDiff.certificateOf(st.law)}\n")
    val head = new StringBuilder
    head.append(Certified.trustsHeader(trusts)).append("\n; BOUNDARY: space\n")
    head.append(s"; AUTO-GENERATED pipeline stage 1 ($name) — DATA-AGNOSTIC: the program vs SC.reduce(program).\n")
    if emitted == 0 then
      head.append(s"; LAW-JUSTIFIED-NO-RESIDUAL: ${steps.size} trace step(s) (SC.verifyTrace: 0 failure(s)); every\n")
      head.append(s"; differing pair renders identically after freeing binders (the rewrite is absorbed by the\n")
      head.append(s"; rendering), so the steps' ∀-certificates carry the cell and no egg run is needed.\n")
      head.append(stepNotes)
      runEggFile(s"$name-space-agnostic.egg", head.toString)
    else
      head.append(s"; ${steps.size} trace step(s), ${emitted} differing subterm pair(s) in total, each checked OBSERVATIONALLY\n")
      head.append(s"; under the certified movement rules with surrounding binders freed; each step is also a\n")
      head.append(s"; certified ∀-law (the certificates below), so a pair the egg ladder does not reach is carried\n")
      head.append(s"; by its certificate and never by a budget.\n")
      head.append(stepNotes)
      head.append("(include \"prelude.egg\")\n")
      if ctx.text.nonEmpty then head.append(ctx.text).append('\n')
      val sched = if lets.toString.contains("(Fix ") then "(run-schedule (repeat ROUNDS (run) (run park)))" else "(run ROUNDS)"
      val body = head.toString + lets.toString + sched + "\n" + checks.toString
      if runEggFileOpt(s"$name-space-agnostic.egg", body) then realCount += 1
      else
        lawCount += 1
        val marker = s"; LAW-JUSTIFIED: the movement observations did not converge within the rounds ladder for\n" +
                     s"; some pair; every step is a certified ∀-law (certificates in the STEP lines below), and\n" +
                     s"; those certificates carry the cell (plan.md 2A.5: decomposition through the trace, never\n" +
                     s"; a budget).\n"
        ArtifactSink.write(new java.io.File(pipeDir, s"$name-space-agnostic.egg"), marker + body)

  // ==============================================================================================
  // ZIPPER — the refinement theorem, instantiated (plan.md 2A.4)
  // ==============================================================================================
  def zipperCells(name: String, prog: Space, sc: SpaceContext, rc: PartialFunction[RoutinePtr, Routine],
                  reference: SpaceValue)(using PathContext, SpaceContext, PartialFunction[RoutinePtr, Routine]): Unit =
    // the INSTANCE differential: the real transpiled zipper materialises to the reference
    val zProg = transpileZ(prog)(using pc0, Map.from(sc.asInstanceOf[SpaceContextMap].m.map((k, v) => k -> ITrie.fromSpaceValue(v))), rc)
    assertEquals(SpaceZipper.materialize(zProg).toSpaceValue, reference, s"$name: zipper executor disagrees")
    // the SHELL, transpiled with every source opaque, read back
    val (shell, holes) = abstractHoles(prog)
    val zShell = transpileZ(shell)(using pc0, Map.empty, PartialFunction.empty)
    val back = spaceOfZipper(zShell)
    val (jst, res) = SmtDiff.partition(back, shell)
    assert(res.isEmpty, s"$name: the shell read back from the zipper differs from the shell by ${res.size} pair(s) " +
                        s"no certified law justifies: ${res.take(2).mkString("; ")}")
    val laws = jst.flatMap((_, law) => lawNames(law)).distinct.sorted
    val trusts = (Vector(Certified.Trust.Law("zipper-refinement")) ++ laws.map(Certified.Trust.Law(_))).distinct
    def cell(form: String, extra: String): String =
      Certified.trustsHeader(trusts) + "\n; BOUNDARY: zipper\n" +
      s"; AUTO-GENERATED pipeline stage 2 ($name) — $form: transpileZ(program) vs the program.\n" +
      s"; LAW-JUSTIFIED-NO-RESIDUAL: an INSTANCE of the universal zipper refinement theorem —\n" +
      s";   proofs/zipper_refinement.smt2 (first-order, over the key-free local algebra; PROVED) and\n" +
      s";   proofs/lean/Zippy/Zipper.lean#Zippy.Zip.refinement (every constructor, boundaries named).\n" +
      s"; SHELL: ${SCStats.of(shell).total} node(s) transpiled with EVERY source opaque (SpaceZipper.Opaque); read back\n" +
      s"; SHELL CONSTRUCTORS: ${shellCtors(shell).mkString(", ")}\n" +
      s"; PROGRAM CONSTRUCTORS: ${shellCtors(prog).mkString(", ")}\n" +
      s"; BINDERS: ${binderNames(prog).mkString(", ")}\n" +
      s"; CALLS: ${callNames(prog).mkString(", ")}\n" +
      s"; through spaceOfZipper it is " +
      (if jst.isEmpty then "alpha-EQUAL to the shell.\n"
       else s"equal to the shell up to ${jst.size} law-justified pair(s): ${laws.mkString(", ")}.\n") +
      s"; HOLES (materialised by transpileZ and evaluated by the executor on BOTH sides — the theorem's\n" +
      s"; `lit` boundaries): ${holes.size}\n" +
      holes.map((m, h) => s";   ${m.s} = ${ctorName(h)}").mkString("\n") + (if holes.isEmpty then "" else "\n") +
      extra
    runSmtFile(s"$name-zipper-agnostic.smt2", cell("DATA-AGNOSTIC", ""))
    runSmtFile(s"$name-zipper.smt2", cell("INSTANCE",
      "; INSTANCE-DIFFERENTIAL: SpaceZipper.materialize(transpileZ(program)) == eval(program) on this input (Scala assertEquals).\n"))

  // ==============================================================================================
  // GRAPH — optimize's action, on the symbolic program
  // ==============================================================================================
  def graphCells(name: String, prog: Space, reference: SpaceValue)
                (using PathContext, SpaceContext, PartialFunction[RoutinePtr, Routine]): Unit =
    val rc = summon[PartialFunction[RoutinePtr, Routine]]
    val uO = AgnosticPipeline.symbolic(prog)
    // obligation: terminating/REGISTRY.tsv O10c — a residual cut is only sound if BOTH sides cut the
    // same thing, arguments included.  The two sides here are built from ONE symbolic program, so the
    // cuts are the same by construction; asserted rather than assumed.
    val r = Routine(RoutinePtr(name + "_ag"), Vector.empty, freeMentions(uO), uO)
    val optG = untranspileTop(optimize(transpile(r)))
    val plainG = untranspileTop(transpile(r))
    val al = AgnosticPipeline.alignCuts(SmtDiff.alphaNorm(optG), SmtDiff.alphaNorm(plainG))
    assert(al.aligned, s"$name: the graph sides cut different residuals — ${al.report}")
    // inlining an acyclic Call through `unrollControl` is the substitution premise (O6a)
    // what rendering the symbolic program in FOL rests on: `Certified.boundary` names every construct
    // outside the certified algebra (Range -> T5, grounded -> T6, a non-positive Fixpoint), and an
    // inlined acyclic Call is the substitution premise O6a
    val hasCall = collect(prog)({ case c: Space.Call if rc.isDefinedAt(c.r) => c })._1.nonEmpty
    val extra = (Certified.boundary(uO) ++ (if hasCall then Vector(Certified.Trust.Open("O6a")) else Vector.empty)).distinct
    val agnostic = agnosticLegs(name, "graph", optG, plainG, withEgg = false, extraTrusts = extra)
    // the INSTANCE cell: the same obligation (it is data-agnostic) plus the executor differential
    val eO = EquivPipeline.expand(prog)
    val g = optimize(transpile(Routine(RoutinePtr(name), Vector.empty, Vector.empty, eO)))
    assertEquals(runGraphT(g).toSpaceValue, reference, s"$name: graph executor disagrees")
    val hdrLine = agnostic.linesIterator.toList
    val instance = hdrLine.head + "\n" +
      "; INSTANCE-DIFFERENTIAL: GraphExec.runGraphT(optimize(transpile(program))) == eval(program) on this input\n" +
      "; (Scala assertEquals); the obligation below is the data-agnostic one, which covers this input.\n" +
      hdrLine.tail.mkString("\n") + "\n"
    runSmtFile(s"$name-graph.smt2", instance.replace("data-agnostic", "instance (data-agnostic obligation + differential)"))

  // ==============================================================================================
  // COVERAGE (plan.md 2A.6): every constructor, binder, call pattern, optimiser law, recursive
  // transformation and backend boundary a cornerstone exercises, with the artifact whose checked
  // chain mentions it.  `scripts/audit_pipeline_markers.py --accept` verifies every row against the
  // artifact it names and fails on a stone with no row of a required kind.
  // ==============================================================================================
  val coverageRows = scala.collection.mutable.ArrayBuffer.empty[String]
  def coverage(name: String, prog: Space, steps: Vector[SC.Step], holes: Vector[(SpaceMention, Space)]): Unit =
    val ctors = scala.collection.mutable.LinkedHashSet.empty[String]
    val binders = scala.collection.mutable.LinkedHashSet.empty[String]
    val calls = scala.collection.mutable.LinkedHashSet.empty[String]
    def gp(p: Path): Unit =
      ctors += p.getClass.getSimpleName.stripSuffix("$")
      p match
        case Path.Concat(l, r) => gp(l); gp(r)
        case Path.GroundedPP(q, _) => gp(q)
        case Path.GroundedSP(x, _) => go(x)
        case _ => ()
    def go(x: Space): Unit =
      ctors += ctorName(x)
      x match
        case Union(a, b) => go(a); go(b)
        case Intersection(a, b) => go(a); go(b)
        case Subtraction(a, b) => go(a); go(b)
        case Restriction(a, b) => go(a); go(b)
        case Raffination(a, b) => go(a); go(b)
        case Composition(a, b) => go(a); go(b)
        case Wrap(src, p) => go(src); gp(p)
        case Unwrap(src, p) => go(src); gp(p)
        case Singleton(p) => gp(p)
        case TailsUnion(src) => go(src)
        case TailsIntersection(src) => go(src)
        case Iteration(src, _, _, body) => binders += "Iteration"; go(src); go(body)
        case Fixpoint(init, _, body) => binders += "Fixpoint"; go(init); go(body)
        case Fold(src, ini, _, _, _, body, upd) => binders += "Fold"; go(src); gp(ini); go(body); gp(upd)
        case Call(r, refs, ms) => calls += r.s; refs.foreach(gp); ms.foreach(go)
        case Range(a, _, _) => go(a)
        case GroundedPS(p, _) => gp(p)
        case GroundedSS(a, _) => go(a)
        case Empty | Literal(_) | Mention(_) => ()
    go(prog)
    val zipperArt = s"proofs/pipeline/$name-zipper.smt2"
    val spaceArt = s"proofs/pipeline/$name-space.smt2"
    val graphArt = s"proofs/pipeline/$name-graph-agnostic.smt2"
    // a constructor is "in a checked chain" where an artifact names it: the zipper cell lists every
    // hole by constructor and the shell; constructors of the shell are named in the SHELL line below
    for c <- ctors do coverageRows += s"$name\tconstructor\t$c\t$zipperArt"
    for b <- binders do coverageRows += s"$name\tbinder\t$b\t$zipperArt"
    for c <- calls do coverageRows += s"$name\tcall\t$c\t$zipperArt"
    for l <- steps.map(_.law).distinct.sorted do coverageRows += s"$name\tlaw\t$l\t$spaceArt"
    for (m, h) <- holes do coverageRows += s"$name\thole\t${ctorName(h)}\t$zipperArt"
    for b <- Seq("space", "zipper", "graph") do
      coverageRows += s"$name\tboundary\t$b\t" + (b match { case "space" => spaceArt; case "zipper" => zipperArt; case _ => graphArt })
  def writeCoverage(): Unit =
    val hdr = "# COVERAGE (plan.md 2A.6) — every construct a cornerstone exercises, and the artifact whose checked\n" +
              "# chain mentions it.  Written by EquivPipelineTest; verified row by row by\n" +
              "# `scripts/audit_pipeline_markers.py --accept` (the named artifact exists and mentions the item).\n" +
              "# cornerstone\tkind\titem\tartifact\n"
    ArtifactSink.write(new java.io.File(smtDir, "COVERAGE.tsv"), hdr + coverageRows.sorted.mkString("\n") + "\n")

  /** 1D.4's census, kept as the gate it is: do the binders survive `expandKeepBinders`? */
  def binderCensus(name: String, prog: Space)
                  (using PathContext, SpaceContext, PartialFunction[RoutinePtr, Routine]): Unit =
    try
      val bO = EquivPipeline.expandKeepBinders(prog)
      assertEquals(eval(bO)(using pc0, SpaceContextMap(Map.empty), PartialFunction.empty), eval(prog),
                   s"$name: binder-preserving expansion changed semantics")
      binderKept += name
    catch case e: IllegalStateException =>
      println(s"[pipeline] $name: binder-preserving sides UNAVAILABLE — ${e.getMessage}")
      binderFallback += name
    println(f"[pipeline] $name%-12s control flow: " +
            (if binderKept(name) then "BINDERS KEPT (Iteration/Fixpoint reach the renderers)"
             else "EXECUTED (fell back to `expand` — see the note above for which node forced it)"))

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

  // 1D.4 — THE BINDER CENSUS IS A GATE, NOT A PRINTOUT.
  //
  // `binderKept` / `binderFallback` were PRINTED per stone, which made "the binders survived" a
  // measured claim rather than a property of the code path — the right first step, and the reason
  // the two failing stones were visible at all.  It is now a GATE, because a printed census is a
  // census nobody has to act on, and what it measures is exactly the difference between a stage-1
  // artifact that certifies THE OPTIMISER and one that certifies THE EXECUTOR: `expand` evaluates
  // the control flow, so a stone on the fallback path emits a claim about a ground computation.
  //
  // IT WENT FROM 5 OF 7 TO 7 OF 7, and not by loosening anything: `expandKeepBinders` now INLINES
  // an acyclic `Call` through `Subst` (plan.md 1D.4, and 2A.2's first clause) instead of refusing
  // it.  `puzzle15` and `nqueens` were the two fallbacks and both were a `Call` reading an enclosing
  // `Iteration`'s variable — which needs a simultaneous capture-avoiding substitution, which is why
  // it could not be done before Track A.
  //
  // A FALLBACK IS STILL POSSIBLE and the gate names it rather than forbidding the shape: a
  // SELF-RECURSIVE call cannot be inlined, and `Fold`/`Range`/grounded have no inlining at all.  If
  // one of those appears under a binder the assertion fires with the node and the reason, which is
  // the actionable form — the alternative (`assert(binderFallback.size <= 2)`) is the allow-list
  // architecture the review rejected.
  test("1D.4. every cornerstone reaches the renderers with its BINDERS INTACT") {
    assertEquals(binderFallback.toVector.sorted, Vector.empty[String],
      s"${binderFallback.size} cornerstone(s) fell back to the EXECUTED form: " +
      s"${binderFallback.toVector.sorted.mkString(", ")}.  Their stage-1 artifacts then describe a " +
      "ground computation rather than the binder structure, so they certify the executor and not " +
      "the optimiser.  The `[pipeline] … binder-preserving sides UNAVAILABLE` line above names the " +
      "node that forced each one; `expandKeepBinders` inlines an acyclic Call, so what reaches that " +
      "refusal is a self-recursive call (residualise it, or lower it to a `Space.Fixpoint`) or a " +
      "Fold/Range/grounded node under a binder (no renderer models one).")
    assert(binderKept.size >= 7,
      s"only ${binderKept.size} stones kept their binders; the pipeline declares seven cornerstones " +
      "(CornerstoneTypes.scala), so a smaller number means a stone stopped being run at all — which " +
      "would make the assertion above pass for the wrong reason.")
    println(s"[pipeline] BINDER CENSUS: ${binderKept.size} of ${binderKept.size + binderFallback.size} " +
            s"stones keep their binders — ${binderKept.toVector.sorted.mkString(", ")}")
  }

  // 0.3 — THE GOLDEN-FILE GATE, declared last so every cornerstone above has emitted.  This suite is
  // the largest artifact producer in the tree (55 `.egg` under zipper-egg-tests/pipeline, 42 `.smt2`
  // plus a STATUS.tsv under proofs/pipeline), and until now every one of them was OVERWRITTEN by the
  // run that should have checked it: `sbt test` dirtied a hundred tracked files and a drifted emitter
  // could never fail.  A VERIFY run now compares each produced artifact against the committed one and
  // fails here on any difference; `ZIPPY_REGENERATE=1 sbt --server 'testOnly morkl.EquivPipelineTest'` is the
  // only thing that rewrites them.
  test("every committed pipeline artifact matches what this suite produces") {
    ArtifactSink.assertClean("morkl.EquivPipelineTest")
  }
end EquivPipelineTest
