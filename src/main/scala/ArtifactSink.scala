package morkl

/** ==================================================================================================
 *  THE ONE WRITER FOR EVERY COMMITTED **PROOF** ARTIFACT, AND ITS GOLDEN-FILE GATE.
 *
 *  ==WHAT WAS WRONG==
 *  Five suites wrote committed files with a bare `java.io.FileWriter` as a SIDE EFFECT of running:
 *  `EquivPipelineTest` (55 egg programs under `zipper-egg-tests/pipeline`, 42 SMT goals plus a
 *  `STATUS.tsv` under `proofs/pipeline`), `ZipperEggTest` (the egg programs directly under
 *  `zipper-egg-tests`), `FixpointSemantics` (`proofs/pipeline/fixpoint-gate`),
 *  `TierThreeConformance` (`proofs/unbounded/COUNTERMODELS.tsv`) and `DatalogShowTest`
 *  (`datalog-morkl.txt`).  (Scala nests block comments, so a glob cannot be written here.)  Three
 *  consequences, all of them observed:
 *
 *   1. `sbt test` DIRTIED THE TREE.  Every run rewrote a hundred tracked files, so `git status` after
 *      a test run said nothing about whether the code had changed the artifacts, and a publication
 *      preflight ("the tree must be clean") could not distinguish a real edit from the last test run.
 *   2. A STALE ARTIFACT COULD NOT FAIL.  Because the artifact was OVERWRITTEN by the run that would
 *      have checked it, the committed content was never compared against anything.  A generator
 *      whose output drifted simply committed its drift on the next `git add`.
 *   3. IT WAS NOT DISTINGUISHABLE FROM PUBLICATION.  `BenchmarkArtifact` / `PublishManifest`
 *      (RunEnvironment.scala) already gate the four BENCHMARK outputs behind a publication
 *      transaction; the proof artifacts had no gate at all, and the two kinds were being confused in
 *      discussion because one of them had no name.
 *
 *  ==WHAT THIS IS==
 *  A sink with two modes, chosen by `$ZIPPY_REGENERATE`:
 *
 *   VERIFY (the default, and what `sbt test` does).  Each write goes to a scratch twin under
 *      `target/artifact-scratch/<repo-relative path>` — the real bytes, at a real path, so an
 *      external tool can still consume it — and its content is COMPARED against the committed file.
 *      A difference, a missing committed file, or a delete the run wanted to perform is recorded as a
 *      finding.  The tree is not touched at all.
 *   REGENERATE (`ZIPPY_REGENERATE=1`).  Writes land on the committed paths.  This is the ONLY way a
 *      proof artifact changes, and it is a deliberate, separate act from running the tests.
 *
 *  `assertClean` turns the findings into one failure per suite, which is the "a stale artifact fails
 *  a test" half of the gate.
 *
 *  ==WHY IT IS NOT `PublishManifest`==
 *  Deliberately distinct, and the two cover DISJOINT file sets.  `PublishManifest` guards MEASURED
 *  NUMBERS: its whole purpose is that one publication carries one commit identity and one
 *  environment record, so it must refuse outside a transaction.  These artifacts are DERIVED TEXT —
 *  an egglog program, an SMT goal, a status table — reproducible from the tree alone, with no
 *  environment in them.  Regenerating them needs no commit identity and no clean tree; what it needs
 *  is to be a decision rather than an accident.  Confusing the two would either put proof artifacts
 *  behind a preflight they have no reason to pass, or put benchmark numbers behind a plain
 *  environment variable.  [[refuseBenchmarkOutput]] keeps the sets disjoint mechanically.
 *
 *  ==ATOMIC, for 0.1's reason==
 *  Every write is `tmp` + `rename`, so a killed suite cannot leave a truncated artifact where a
 *  complete one was — the same property `proofs/run.sh` and `terminating/run.sh` now have for their
 *  status tables.
 *  ================================================================================================== */
object ArtifactSink:

  /** THE FOUR BENCHMARK OUTPUTS, which belong to `PublishManifest` and must never come through here.
   *  Kept as a literal list rather than read from the publisher: this is an assertion that the two
   *  sets are disjoint, and an assertion that imported the other side's list could not detect an
   *  overlap. */
  private val benchmarkOutputs = Set(
    "corpus_runtimes.csv", "expressivity.csv", "prog_matrix.tsv", "docs/BENCHMARKS.md")

  enum Mode:
    case Verify, Regenerate

  val mode: Mode =
    sys.env.get("ZIPPY_REGENERATE").map(_.trim.toLowerCase) match
      case Some("1") | Some("true") | Some("yes") => Mode.Regenerate
      case _                                      => Mode.Verify

  def regenerating: Boolean = mode == Mode.Regenerate

  /** where a VERIFY run's twins go.  Under `target/`, which is git-ignored, so a verify run cannot
   *  add an untracked file to the tree either. */
  lazy val scratchRoot: java.io.File =
    val d = sys.env.get("ZIPPY_ARTIFACT_SCRATCH").map(new java.io.File(_))
      .getOrElse(new java.io.File(RunEnvironment.repoRoot, "target/artifact-scratch"))
    d.mkdirs(); d

  /** what a verify run found out about one artifact */
  enum Finding:
    /** the run produced different content than the tree holds */
    case Changed(rel: String, committedBytes: Int, producedBytes: Int, firstDiff: String)
    /** the run produced an artifact the tree does not have */
    case Absent(rel: String, producedBytes: Int)
    /** the run wanted to DELETE a committed artifact */
    case WouldDelete(rel: String)

    def rel: String
    def show: String = this match
      case Changed(r, cb, pb, d) => s"CHANGED   $r  (committed $cb B, produced $pb B)  first difference: $d"
      case Absent(r, pb)         => s"ABSENT    $r  (produced $pb B; no committed file)"
      case WouldDelete(r)        => s"DELETE    $r  (the run would have removed this committed file)"

  private val found = scala.collection.mutable.LinkedHashMap.empty[String, Finding]
  private val written = scala.collection.mutable.LinkedHashSet.empty[String]

  /** every finding of this JVM, in first-seen order */
  def findings: Vector[Finding] = synchronized(found.values.toVector)

  /** every artifact this JVM produced, repo-relative */
  def produced: Vector[String] = synchronized(written.toVector)

  // ------------------------------------------------------------------------------------------------
  private def rel(f: java.io.File): String =
    val root = RunEnvironment.repoRoot.getCanonicalFile.toPath
    val p = f.getCanonicalFile.toPath
    if p.startsWith(root) then root.relativize(p).toString.replace('\\', '/') else f.getPath

  private def refuseBenchmarkOutput(r: String): Unit =
    if benchmarkOutputs.contains(r) then
      throw new IllegalStateException(
        s"ArtifactSink: `$r` is a BENCHMARK output and belongs to PublishManifest, not to this sink.  " +
        "The two gates cover disjoint sets on purpose: a measured number carries a commit identity " +
        "and an environment record and must be written inside a publication transaction " +
        "(scripts/publish_benchmarks.py); a derived proof artifact carries neither and is " +
        "regenerated with ZIPPY_REGENERATE=1.  Route this through BenchmarkArtifact.write.")

  /** The directory a writer should use for an artifact whose committed home is `committed`.
   *
   *  In VERIFY mode this is the scratch twin, created on demand.  Callers that hand the path to an
   *  external tool keep working, because the twin is a real directory holding real bytes — note that
   *  `egglog` resolves `(include "…")` against its WORKING DIRECTORY and not against the file's own
   *  directory (measured), so a caller must keep running the tool from the committed directory while
   *  pointing it at the twin's file. */
  def dir(committed: java.io.File): java.io.File =
    val d = mode match
      case Mode.Regenerate => committed
      case Mode.Verify     => new java.io.File(scratchRoot, rel(committed))
    d.mkdirs(); d

  /** The path a writer should write to, for the artifact committed at `committed`. */
  def path(committed: java.io.File): java.io.File =
    refuseBenchmarkOutput(rel(committed))
    new java.io.File(dir(committed.getAbsoluteFile.getParentFile), committed.getName)

  /** Write `content` for the artifact committed at `committed`, and return the file actually written.
   *
   *  In VERIFY mode the committed file is compared against `content` and any difference is recorded.
   *  Repeated writes to the same artifact REPLACE the earlier finding — `EquivPipelineTest`'s egglog
   *  rounds ladder writes one file once per rung, and only the content it settles on is the artifact.
   */
  def write(committed: java.io.File, content: String): java.io.File =
    val r = rel(committed)
    refuseBenchmarkOutput(r)
    val target = path(committed)
    writeAtomically(target, content)
    synchronized {
      written += r
      found -= r
      if mode == Mode.Verify then
        if !committed.isFile then found(r) = Finding.Absent(r, content.length)
        else
          val have = readAll(committed)
          if have != content then found(r) = Finding.Changed(r, have.length, content.length, firstDiff(have, content))
    }
    target

  /** The BINARY twin of [[write]], for an artifact that is not text.
   *
   *  It exists for `corpus_1000.ser` — a Java-serialized program corpus.  Comparing bytes rather
   *  than lines means a difference cannot report a first differing LINE, so the finding carries the
   *  two sizes and says the comparison was byte-level; that is the honest report for a format whose
   *  content is not human-readable anyway. */
  def writeBytes(committed: java.io.File, content: Array[Byte]): java.io.File =
    val r = rel(committed)
    refuseBenchmarkOutput(r)
    val target = path(committed)
    Option(target.getParentFile).foreach(_.mkdirs())
    val tmp = new java.io.File(target.getParentFile, target.getName + ".tmp")
    java.nio.file.Files.write(tmp.toPath, content)
    java.nio.file.Files.move(tmp.toPath, target.toPath,
      java.nio.file.StandardCopyOption.REPLACE_EXISTING)
    synchronized {
      written += r
      found -= r
      if mode == Mode.Verify then
        if !committed.isFile then found(r) = Finding.Absent(r, content.length)
        else
          val have = java.nio.file.Files.readAllBytes(committed.toPath)
          if !java.util.Arrays.equals(have, content) then
            found(r) = Finding.Changed(r, have.length, content.length,
              "byte-level comparison (binary artifact); no line to report")
    }
    target

  /** A delete a writer wants to perform (`EquivPipelineTest.dropFallback`).  In VERIFY mode nothing
   *  is removed from the tree and the intent is recorded, because "this committed file should not
   *  exist" is exactly as much of an artifact change as a content edit. */
  def delete(committed: java.io.File): Boolean =
    val r = rel(committed)
    mode match
      case Mode.Regenerate => committed.exists() && committed.delete()
      case Mode.Verify =>
        if committed.exists() then { synchronized { found(r) = Finding.WouldDelete(r) }; false } else false

  private def readAll(f: java.io.File): String =
    new String(java.nio.file.Files.readAllBytes(f.toPath), java.nio.charset.StandardCharsets.UTF_8)

  /** ATOMIC: write beside the target and rename.  See proofs/run.sh's header for the measured reason. */
  private def writeAtomically(target: java.io.File, content: String): Unit =
    Option(target.getParentFile).foreach(_.mkdirs())
    val tmp = new java.io.File(target.getParentFile, target.getName + ".tmp")
    java.nio.file.Files.write(tmp.toPath, content.getBytes(java.nio.charset.StandardCharsets.UTF_8))
    java.nio.file.Files.move(tmp.toPath, target.toPath,
      java.nio.file.StandardCopyOption.REPLACE_EXISTING)

  /** the first differing line, as `line N: <committed> | <produced>`, truncated */
  private def firstDiff(a: String, b: String): String =
    val la = a.linesIterator.toVector
    val lb = b.linesIterator.toVector
    val i = (0 until math.max(la.length, lb.length)).find(i => la.lift(i) != lb.lift(i))
    i match
      case None => s"same lines, ${a.length} vs ${b.length} bytes (trailing newline?)"
      case Some(n) =>
        def t(s: Option[String]) = s.map(x => if x.length > 70 then x.take(67) + "..." else x).getOrElse("<eof>")
        s"line ${n + 1}: committed `${t(la.lift(n))}` | produced `${t(lb.lift(n))}`"

  /** The report a suite prints, whatever the outcome — a verify run that produced nothing is itself
   *  worth seeing, because it means the writers were skipped. */
  def report(suite: String): String =
    val fs = findings
    val head = mode match
      case Mode.Regenerate =>
        s"ARTIFACTS [$suite]: REGENERATE — ${produced.length} committed artifact(s) rewritten " +
        "(ZIPPY_REGENERATE is set; review `git diff` before committing)"
      case Mode.Verify =>
        s"ARTIFACTS [$suite]: VERIFY — ${produced.length} artifact(s) produced into " +
        s"${rel(scratchRoot)}, ${fs.length} differing from the tree"
    (head +: fs.map("  " + _.show)).mkString("\n")

  /** THE GATE.  Throws with the whole finding list when a verify run disagrees with the tree.
   *
   *  Regenerate mode never fails here: it has just made the tree agree by construction, and a check
   *  in that mode could only ever compare a file against itself. */
  def assertClean(suite: String): Unit =
    println(report(suite))
    val fs = findings
    if mode == Mode.Verify && fs.nonEmpty then
      throw new AssertionError(
        s"$suite: ${fs.length} committed proof artifact(s) are STALE — this run produced different " +
        s"content than the tree holds:\n" + fs.map("  " + _.show).mkString("\n") +
        "\n\nThe produced files are under " + rel(scratchRoot) + " for inspection.  If the new " +
        "content is correct, regenerate the committed artifacts deliberately:\n" +
        "    ZIPPY_REGENERATE=1 sbt 'testOnly " + suite + "'\n" +
        "and commit the diff.  A test run must never rewrite them as a side effect: that is how a " +
        "drifting generator used to commit its own drift.")
end ArtifactSink
