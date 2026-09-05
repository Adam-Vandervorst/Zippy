package morkl

/** ==============================================================================================
 *  THE ONE CORPUS LOADER.
 *
 *  Twenty test files used to open `corpus_1000.ser` themselves, each with its own copy of the
 *  four-line read and its own (or no) staleness guard.  That is how the corpus gate died silently:
 *  when the read started failing, every one of those files reported a `ClassCastException` from a
 *  different line and nothing said "the corpus is not being checked".
 *
 *  ==WHAT KILLED IT, AND WHY IT IS NOT AN ARTIFACT PROBLEM==
 *  Run IN-PROCESS, sbt's layered test classloader makes `ObjectInputStream.latestUserDefinedLoader`
 *  resolve `scala.collection.generic.DefaultSerializationProxy` in a different layer from
 *  `morkl.SpaceValue`, so the proxy's `readResolve` never runs and the read dies with
 *
 *      cannot assign instance of scala.collection.generic.DefaultSerializationProxy
 *      to field morkl.SpaceValue.paths of type scala.collection.immutable.Set
 *
 *  The very same file reads cleanly from a plain JVM started on sbt's own `Test/fullClasspath`,
 *  which is what identifies the classloader rather than the artifact as the cause.  `Test / fork`
 *  in build.sbt is the fix; this loader is the guard that makes a regression visible as ONE
 *  actionable message instead of twenty stack traces.
 *
 *  ==THE THREE FAILURE MODES, EACH WITH ITS OWN MESSAGE==
 *  ABSENT   — the generator has never been run in this checkout.
 *  STALE    — the serialized classes changed under the file (`InvalidClassException`).
 *  UNREADABLE — anything else, including the classloader failure above.
 *  All three name the exact command that fixes them (`docs/traps.md` §3: a loader must give an
 *  actionable error, never a bare exception).
 *  ============================================================================================== */
object Corpus:
  val Regenerate = "sbt 'testOnly morkl.ProgramExpressivity -- --tests=.*corpus.*'"

  def file: java.io.File = new java.io.File(Loaders.repoRoot, "corpus_1000.ser")

  /** the 1000-program fuzzed corpus, or a diagnostic that says which of the three things went wrong */
  def load(): Vector[FuzzRec] =
    val f = file
    if !f.exists then
      throw new AssertionError(
        s"corpus ABSENT: ${f.getPath} has never been generated in this checkout.  Run:\n  $Regenerate")
    try
      val ois = new java.io.ObjectInputStream(new java.io.FileInputStream(f))
      try ois.readObject().asInstanceOf[Vector[FuzzRec]] finally ois.close()
    catch
      case e: java.io.InvalidClassException =>
        throw new AssertionError(
          s"corpus STALE: the serialized classes changed under ${f.getName} (${e.getMessage}).  Run:\n  $Regenerate", e)
      case e: ClassCastException =>
        throw new AssertionError(
          s"corpus UNREADABLE: ${e.getMessage}\n" +
          "  This is the sbt in-process-classloader failure `Test / fork := true` exists to prevent " +
          "(see build.sbt and the header of this file).  Check that the fork setting is still in " +
          s"effect; if the artifact really is bad, regenerate it:\n  $Regenerate", e)
      case e: Throwable =>
        throw new AssertionError(s"corpus UNREADABLE (${e.getClass.getSimpleName}: ${e.getMessage}).  Run:\n  $Regenerate", e)

  /** the corpus, capped — the sweeps that only need a sample say how big a sample they need */
  def load(limit: Int): Vector[FuzzRec] = load().take(limit)
end Corpus
