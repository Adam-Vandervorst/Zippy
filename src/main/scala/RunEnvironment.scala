package morkl

/** ==============================================================================================
 *  PROVENANCE FOR EVERY GENERATED NUMBER.
 *
 *  A timing table without the machine, the toolchain and the configuration it was produced on is
 *  not a measurement — it cannot be reproduced, compared against a later run, or even read
 *  ("is 43.6 ms fast?" has no answer without the CPU).  `docs/design_plan.md` §7.4 already requires
 *  "committed numbers, seeds, generator versions; explicit cold/warm interner policy"; this object
 *  is the one implementation of that requirement, and [[BenchmarkReport]] is the one writer that
 *  stamps it onto an artifact.
 *
 *  Everything here is read from the JVM and the OS at call time — no configuration, no external
 *  process except `git rev-parse`, and every field degrades to `"unknown"` rather than throwing, so
 *  a benchmark can never fail because provenance was unavailable.
 *  ============================================================================================== */
object RunEnvironment:
  import scala.util.Try

  private def firstLine(f: String, key: String): Option[String] =
    Try(scala.io.Source.fromFile(f)).toOption.flatMap { s =>
      try s.getLines().find(_.startsWith(key)).map(_.split(":", 2).last.trim) finally s.close()
    }

  /** e.g. "AMD EPYC 7R13 48-Core Processor" — `/proc/cpuinfo` on Linux, the JVM's arch elsewhere. */
  lazy val cpu: String =
    firstLine("/proc/cpuinfo", "model name")
      .orElse(firstLine("/proc/cpuinfo", "Model"))
      .getOrElse(sys.props.getOrElse("os.arch", "unknown"))

  lazy val cores: Int = Runtime.getRuntime.availableProcessors

  /** total physical RAM in GiB, or -1 */
  lazy val memGiB: Long =
    firstLine("/proc/meminfo", "MemTotal")
      .flatMap(v => v.split("\\s+").headOption).flatMap(_.toLongOption)
      .map(_ / 1024 / 1024).getOrElse(-1L)

  lazy val os: String = s"${sys.props.getOrElse("os.name", "?")} ${sys.props.getOrElse("os.version", "?")}"

  lazy val jvm: String =
    s"${sys.props.getOrElse("java.vm.name", "?")} ${sys.props.getOrElse("java.version", "?")}" +
    s" (${sys.props.getOrElse("java.vendor", "?")})"

  /** the JIT-relevant flags actually in effect, not the ones someone meant to pass */
  lazy val jvmArgs: String =
    Try(java.lang.management.ManagementFactory.getRuntimeMXBean.getInputArguments)
      .map { as => val l = as.toArray.map(_.toString).toList; if l.isEmpty then "(none)" else l.mkString(" ") }
      .getOrElse("unknown")

  lazy val heapMaxGiB: String =
    f"${Runtime.getRuntime.maxMemory.toDouble / (1L << 30)}%.1f"

  lazy val scalaVersion: String =
    Try(scala.util.Properties.versionNumberString).getOrElse("unknown")

  /** git HEAD plus a dirty marker, so a table can never be attributed to a tree that never existed */
  lazy val gitCommit: String =
    def run(args: String*): Option[String] =
      Try {
        val pb = new ProcessBuilder(args*)
        pb.directory(repoRoot); pb.redirectErrorStream(true)
        val p = pb.start()
        val out = new String(p.getInputStream.readAllBytes()).trim
        if p.waitFor() == 0 then Some(out) else None
      }.toOption.flatten
    val sha = run("git", "rev-parse", "--short", "HEAD").getOrElse("unknown")
    val dirty = run("git", "status", "--porcelain").exists(_.nonEmpty)
    if dirty then s"$sha-dirty" else sha

  /** nearest ancestor of the working directory containing build.sbt */
  lazy val repoRoot: java.io.File =
    var d = new java.io.File(".").getCanonicalFile
    while d != null && !new java.io.File(d, "build.sbt").exists do d = d.getParentFile
    if d != null then d else new java.io.File(".").getCanonicalFile

  /** UTC, second resolution — the same string sorts and parses */
  def timestamp(): String =
    java.time.ZonedDateTime.now(java.time.ZoneOffset.UTC)
      .format(java.time.format.DateTimeFormatter.ofPattern("uuuu-MM-dd'T'HH:mm:ss'Z'"))

  def date(): String =
    java.time.LocalDate.now(java.time.ZoneOffset.UTC).toString

  /** the ablation toggles that change what is being measured */
  lazy val tuning: String = s"literalByRef=${Tuning.literalByRef} patriciaOps=${Tuning.patriciaOps}"

  /** THE BLOCK.  Markdown, one row per field, emitted directly above every generated table.
   *
   *  `extra` carries the run-shaped configuration the caller owns and this object cannot know:
   *  warmup/repetition counts, the seed, the interner cold/warm policy, the input scales. */
  def markdown(extra: Seq[(String, String)] = Nil): String =
    val rows = Seq(
      "timestamp (UTC)" -> timestamp(),
      "git commit" -> gitCommit,
      "cpu" -> s"$cpu ($cores logical cores)",
      "memory" -> (if memGiB > 0 then s"$memGiB GiB" else "unknown"),
      "os" -> os,
      "jvm" -> jvm,
      "jvm args" -> jvmArgs,
      "max heap" -> s"$heapMaxGiB GiB",
      "scala" -> scalaVersion,
      "tuning" -> tuning,
    ) ++ extra
    val sb = new StringBuilder
    sb.append("| environment | value |\n|---|---|\n")
    for (k, v) <- rows do sb.append(s"| $k | ${v.replace("|", "\\|")} |\n")
    sb.toString

  /** the same facts on one line, for a CSV/TSV header comment or a console banner */
  def oneLine(extra: Seq[(String, String)] = Nil): String =
    (Seq(s"ts=${timestamp()}", s"git=$gitCommit", s"cpu=${cpu.replace(',', ' ')}", s"cores=$cores",
         s"mem=${memGiB}GiB", s"os=$os", s"jvm=$jvm", s"heap=${heapMaxGiB}GiB",
         s"scala=$scalaVersion", tuning) ++ extra.map((k, v) => s"$k=$v")).mkString("; ")
end RunEnvironment


/** ==============================================================================================
 *  THE ONE WRITER for a generated results section.
 *
 *  ==WHY THIS EXISTS==
 *  Every benchmark used to do `new FileWriter(docs/BENCHMARKS.md, append = true)`.  Five appenders x
 *  every run left the file a 3,700-line tape of ~28 near-identical replays of the same five
 *  sections, in which the CURRENT numbers were indistinguishable from numbers produced months
 *  earlier by different code on a different machine — and none of them said which machine.
 *
 *  ==WHAT IT DOES==
 *  A section is addressed by a stable SLUG and delimited by HTML comment markers.  Writing a
 *  section REPLACES the text between its markers (or appends the section when the slug is new), and
 *  always stamps [[RunEnvironment.markdown]] directly under the heading.  So the document has one
 *  copy of each result, always current, always attributed; history lives in git, which is what git
 *  is for.
 *  ============================================================================================== */
object BenchmarkReport:
  import java.io.File

  def beginMarker(slug: String): String = s"<!-- BEGIN benchmark:$slug -->"
  def endMarker(slug: String): String = s"<!-- END benchmark:$slug -->"

  /** Replace (or append) the `slug` section of `file` with `heading` + provenance + `body`. */
  def write(file: File, slug: String, heading: String, body: String,
            extra: Seq[(String, String)] = Nil): Unit =
    val section =
      s"""${beginMarker(slug)}
## $heading

${RunEnvironment.markdown(extra)}
$body
${endMarker(slug)}"""
    val old = if file.exists then readAll(file) else ""
    val (b, e) = (beginMarker(slug), endMarker(slug))
    val next =
      val i = old.indexOf(b)
      val j = old.indexOf(e)
      if i >= 0 && j > i then old.substring(0, i) + section + old.substring(j + e.length)
      else (if old.isEmpty || old.endsWith("\n\n") then old
            else if old.endsWith("\n") then old + "\n"
            else old + "\n\n") + section + "\n"
    val w = new java.io.FileWriter(file)
    try w.write(next) finally w.close()

  private def readAll(f: File): String =
    val s = scala.io.Source.fromFile(f); try s.mkString finally s.close()
end BenchmarkReport
