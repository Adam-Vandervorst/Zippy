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

  // ---------------------------------------------------------------------------------------------
  // THE BUILD, NOT JUST THE RUNTIME.  `jvm` and `scala` said which VM ran and which library was on
  // the classpath; neither said which BUILD produced the classes, and a table cannot be reproduced
  // from a JVM version alone.  All three of these are read from the files that ARE the source of
  // truth, so they cannot drift from what a rebuild would use.
  // ---------------------------------------------------------------------------------------------
  /** the sbt version, from `project/build.properties` — the file that pins it */
  lazy val sbtVersion: String =
    firstLineOf("project/build.properties", "sbt.version=").map(_.stripPrefix("sbt.version=").trim)
      .getOrElse("unknown")

  /** the compiler version and flags, from `build.sbt` — likewise the pinning file.  The flags matter:
   *  `-source:3.3` changes what the compiler accepts and therefore what was compiled. */
  lazy val scalacConfig: String =
    val lines = linesOf("build.sbt")
    val ver = lines.collectFirst { case l if l.contains("scalaVersion") && l.contains(":=") =>
      l.split(":=").last.trim.stripPrefix("\"").stripSuffix("\"") }.getOrElse("unknown")
    val flags = lines.filter(l => l.contains("scalacOptions") && l.contains("+="))
      .map(_.split("\\+=").last.trim.stripPrefix("\"").stripSuffix("\""))
    s"scalac $ver" + (if flags.isEmpty then "" else s" ${flags.mkString(" ")}")

  /** the external tools, resolved and version-probed — relevant to every table whose numbers came
   *  from a prover or the e-graph engine, and unrecoverable after the fact. */
  lazy val externalTools: String =
    Tools.all.map { tl =>
      tl.path match
        case None => s"${tl.name}=ABSENT"
        case Some(bin) =>
          val v =
            try
              val pb = new ProcessBuilder(bin, tl.versionFlag).redirectErrorStream(true)
              val pr = pb.start()
              val out = new String(pr.getInputStream.readAllBytes()).linesIterator.take(1).mkString.trim
              pr.waitFor()
              out.replaceAll("[|;]", " ").trim
            catch case _: Throwable => "?"
          s"${tl.name}=${if v.isEmpty then "?" else v}"
    }.mkString("  ")

  /** how many tracked paths differ from HEAD — `0` is a clean tree.  Reported as a NUMBER rather
   *  than folded into the commit string, because "how dirty" is what a reader needs to judge
   *  whether `<sha>-dirty` can be reconstructed at all. */
  lazy val dirtyFileCount: Int =
    gitLines("status", "--porcelain").map(_.count(_.trim.nonEmpty)).getOrElse(-1)

  def sourceClean: Boolean = dirtyFileCount == 0

  /** ARTIFACT GENERATION CAN BE GATED ON A CLEAN TREE.  With `$ZIPPY_REQUIRE_CLEAN` set, a generated
   *  table refuses to be written from a dirty working tree — because `<sha>-dirty` does not identify
   *  the code that produced the numbers, so such a table cannot be reproduced from any commit and
   *  cannot establish what the tree does.  Unset (the default) a dirty run is allowed and SAYS SO in
   *  its own header, which is what a local experiment wants; the release regeneration sets it. */
  def requireCleanIfAsked(what: String): Unit =
    if sys.env.get("ZIPPY_REQUIRE_CLEAN").exists(v => v != "0" && v.nonEmpty) && !sourceClean then
      throw new IllegalStateException(
        s"$what: refusing to generate from a DIRTY working tree ($dirtyFileCount modified path(s)). " +
        s"`$gitCommit` does not identify the code that produced the numbers. Commit the code first, " +
        s"then regenerate — or unset ZIPPY_REQUIRE_CLEAN for a local run whose header will say `dirty`.")

  private def linesOf(rel: String): List[String] =
    try scala.io.Source.fromFile(new java.io.File(repoRoot, rel)).getLines().toList
    catch case _: Throwable => Nil
  private def firstLineOf(rel: String, key: String): Option[String] =
    linesOf(rel).find(_.trim.startsWith(key)).map(_.trim)
  private def gitLines(args: String*): Option[List[String]] =
    try
      val pb = new ProcessBuilder(("git" +: args)*).directory(repoRoot).redirectErrorStream(true)
      val pr = pb.start()
      val out = new String(pr.getInputStream.readAllBytes())
      if pr.waitFor() == 0 then Some(out.linesIterator.toList) else None
    catch case _: Throwable => None

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
      "scala (runtime library)" -> scalaVersion,
      "build" -> s"sbt $sbtVersion; $scalacConfig",
      "external tools" -> externalTools,
      "source tree" -> (if sourceClean then "CLEAN (the commit above identifies it)"
                        else s"DIRTY — $dirtyFileCount modified path(s); `$gitCommit` does NOT " +
                             "identify the code that produced these numbers"),
      "tuning" -> tuning,
    ) ++ extra
    val sb = new StringBuilder
    sb.append("| environment | value |\n|---|---|\n")
    for (k, v) <- rows do sb.append(s"| $k | ${v.replace("|", "\\|")} |\n")
    sb.toString

  /** the same facts on one line, for a CSV/TSV header comment or a console banner */
  def oneLine(extra: Seq[(String, String)] = Nil): String =
    (Seq(s"ts=${timestamp()}", s"git=$gitCommit",
         s"clean=${if sourceClean then "yes" else s"no($dirtyFileCount)"}",
         s"cpu=${cpu.replace(',', ' ')}", s"cores=$cores",
         s"mem=${memGiB}GiB", s"os=$os", s"jvm=$jvm", s"heap=${heapMaxGiB}GiB",
         s"scala=$scalaVersion", s"sbt=$sbtVersion", s"build=${scalacConfig.replace(';', ' ')}",
         s"tools=${externalTools.replace(';', ' ')}", tuning) ++ extra.map((k, v) => s"$k=$v")).mkString("; ")
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
    // A GENERATED ARTIFACT MUST NAME THE CODE THAT PRODUCED IT.  `<sha>-dirty` does not: the tree it
    // describes never existed as a commit, so the numbers cannot be reproduced from anything and
    // cannot establish what the tree does.  With `$ZIPPY_REQUIRE_CLEAN` set this refuses; unset, a
    // dirty run is allowed and the metadata block above the section says `DIRTY` with the modified
    // path count, so the weaker attribution is stated rather than implied by a suffix.
    RunEnvironment.requireCleanIfAsked(s"BenchmarkReport.write($slug)")
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
