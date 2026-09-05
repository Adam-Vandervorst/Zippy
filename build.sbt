ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.8.1"
// https://github.com/scala/scala3/issues/20266
ThisBuild / scalacOptions += "-source:3.3"
ThisBuild / scalacOptions += "-feature"
ThisBuild / scalacOptions += "-explain"

// -------------------------------------------------------------------------------------------------
// Keys declared at the top level, assigned inside `root`'s settings below: a bare `key := ...` in
// build.sbt is NOT injected into an explicitly-declared `project in file(".")`, so an assignment
// left out here compiles and then reports `Not a valid key`.
// -------------------------------------------------------------------------------------------------
lazy val testRuntimeDir = settingKey[File]("where exportTestRuntime writes the runner")
// Returns Unit, not the runner's `File`: sbt 2 refuses to cache a task whose output type is
// `File`/`Path`, and the runner's location is a SETTING (`testRuntimeDir`) that every consumer
// can read without running the task.
lazy val exportTestRuntime = taskKey[Unit]("write the test classpath + a one-suite runner for scripts/gates.py")
lazy val check = taskKey[Unit]("run every acceptance gate (scripts/gates.py holds the list)")

lazy val root = (project in file("."))
  .settings(
    name := "Zippy",
    libraryDependencies += "org.scalameta" %% "munit" % "1.2.1" % Test,
    libraryDependencies += "org.scala-lang.modules" %% "scala-collection-contrib" % "0.3.0",

    // FORK THE TEST JVM.  Two reasons, both measured:
    //
    // 1. JAVA DESERIALIZATION OF THE CORPUS.  Run in-process, sbt's LAYERED test classloader makes
    //    `java.io.ObjectInputStream.latestUserDefinedLoader` resolve `scala.collection.generic.
    //    DefaultSerializationProxy` in a different layer from `morkl.SpaceValue`, so the proxy's
    //    `readResolve` never runs and every read of `corpus_1000.ser` dies with
    //    "cannot assign instance of DefaultSerializationProxy to field morkl.SpaceValue.paths".
    //    That killed SEVENTEEN corpus-wide soundness gates at once — every "sound on the corpus"
    //    claim in the suite was silently not running.  The same file reads without complaint from a
    //    plain JVM on sbt's own `Test/fullClasspath`, which is what identifies the classloader as
    //    the cause; `Corpus.load` (src/test/scala/Corpus.scala) additionally falls back to the text
    //    corpus so the gate survives a future serialization change.
    // 2. HEAP AND STACK.  The suite needs both (the 9!/2 = 181 440-state puzzle enumeration, the
    //    n=12 n-queens search and the 3000-program corpus sweeps OOM at sbt's 1 GB default), and a
    //    forked JVM is the only place a test-specific `-Xmx` is honoured.  `.jvmopts` sizes the sbt
    //    JVM itself, which still has to compile this tree.
    Test / fork := true,
    // THE ARTIFACT-SINK SWITCH REACHES THE FORKED JVM.  `ArtifactSink` reads `$ZIPPY_REGENERATE` (and
    // `$ZIPPY_ARTIFACT_SCRATCH`) from its own process environment; a forked test JVM does not see the
    // variables the `sbt` invocation was given unless they are passed through here.  Measured
    // (2026-09-04): `ZIPPY_REGENERATE=1 sbt 'testOnly morkl.EquivPipelineTest'` ran 21 minutes in
    // VERIFY mode and then reported 98 stale artifacts.
    Test / envVars ++= Seq("ZIPPY_REGENERATE", "ZIPPY_ARTIFACT_SCRATCH", "ZIPPY_TOOLS", "Z3", "VAMPIRE", "EGGLOG", "LAKE")
      .flatMap(k => sys.env.get(k).map(k -> _)).toMap,
    Test / javaOptions ++= Seq("-Xmx24G", "-Xss16M", "-Dfile.encoding=UTF-8"),

    // ==================================================================================================
    // 0.2 — ONE FORKED JVM PER SUITE.
    //
    // `Test / fork := true` forks ONE JVM for the WHOLE suite set, so every measuring suite ran inside a
    // process whose global state had already been shaped by however many suites happened to precede it
    // alphabetically.  Two globals are process-wide and append-only by design — `Interner` (PathItem <->
    // Int, IntTrie.scala) and `HeadAtoms` (Set[PathItem] <-> Int, SpatialShape.scala) — and a third,
    // `EffortSink.armed`, is a process-wide flag.  The consequence was MEASURED and recorded in
    // build.log: `sbt test` and `testOnly morkl.SpatialScaleCheck` disagreed on a counted column, so the
    // same tree reported a product requirement as PASSING in one invocation and FAILING-AND-UNDIAGNOSED
    // in the other.  A number that depends on which other tests ran is not a measurement, and the
    // numbers this repository publishes are read off exactly those columns.
    //
    // So each test CLASS gets its own subprocess: `testOnly X` is then byte-identical to X's slice of
    // `sbt test` by construction, and the counted columns stop depending on suite order.  Groups run
    // sequentially (sbt's default, `testForkedParallel` left off) because several of these suites also
    // take WALL-CLOCK measurements against budgets — build.log's round-7 footnote is a 5088 ms vs
    // 2622.9 ms latency reading on one cornerstone, the entire difference being 50 other suites sharing
    // the JVM.  Sequential single-suite JVMs fix that reading too, and `-Xmx24G` is only ever committed
    // by one process at a time.
    //
    // THE COST IS REAL AND IT IS THE RIGHT TRADE: one JVM start per test CLASS.  MEASURED:
    // `print Test/testGrouping` reports 94 groups over the 95 test classes in the 66 files of
    // `src/test/scala`, i.e. one each.  The
    // alternative on offer was a "deterministic pre-intern of the ladder's alphabet", which pins one
    // symptom in one suite and leaves every other counted column order-dependent.
    //
    // `Def.uncached` because sbt 2 wants a `JsonFormat[Seq[Tests.Group]]` to cache the setting's value
    // and `Tests.Group` has none; the grouping is derived from `definedTests` on every run anyway, so
    // there is nothing to cache.
    Test / testGrouping := Def.uncached {
      val opts = (Test / forkOptions).value
      (Test / definedTests).value.map { t =>
        Tests.Group(name = t.name, tests = Seq(t), runPolicy = Tests.SubProcess(opts))
      }
    },

    // ==================================================================================================
    // 0.4 — THE IN-TREE RUNNER.
    //
    // `scripts/publish_benchmarks.py` needed `--runner` or `$ZIPPY_RUNNER` — "a command that runs one
    // JUnit suite" — supplied from outside the tree.  That is an environment variable standing between
    // the repository and its own acceptance gates: a reader who checks out this commit cannot run them,
    // and two runs can disagree because they were handed different runners.
    //
    // `exportTestRuntime` writes the test classpath and the fork options that `Test / fork` uses, plus an
    // executable `run-suite.sh` that runs ONE suite in ONE plain forked JVM with exactly those options —
    // the same JVM OPTIONS and CLASSPATH a `testGrouping` group gets, so a gate run and a `sbt test`
    // slice measure in the same process shape.  `scripts/gates.py` finds it at a fixed path, so
    // `sbt check` and `publish_benchmarks.py` need no environment at all.
    //
    // THE HARNESS IS NOT IDENTICAL, AND THE DIFFERENCE IS REAL: sbt drives munit through
    // test-interface, this drives it through `JUnitCore`, and `JUnitCore.main` calls `System.exit` on
    // the result.  MEASURED: an `override def afterAll()` prints under `sbt test` and is DROPPED
    // here, because `MUnitRunner` drives `runAfterAll` through a `Future` that the exit does not
    // wait for.  `CalibrationProbe` hangs its EXIT probe off a JVM shutdown hook for exactly that
    // reason — anything that must appear in BOTH harnesses has to be attached to the JVM rather
    // than to the test lifecycle.
    //
    // munit suites are JUnit-4 runnable (`munit.Suite` carries `@RunWith`, and `junit-interface` puts
    // junit 4.13.2 on the test classpath), so `org.junit.runner.JUnitCore` is the launcher and its exit
    // status is the gate's verdict.
    testRuntimeDir := (ThisBuild / baseDirectory).value / "target" / "test-runtime",

    // `Def.uncached` for the same reason as `testGrouping`: this task's inputs include a
    // `ForkOptions` and an `Attributed[HashedVirtualFileRef]` classpath, neither of which sbt 2
    // can hash for its cache — and there is nothing to cache anyway, since the point of the task
    // is to write the CURRENT classpath to disk.
    exportTestRuntime := Def.uncached {
      val dir = testRuntimeDir.value
      IO.createDirectory(dir)
      // sbt 2 hands out `HashedVirtualFileRef`s, not `File`s, so the classpath is materialised
      // through the build's own `fileConverter` rather than by assuming an on-disk shape.
      val conv = fileConverter.value
      val cp = (Test / fullClasspath).value
        .map(a => conv.toPath(a.data).toAbsolutePath.toString)
        .mkString(java.io.File.pathSeparator)
      val opts = (Test / javaOptions).value
      val home = (Test / forkOptions).value.javaHome
        .map(_.getAbsolutePath).getOrElse(System.getProperty("java.home"))
      val javaBin = home + "/bin/java"
      IO.write(dir / "classpath.txt", cp + "\n")
      IO.write(dir / "javaOptions.txt", opts.mkString("\n") + "\n")
      IO.write(dir / "java.txt", javaBin + "\n")
      val sh = dir / "run-suite.sh"
      // The runner is GENERATED rather than committed, because the classpath it needs is a build
      // output.  It reads the three files beside it, so re-exporting after a dependency change is
      // enough and there is no second copy of the classpath to go stale.
      IO.write(sh,
        s"""#!/bin/sh
           |# GENERATED by `sbt exportTestRuntime` — do not edit; re-run the task instead.
           |# Runs ONE munit suite in ONE plain forked JVM, with the same options `Test / fork` uses.
           |d=$$(dirname "$$0")
           |exec "$$(cat "$$d/java.txt")" $$(cat "$$d/javaOptions.txt" | tr '\\n' ' ') \\
           |  -cp "$$(cat "$$d/classpath.txt")" org.junit.runner.JUnitCore "$$@"
           |""".stripMargin)
      sh.setExecutable(true)
      streams.value.log.info(s"test runtime exported to $dir (runner: ${sh.getAbsolutePath})")
    },

    // ==================================================================================================
    // 0.4 — ONE GATE LIST, ONE ENTRY POINT.
    //
    // `sbt check` is the acceptance-gate command.  It does NOT hold a gate list: `scripts/gates.py` does,
    // and `publish_benchmarks.py` imports the same module, so a gate cannot be in one and missing from
    // the other.  (It was: an earlier revision of the publisher listed only the four Scala suites, so
    // item 7's and item 8's declared gates were never run by the thing that gates publication.)
    check := Def.uncached {
      exportTestRuntime.value
      val runner = testRuntimeDir.value / "run-suite.sh"
      val log = streams.value.log
      val root = (ThisBuild / baseDirectory).value
      val rc = scala.sys.process.Process(
        Seq("python3", "scripts/gates.py", "--run", "--runner", runner.getAbsolutePath), root).!
      if (rc != 0) sys.error(s"acceptance gates FAILED (scripts/gates.py exited $rc)")
      log.info("all acceptance gates green")
    },
  )
