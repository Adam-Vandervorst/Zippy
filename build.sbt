ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.8.1"
// https://github.com/scala/scala3/issues/20266
ThisBuild / scalacOptions += "-source:3.3"
ThisBuild / scalacOptions += "-feature"
ThisBuild / scalacOptions += "-explain"

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
    Test / javaOptions ++= Seq("-Xmx24G", "-Xss16M", "-Dfile.encoding=UTF-8"),
  )
