package morkl

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}

@main def resultSpaceSizeRandomAudit(
  count: Int = 1000,
  seed: Long = 20260708L,
  maxDepth: Int = 5,
  maxResult: Int = 400,
  output: String = "/tmp/result-space-size-random-audit.md"
): Unit =
  val records = SpaceFuzzerCorpus.generate(count, seed, maxDepth, maxResult)
  ResultSpaceSizeAudit.reset(
    s"Result-space size audit: $count random programs (seed=$seed, depth=$maxDepth, result≤$maxResult)"
  )
  val pc = PathContextMap(Map.empty)
  val rc = PartialFunction.empty[RoutinePtr, Routine]
  records.foreach { record =>
    val example = record.example
    val sc = SpaceContextMap(Map(SpaceFuzzer.argM -> example.arg))
    ResultSpaceSizeAudit.observeExplicit(example.program, example.result)(using pc, sc, rc)
  }
  val report = ResultSpaceSizeAudit.render
  Files.writeString(Paths.get(output), report, StandardCharsets.UTF_8)
  println(report)
