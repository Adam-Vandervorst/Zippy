package morkl

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}

@main def resultPathLengthRandomAudit(
  count: Int = 1000,
  seed: Long = 20260708L,
  maxDepth: Int = 5,
  maxResult: Int = 400,
  output: String = "/tmp/result-path-length-random-audit.md"
): Unit =
  val records = SpaceFuzzerCorpus.generate(count, seed, maxDepth, maxResult)
  val gapBuckets = Vector(0, 1, 2, 4, 8, 16, 32)
  val lowerGaps = Array.fill(gapBuckets.size + 1)(0)
  val upperGaps = Array.fill(gapBuckets.size + 1)(0)
  var exactLower = 0
  var exactUpper = 0
  var finiteUpper = 0
  var improvedLower = 0
  var improvedUpper = 0
  var totalLowerGap = BigInt(0)
  var totalUpperGap = BigInt(0)
  var worstLower = (BigInt(-1), -1, "")
  var worstUpper = (BigInt(-1), -1, "")

  def bucket(gap: BigInt): Int =
    gapBuckets.indexWhere(gap <= _) match
      case -1 => gapBuckets.size
      case value => value

  records.foreach { record =>
    val example = record.example
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map(SpaceFuzzer.argM -> example.arg))
    given PartialFunction[RoutinePtr, Routine] = PartialFunction.empty

    val actualLower = BigInt(example.result.paths.iterator.map(_.items.length).min)
    val actualUpper = BigInt(example.result.paths.iterator.map(_.items.length).max)
    val baseline = ResultPathLength.estimateBaseline(example.program)
    val refined = ResultPathLength.estimate(example.program)
    val baselineLower = baseline.lower.evaluate
    val baselineUpper = baseline.upper.evaluate
    val lower = refined.lower.evaluate
    val upper = refined.upper.evaluate

    require(lower.exists(_ <= actualLower),
      s"program ${record.id}: lower ${lower.fold("∞")(_.toString)} exceeds $actualLower; ${example.program.show}; ${refined.show}")
    require(upper.forall(_ >= actualUpper),
      s"program ${record.id}: upper ${upper.fold("∞")(_.toString)} is below $actualUpper; ${example.program.show}; ${refined.show}")
    require((baselineLower, lower) match
      case (Some(base), Some(value)) => value >= base
      case (None, None) => true
      case _ => false,
      s"program ${record.id}: refined lower weakened ${baseline.show} to ${refined.show}")
    require((baselineUpper, upper) match
      case (Some(base), Some(value)) => value <= base
      case (None, _) => true
      case _ => false,
      s"program ${record.id}: refined upper weakened ${baseline.show} to ${refined.show}")

    val lowerGap = actualLower - lower.get
    totalLowerGap += lowerGap
    lowerGaps(bucket(lowerGap)) += 1
    if lowerGap == 0 then exactLower += 1
    if lowerGap > worstLower._1 then worstLower = (lowerGap, record.id, example.program.show)
    if baselineLower.exists(lower.get > _) then improvedLower += 1

    upper.foreach { value =>
      finiteUpper += 1
      val upperGap = value - actualUpper
      totalUpperGap += upperGap
      upperGaps(bucket(upperGap)) += 1
      if upperGap == 0 then exactUpper += 1
      if upperGap > worstUpper._1 then worstUpper = (upperGap, record.id, example.program.show)
      if baselineUpper.forall(value < _) then improvedUpper += 1
    }

  }

  def labels: Vector[String] = gapBuckets.map {
    case 0 => "0"
    case boundary => s"≤$boundary"
  } :+ ">32"
  def rows(values: Array[Int]): String =
    labels.zip(values).map((label, value) => s"| $label | $value |").mkString("\n")
  def mean(total: BigInt, divisor: Int): String =
    if divisor == 0 then "n/a"
    else (BigDecimal(total) / BigDecimal(divisor)).setScale(3, BigDecimal.RoundingMode.HALF_UP).toString
  def short(value: String): String = if value.length <= 500 then value else value.take(499) + "…"

  val report =
    s"""~# Path-length audit: $count random programs
       ~
       ~- Corpus: seed `$seed`, depth `$maxDepth`, result cap `$maxResult`
       ~- Sound: yes; all $count lower and upper bounds contained their concrete result lengths
       ~- Finite upper bounds: $finiteUpper / $count
       ~- Exact lower bounds: $exactLower / $count
       ~- Exact finite upper bounds: $exactUpper / $finiteUpper
       ~- Z3 lower improvements over compositional baseline: $improvedLower
       ~- Z3 upper improvements over compositional baseline: $improvedUpper
       ~- Mean lower underestimate: ${mean(totalLowerGap, count)} path items
       ~- Mean finite upper overestimate: ${mean(totalUpperGap, finiteUpper)} path items
       ~- Least-tight lower: gap ${worstLower._1}, program ${worstLower._2}: `${short(worstLower._3).replace("|", "\\|")}`
       ~- Least-tight finite upper: gap ${worstUpper._1}, program ${worstUpper._2}: `${short(worstUpper._3).replace("|", "\\|")}`
       ~
       ~## Lower-bound additive underestimate
       ~
       ~| Gap | Programs |
       ~|---:|---:|
       ~${rows(lowerGaps)}
       ~
       ~## Finite upper-bound additive overestimate
       ~
       ~| Gap | Programs |
       ~|---:|---:|
       ~${rows(upperGaps)}
       ~""".stripMargin('~')
  Files.writeString(Paths.get(output), report, StandardCharsets.UTF_8)
  println(report)
