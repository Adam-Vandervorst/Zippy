package morkl

@main def spatialTypeRandomAudit(
  count: Int = 1000,
  seed: Long = 20260708L,
  maxDepth: Int = 5,
  maxResult: Int = 400
): Unit =
  val records = SpaceFuzzerCorpus.generate(count, seed, maxDepth, maxResult)
  var exactSizes = 0
  var exactLengths = 0
  var sizeLowerImprovements = 0
  var sizeUpperImprovements = 0
  var lengthLowerImprovements = 0
  var lengthUpperImprovements = 0
  var checkedExactStrata = 0
  var unboundedSizes = 0
  var unboundedLengths = 0
  var unboundedStrata = 0
  var optimizedSound = 0

  records.foreach { record =>
    val example = record.example
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map(SpaceFuzzer.argM -> example.arg))
    given PartialFunction[RoutinePtr, Routine] = SpaceFuzzer.routines
    val assumptions = SpatialAssumptions(spaces = Map(SpaceFuzzer.argM -> SpatialType.exact(example.arg)))
    val spatial = SpatialTypeAnalysis.output(example.program, assumptions, SpaceFuzzer.routines)
    val optimizedSpatial = SpatialTypeAnalysis.output(
      Supercompiler.normalize(example.program).space, assumptions, SpaceFuzzer.routines)
    val scalarSize = ResultSpaceSize.estimate(example.program, assumptions.sizeAssumptions)
    val scalarLength = ResultPathLength.estimate(example.program, assumptions.lengthAssumptions,
      assumptions.pathLengthAssumptions, assumptions.sizeAssumptions)
    val actualSize = BigInt(example.result.paths.size)
    val actualMin = BigInt(example.result.paths.map(_.items.length).min)
    val actualMax = BigInt(example.result.paths.map(_.items.length).max)
    val lower = spatial.size.lower.annotatedBound(Z3BoundDirection.Lower).getOrElse(BigInt(0))
    val upper = spatial.size.upper.annotatedBound(Z3BoundDirection.Upper)
    val minLength = spatial.pathLength.lower.annotatedBound(Z3BoundDirection.Lower).getOrElse(BigInt(0))
    val maxLength = spatial.pathLength.upper.annotatedBound(Z3BoundDirection.Upper)
    if upper.isEmpty then unboundedSizes += 1
    if maxLength.isEmpty then unboundedLengths += 1

    require(lower <= actualSize && upper.forall(_ >= actualSize),
      s"program ${record.id}: spatial size [$lower,${upper.getOrElse("∞")}] misses $actualSize; ${example.program.show}; ${spatial.show}")
    require(minLength <= actualMin && maxLength.forall(_ >= actualMax),
      s"program ${record.id}: spatial length [$minLength,${maxLength.getOrElse("∞")}] misses [$actualMin,$actualMax]; ${example.program.show}; ${spatial.show}")
    require(SpatialMembership.gammaMember(example.result, spatial),
      s"program ${record.id}: full spatial gamma omits concrete output; ${example.program.show}; ${spatial.show}")
    val optimizedLower = optimizedSpatial.size.lower.annotatedBound(Z3BoundDirection.Lower).getOrElse(BigInt(0))
    val optimizedUpper = optimizedSpatial.size.upper.annotatedBound(Z3BoundDirection.Upper)
    val optimizedMin = optimizedSpatial.pathLength.lower.annotatedBound(Z3BoundDirection.Lower).getOrElse(BigInt(0))
    val optimizedMax = optimizedSpatial.pathLength.upper.annotatedBound(Z3BoundDirection.Upper)
    require(optimizedLower <= actualSize && optimizedUpper.forall(_ >= actualSize) &&
      optimizedMin <= actualMin && optimizedMax.forall(_ >= actualMax),
      s"optimized program ${record.id}: spatial envelope misses concrete result")
    optimizedSound += 1
    scalarSize.lower.annotatedBound(Z3BoundDirection.Lower).foreach { value =>
      require(lower >= value, s"program ${record.id}: spatial size lower $lower weaker than Z3 $value")
      if lower > value then sizeLowerImprovements += 1
    }
    scalarSize.upper.annotatedBound(Z3BoundDirection.Upper).foreach { value =>
      require(upper.exists(_ <= value), s"program ${record.id}: spatial size upper $upper weaker than Z3 $value")
      if upper.exists(_ < value) then sizeUpperImprovements += 1
    }
    scalarLength.lower.annotatedBound(Z3BoundDirection.Lower).foreach { value =>
      require(minLength >= value, s"program ${record.id}: spatial length lower $minLength weaker than Z3 $value")
      if minLength > value then lengthLowerImprovements += 1
    }
    scalarLength.upper.annotatedBound(Z3BoundDirection.Upper).foreach { value =>
      require(maxLength.exists(_ <= value), s"program ${record.id}: spatial length upper $maxLength weaker than Z3 $value")
      if maxLength.exists(_ < value) then lengthUpperImprovements += 1
    }
    if lower == actualSize && upper.contains(actualSize) then exactSizes += 1
    if minLength == actualMin && maxLength.contains(actualMax) then exactLengths += 1

    val collapsed = spatial.collapseByLength
    if collapsed.forall(_.exactLength.nonEmpty) then
      val actualByLength = example.result.paths.groupBy(_.items.length).view.mapValues(paths => BigInt(paths.size)).toMap
      collapsed.foreach { stratum =>
        val length = stratum.exactLength.get
        val actual = actualByLength.getOrElse(length, BigInt(0))
        val stratumLower = stratum.cardinality.lower.annotatedBound(Z3BoundDirection.Lower).getOrElse(BigInt(0))
        val stratumUpper = stratum.cardinality.upper.annotatedBound(Z3BoundDirection.Upper)
        if stratumUpper.isEmpty then unboundedStrata += 1
        require(stratumLower <= actual && stratumUpper.forall(_ >= actual),
          s"program ${record.id}: length-$length stratum [$stratumLower,${stratumUpper.getOrElse("∞")}] misses $actual; ${example.program.show}; ${spatial.show}")
      }
      val represented = collapsed.flatMap(_.exactLength).toSet
      require(actualByLength.keySet.subsetOf(represented),
        s"program ${record.id}: spatial type omitted lengths ${actualByLength.keySet -- represented}; ${example.program.show}; ${spatial.show}")
      checkedExactStrata += 1
  }

  println(
    s"spatial audit: programs=$count sound=$count optimizedSound=$optimizedSound exactSizes=$exactSizes exactLengths=$exactLengths " +
      s"sizeImprovements=$sizeLowerImprovements/$sizeUpperImprovements " +
      s"lengthImprovements=$lengthLowerImprovements/$lengthUpperImprovements exactStrataChecked=$checkedExactStrata " +
      s"unbounded=$unboundedSizes/$unboundedLengths/$unboundedStrata"
  )

@main def spatialTypeScalingAudit(
  minimumPower: Int = 10,
  maximumPower: Int = 15,
  runs: Int = 7
): Unit =
  require(minimumPower >= 1 && maximumPower >= minimumPower && runs >= 1)

  def balanced(values: Vector[Space]): Space =
    if values.size == 1 then values.head
    else
      val middle = values.size / 2
      Space.Union(balanced(values.take(middle)), balanced(values.drop(middle)))

  def median(values: Vector[Double]): Double = values.sorted.apply(values.size / 2)

  for power <- minimumPower to maximumPower do
    val leaves = 1 << power
    val expression = balanced(Vector.tabulate(leaves) { index =>
      Space.Singleton(Path.Constant(PathValue(List(PathItem(s"scale_$index")))))
    })
    SpatialTypeAnalysis.output(expression)
    val samples = Vector.fill(runs) {
      val started = System.nanoTime()
      val result = SpatialTypeAnalysis.output(expression)
      val elapsed = (System.nanoTime() - started).toDouble / 1_000_000.0
      require(result.strata.nonEmpty && result.size.upper != SizeExpr.Zero)
      elapsed
    }
    println(f"spatial scaling: leaves=$leaves%6d medianMs=${median(samples)}%.3f")

/** Open-input companion to [[spatialTypeRandomAudit]]. It reuses the exact
  * same generated programs and concrete witnesses, but analysis receives only
  * one declared input envelope, never `SpatialType.exact(example.arg)`. */
@main def spatialTypeOpenRandomAudit(
  count: Int = 1000,
  seed: Long = 20260708L,
  maxDepth: Int = 5,
  maxResult: Int = 400,
  extended: Boolean = false,
): Unit =
  val records = SpaceFuzzerCorpus.generate(count, seed, maxDepth, maxResult, extended)
  val spaceKinds = records.flatMap(_.opKinds).filter(_.startsWith("Space.")).toSet
  val callPrograms = records.count(_.opKinds.contains("Space.Call"))
  if extended && count >= 1000 then
    val expected = Set("Empty", "Call", "Mention", "Singleton", "Literal", "Union", "Intersection",
      "Subtraction", "Restriction", "Raffination", "Composition", "Iteration", "Fold", "Fixpoint",
      "Wrap", "Unwrap", "TailsUnion", "TailsIntersection", "PrefixClosure", "SuffixClosure",
      "TailsClosure", "GroundedPS", "GroundedSS", "Range").map("Space." + _)
    require(expected.subsetOf(spaceKinds), s"extended fuzzer missed ${expected -- spaceKinds}")
  val declaredInput = SpatialType.fromStrata(Vector(SpatialStratum(
    PathLengthEstimate.unknown,
    ResultSizeEstimate(SizeExpr.const(28), SizeExpr.One),
  )))
  var finiteUpper = 0
  var exactSize = 0
  val sizeSlack = collection.mutable.Map.empty[String, Int].withDefaultValue(0)

  def bucket(value: Option[BigInt]): String = value match
    case None => "infinity"
    case Some(n) if n == 0 => "0"
    case Some(n) if n <= 2 => "1-2"
    case Some(n) if n <= 8 => "3-8"
    case Some(n) if n <= 32 => "9-32"
    case Some(_) => "33+"

  records.foreach { record =>
    val example = record.example
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map(SpaceFuzzer.argM -> example.arg))
    given PartialFunction[RoutinePtr, Routine] = SpaceFuzzer.routines
    val assumptions = SpatialAssumptions(
      spaces = Map(SpaceFuzzer.argM -> declaredInput),
      config = if extended then SpatialAnalysisConfig(analysisNodeBudget = 1000)
        else SpatialAnalysisConfig(),
    )
    require(SpatialMembership.gammaMember(example.arg, declaredInput),
      s"open program ${record.id}: concrete argument is outside its declared input")
    val spatial = SpatialTypeAnalysis.output(example.program, assumptions, SpaceFuzzer.routines)
    val actualSize = BigInt(example.result.paths.size)
    val actualMin = BigInt(example.result.paths.map(_.items.length).min)
    val actualMax = BigInt(example.result.paths.map(_.items.length).max)
    val lower = spatial.size.lower.annotatedBound(Z3BoundDirection.Lower).getOrElse(BigInt(0))
    val upper = spatial.size.upper.annotatedBound(Z3BoundDirection.Upper)
    val minLength = spatial.pathLength.lower.annotatedBound(Z3BoundDirection.Lower).getOrElse(BigInt(0))
    val maxLength = spatial.pathLength.upper.annotatedBound(Z3BoundDirection.Upper)
    require(lower <= actualSize && upper.forall(_ >= actualSize),
      s"open program ${record.id}: size [$lower,${upper.getOrElse("∞")}] misses $actualSize; ${example.program.show}; ${spatial.show}")
    require(minLength <= actualMin && maxLength.forall(_ >= actualMax),
      s"open program ${record.id}: length [$minLength,${maxLength.getOrElse("∞")}] misses [$actualMin,$actualMax]; ${example.program.show}; ${spatial.show}")
    require(SpatialMembership.gammaMember(example.result, spatial),
      s"open program ${record.id}: full spatial gamma omits concrete output; ${example.program.show}; ${spatial.show}")
    upper.foreach { value =>
      finiteUpper += 1
      if value == actualSize && lower == actualSize then exactSize += 1
    }
    sizeSlack.update(bucket(upper.map(_ - actualSize)), sizeSlack(bucket(upper.map(_ - actualSize))) + 1)
  }

  val distribution = sizeSlack.toVector.sortBy(_._1).map((name, n) => s"$name=$n").mkString(",")
  println(s"spatial open audit: programs=$count sound=$count extended=$extended finiteUppers=$finiteUpper " +
    s"exactSizes=$exactSize spaceConstructors=${spaceKinds.size}/24 callPrograms=$callPrograms upperSlack={$distribution}")

/** Soundness hunt with deliberately approximate (but inhabited) annotations.
  * This is distinct from exact-input validation and catches refinements that
  * accidentally smuggle concrete observations into the abstract state. */
@main def spatialTypeAdversarialGammaAudit(
  count: Int = 1000,
  seed: Long = 20260708L,
  maxDepth: Int = 6,
  maxResult: Int = 400,
): Unit =
  val records = SpaceFuzzerCorpus.generate(count, seed, maxDepth, maxResult, extended = true)
  var envelopeAccepted = 0
  var gammaAccepted = 0
  records.foreach { record =>
    val example = record.example
    val byLength = example.arg.paths.groupBy(_.items.length).toVector.sortBy(_._1)
    val declared = SpatialType.fromStrata(byLength.map { (length, paths) =>
      SpatialStratum(PathLengthEstimate.exact(PathLengthExpr.const(length)),
        ResultSizeEstimate(SizeExpr.const(paths.size + 3), SizeExpr.Zero))
    }, sizeOverride = Some(ResultSizeEstimate(SizeExpr.const(example.arg.paths.size + 6), SizeExpr.Zero)))
    require(SpatialMembership.gammaMember(example.arg, declared), s"${record.id}: malformed approximate declaration")
    val assumptions = SpatialAssumptions(spaces = Map(SpaceFuzzer.argM -> declared),
      config = SpatialAnalysisConfig(analysisNodeBudget = 1500))
    val result = SpatialTypeAnalysis.output(example.program, assumptions, SpaceFuzzer.routines)
    if SpatialMembership.satisfies(example.result, result) then envelopeAccepted += 1
    if SpatialMembership.gammaMember(example.result, result) then gammaAccepted += 1
    require(SpatialMembership.gammaMember(example.result, result),
      s"adversarial ${record.id}: γ violation; ${example.program.show}; declared=${declared.show}; result=${result.show}")
  }
  println(s"spatial adversarial gamma audit: programs=$count envelope=$envelopeAccepted gamma=$gammaAccepted sound=$gammaAccepted")

@main def spatialSpecializationCorpusAudit(
  count: Int = 1000,
  seed: Long = 20260708L,
  maxDepth: Int = 5,
  maxResult: Int = 400,
): Unit =
  val records = SpaceFuzzerCorpus.generate(count, seed, maxDepth, maxResult)
  var rewritten = 0
  records.foreach { record =>
    val routine = Routine(RoutinePtr(s"spatial_specialize_${record.id}"), Vector.empty,
      Vector(SpaceFuzzer.argM), record.example.program)
    val selection = SpatialCompilation.selectApplicable(
      routine,
      SpatialRoutineAnnotations(spaces = Map(SpaceFuzzer.argM -> SpatialType.exact(record.example.arg))),
      Map(SpaceFuzzer.argM -> record.example.arg),
      Map.empty,
      SpaceFuzzer.routines,
    )
    val specialized = selection.specialization.getOrElse(
      throw IllegalStateException(s"${record.id}: exact argument did not select its guarded residual"))
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map(SpaceFuzzer.argM -> record.example.arg))
    given PartialFunction[RoutinePtr, Routine] = SpaceFuzzer.routines
    val residualResult = eval(specialized.residual.body)
    require(residualResult == record.example.result,
      s"specialized ${record.id} changed meaning; original=${record.example.program.show}; residual=${specialized.residual.body.show}")
    if specialized.facts.nonEmpty then rewritten += 1
  }
  println(s"spatial production-specialization corpus: programs=$count preserved=$count selected=$count rewritten=$rewritten")
