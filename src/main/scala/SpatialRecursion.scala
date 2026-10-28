package morkl

/** Syntax-only decreasing-measure evidence for recursive routine costs.
  * Failure to find evidence is deliberately inconclusive: the caller retains
  * named recursive cost atoms instead of pretending the recursion is free or
  * replacing a finite-but-unknown cost by infinity.
  */
object SpatialRecursion:
  private def subsetOf(value: Space, parameter: SpaceMention): Boolean = value match
    case Space.Mention(mention) => mention == parameter
    case Space.Intersection(left, right) => subsetOf(left, parameter) || subsetOf(right, parameter)
    case Space.Subtraction(left, _) => subsetOf(left, parameter)
    case Space.Restriction(left, _) => subsetOf(left, parameter)
    case Space.Raffination(left, _) => subsetOf(left, parameter)
    case Space.Range(source, _, _) => subsetOf(source, parameter)
    case Space.Union(left, right) => subsetOf(left, parameter) && subsetOf(right, parameter)
    case _ => false

  private def constantLength(value: Path): Option[Int] = value match
    case Path.Constant(path) => Some(path.items.length)
    case Path.Concat(left, right) => for a <- constantLength(left); b <- constantLength(right) yield a + b
    case Path.Deref(reference) if reference.lengthHint >= 0 => Some(reference.lengthHint)
    case _ => None

  /** Minimum number of path items consumed by this argument, if proved. */
  private def decrease(value: Space, parameter: SpaceMention, rests: Map[SpaceMention, Space]): Option[Int] = value match
    case Space.Empty => Some(1)
    case Space.TailsUnion(source) if subsetOf(source, parameter) => Some(1)
    case Space.TailsIntersection(source) if subsetOf(source, parameter) => Some(1)
    case Space.Unwrap(source, prefix) if subsetOf(source, parameter) => constantLength(prefix).filter(_ > 0)
    case Space.Mention(rest) if rests.get(rest).exists(subsetOf(_, parameter)) => Some(1)
    case Space.Subtraction(left, _) => decrease(left, parameter, rests)
    case Space.Restriction(left, _) => decrease(left, parameter, rests)
    case Space.Raffination(left, _) => decrease(left, parameter, rests)
    case Space.Range(source, _, _) => decrease(source, parameter, rests)
    case Space.Intersection(left, right) =>
      decrease(left, parameter, rests).orElse(decrease(right, parameter, rests))
    case Space.Union(left, right) =>
      decrease(left, parameter, rests).flatMap(a =>
        decrease(right, parameter, rests).map(b => a.min(b)))
    case _ => None

  private case class RecursiveArgument(values: Vector[Space], rests: Map[SpaceMention, Space])

  private def recursiveArguments(body: Space, routine: RoutinePtr): Vector[RecursiveArgument] =
    def walk(value: Space, rests: Map[SpaceMention, Space]): Vector[RecursiveArgument] = value match
      case Space.Call(name, _, mentions) =>
        val here = Option.when(name == routine)(RecursiveArgument(mentions, rests)).toVector
        here ++ mentions.flatMap(walk(_, rests))
      case binary @ (Space.Union(_, _) | Space.Intersection(_, _) |
           Space.Subtraction(_, _) | Space.Restriction(_, _) |
           Space.Raffination(_, _) | Space.Composition(_, _)) =>
        val (left, right) = binary match
          case Space.Union(a, b) => a -> b
          case Space.Intersection(a, b) => a -> b
          case Space.Subtraction(a, b) => a -> b
          case Space.Restriction(a, b) => a -> b
          case Space.Raffination(a, b) => a -> b
          case Space.Composition(a, b) => a -> b
        walk(left, rests) ++ walk(right, rests)
      case Space.Iteration(source, _, rest, templates) =>
        walk(source, rests) ++ walk(templates, rests.updated(rest, source))
      case Space.Fold(source, _, _, _, rest, templates, _) =>
        walk(source, rests) ++ walk(templates, rests.updated(rest, source))
      case Space.Fixpoint(initial, variable, step) =>
        walk(initial, rests) ++ walk(step, rests.updated(variable, initial))
      case unary @ (Space.Wrap(_, _) | Space.Unwrap(_, _) | Space.TailsUnion(_) |
           Space.TailsIntersection(_) | Space.PrefixClosure(_) |
           Space.SuffixClosure(_) | Space.TailsClosure(_) |
           Space.GroundedSS(_, _) | Space.Range(_, _, _)) =>
        val source = unary match
          case Space.Wrap(s, _) => s
          case Space.Unwrap(s, _) => s
          case Space.TailsUnion(s) => s
          case Space.TailsIntersection(s) => s
          case Space.PrefixClosure(s) => s
          case Space.SuffixClosure(s) => s
          case Space.TailsClosure(s) => s
          case Space.GroundedSS(s, _) => s
          case Space.Range(s, _, _) => s
        walk(source, rests)
      case _ => Vector.empty
    walk(body, Map.empty)

  /** A depth bound from an annotated input, when one parameter decreases on
    * every recursive edge. Symbolic maximum lengths remain named parameters.
    */
  def depthBound(routine: Routine, inputs: Vector[SpatialType]): Option[SizeExpr] =
    val calls = recursiveArguments(routine.body, routine.name)
    if calls.isEmpty then None
    else routine.mentions.indices.iterator.flatMap { index =>
      val parameter = routine.mentions(index)
      Option.when(index < inputs.size && calls.forall(_.values.size > index)) {
        calls.map(call => decrease(call.values(index), parameter, call.rests))
      }.filter(_.forall(_.nonEmpty)).map { amounts =>
        val consumed = amounts.flatten.min.max(1)
        inputs(index).pathLength.upper.annotatedBound(Z3BoundDirection.Upper) match
          case Some(maximum) => SizeExpr.const((maximum + consumed - 1) / consumed)
          case None => SizeExpr.symbol(s"ceilDepth(${parameter.s},$consumed)")
      }
    }.toSeq.headOption

  private def occurs(value: SizeExpr, name: String): Boolean = value match
    case SizeExpr.Symbol(found) => found == name
    case SizeExpr.Add(values) => values.exists(occurs(_, name))
    case SizeExpr.Multiply(values) => values.exists(occurs(_, name))
    case SizeExpr.Maximum(values) => values.exists(occurs(_, name))
    case SizeExpr.Minimum(values) => values.exists(occurs(_, name))
    case SizeExpr.PositiveDifference(left, right) => occurs(left, name) || occurs(right, name)
    case SizeExpr.Positive(inner) => occurs(inner, name)
    case SizeExpr.CeilingDivide(numerator, denominator) =>
      occurs(numerator, name) || occurs(denominator, name)
    case SizeExpr.GeometricSeries(branching, rounds) =>
      occurs(branching, name) || occurs(rounds, name)
    case SizeExpr.RangeCardinality(inner, _, _) => occurs(inner, name)
    case SizeExpr.IfZero(condition, ifZero, ifNonZero) =>
      occurs(condition, name) || occurs(ifZero, name) || occurs(ifNonZero, name)
    case SizeExpr.Z3Cardinality(_, _, baseline) => occurs(baseline, name)
    case _ => false

  /** Split `a + b*T` without distributing arbitrary expressions. */
  private def splitLinear(value: SizeExpr, name: String): Option[(SizeExpr, SizeExpr)] = value match
    case SizeExpr.Symbol(found) if found == name => Some(SizeExpr.Zero -> SizeExpr.One)
    case current if !occurs(current, name) => Some(current -> SizeExpr.Zero)
    case SizeExpr.Add(values) =>
      values.foldLeft(Option(SizeExpr.Zero -> SizeExpr.Zero)) { (state, term) => for
        accumulated <- state
        split <- splitLinear(term, name)
      yield SizeExpr.add(accumulated._1, split._1) -> SizeExpr.add(accumulated._2, split._2) }
    case SizeExpr.Multiply(values) =>
      val recursive = values.filter(occurs(_, name))
      if recursive.size != 1 then None
      else splitLinear(recursive.head, name).map { (additive, branching) =>
        val constant = SizeExpr.multiply(values.filterNot(_ eq recursive.head)*)
        SizeExpr.multiply(constant, additive) -> SizeExpr.multiply(constant, branching)
      }
    case _ => None

  private def close(value: SizeExpr, marker: String, depth: SizeExpr): SizeExpr =
    splitLinear(value, marker).fold(value) { (additive, branching) =>
      SpatialRecurrence.solve(additive, branching, depth)
    }

  def marker(name: RoutinePtr): SpatialCostEstimate =
    def interval(backend: String) =
      val work = SizeExpr.symbol(s"recWork(${name.s},$backend)")
      val allocation = SizeExpr.symbol(s"recAlloc(${name.s},$backend)")
      val rounds = SizeExpr.symbol(s"recRounds(${name.s},$backend)")
      SpatialCostInterval(
        SizeExpr.Zero, work,
        SizeExpr.Zero, allocation,
        SizeExpr.Zero, rounds,
        SpatialCostComponents(
          nodeVisits = SizeExpr.symbol(s"recNodeVisits(${name.s},$backend)"),
          patriciaVisits =
            if backend == "reference" || backend == "generic" then SizeExpr.Zero
            else SizeExpr.symbol(s"recPatriciaVisits(${name.s},$backend)"),
          pathComparisons = SizeExpr.symbol(s"recPathComparisons(${name.s},$backend)"),
          allocations = SizeExpr.symbol(s"recAllocations(${name.s},$backend)"),
          rounds = rounds,
        ),
      )
    val generic = interval("generic")
    SpatialCostEstimate(generic.workUpper, generic.allocationUpper,
      backend = SpatialBackend.values.map(value => value -> interval(value.toString.toLowerCase)).toMap,
      roundsUpper = generic.roundsUpper)

  def close(name: RoutinePtr, routine: Routine, inputs: Vector[SpatialType], value: SpatialType): SpatialType =
    depthBound(routine, inputs).fold(value) { depth =>
      def closed(interval: SpatialCostInterval, backend: String): SpatialCostInterval = interval.copy(
        workUpper = close(interval.workUpper, s"recWork(${name.s},$backend)", depth),
        allocationUpper = close(interval.allocationUpper, s"recAlloc(${name.s},$backend)", depth),
        roundsUpper = close(interval.roundsUpper, s"recRounds(${name.s},$backend)", depth),
        componentsUpper = SpatialCostComponents(
          nodeVisits = close(interval.componentsUpper.nodeVisits,
            s"recNodeVisits(${name.s},$backend)", depth),
          patriciaVisits = close(interval.componentsUpper.patriciaVisits,
            s"recPatriciaVisits(${name.s},$backend)", depth),
          pathComparisons = close(interval.componentsUpper.pathComparisons,
            s"recPathComparisons(${name.s},$backend)", depth),
          allocations = close(interval.componentsUpper.allocations,
            s"recAllocations(${name.s},$backend)", depth),
          rounds = close(interval.componentsUpper.rounds,
            s"recRounds(${name.s},$backend)", depth),
        ),
      )
      val generic = closed(value.cost.generic, "generic")
      value.copy(cost = SpatialCostEstimate(generic.workUpper, generic.allocationUpper,
        generic.workLower, generic.allocationLower,
        SpatialBackend.values.map { backend =>
          backend -> closed(value.cost.forBackend(backend), backend.toString.toLowerCase)
        }.toMap, generic.roundsUpper, generic.roundsLower))
    }
