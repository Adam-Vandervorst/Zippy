package morkl

import java.nio.charset.StandardCharsets
import java.util.concurrent.TimeUnit
import java.io.ByteArrayOutputStream
import java.util.concurrent.atomic.AtomicReference
import scala.collection.concurrent.TrieMap
import scala.collection.mutable
import scala.util.DynamicVariable

enum Z3BoundDirection:
  case Lower, Upper

enum Z3AtomRelation:
  case Subset(left: Int, right: Int)
  case Disjoint(left: Int, right: Int)

  def render: String = this match
    case Z3AtomRelation.Subset(left, right) => s"a$left<=a$right"
    case Z3AtomRelation.Disjoint(left, right) => s"a$left#a$right"

enum Z3SetFormula:
  case False
  case Atom(index: Int)
  case Or(left: Z3SetFormula, right: Z3SetFormula)
  case And(left: Z3SetFormula, right: Z3SetFormula)
  case Not(value: Z3SetFormula)

  def render: String = this match
    case Z3SetFormula.False => "false"
    case Z3SetFormula.Atom(index) => s"a$index"
    case Z3SetFormula.Or(left, right) => s"(or ${left.render} ${right.render})"
    case Z3SetFormula.And(left, right) => s"(and ${left.render} ${right.render})"
    case Z3SetFormula.Not(value) => s"(not ${value.render})"

  def contains(mask: Int): Boolean = this match
    case Z3SetFormula.False => false
    case Z3SetFormula.Atom(index) => (mask & (1 << index)) != 0
    case Z3SetFormula.Or(left, right) => left.contains(mask) || right.contains(mask)
    case Z3SetFormula.And(left, right) => left.contains(mask) && right.contains(mask)
    case Z3SetFormula.Not(value) => !value.contains(mask)

final class MissingZ3Executable(message: String, cause: Throwable)
    extends IllegalStateException(message, cause)

enum Z3Diagnostic:
  case ProcessTimeout(command: Vector[String], timeoutMillis: Long)
  case NonZeroExit(command: Vector[String], exitCode: Int)
  case ProcessIoFailure(command: Vector[String], channel: String, detail: String)
  case SolverTimeout(obligation: String, timeoutMillis: Long)
  case SolverUnknown(obligation: String, reason: String)

  def show: String = this match
    case Z3Diagnostic.ProcessTimeout(command, timeoutMillis) =>
      s"Z3 timed out: process '${command.mkString(" ")}' exceeded ${timeoutMillis}ms"
    case Z3Diagnostic.NonZeroExit(command, exitCode) =>
      s"Z3 process '${command.mkString(" ")}' exited with status $exitCode"
    case Z3Diagnostic.ProcessIoFailure(command, channel, detail) =>
      s"Z3 process '${command.mkString(" ")}' failed on $channel: $detail"
    case Z3Diagnostic.SolverTimeout(obligation, timeoutMillis) =>
      s"Z3 timed out after ${timeoutMillis}ms in $obligation; compositional fallback retained"
    case Z3Diagnostic.SolverUnknown(obligation, reason) =>
      s"Z3 returned unknown in $obligation ($reason); compositional fallback retained"

case class Z3AnalysisReport[+A](value: A, diagnostics: Vector[Z3Diagnostic]):
  def degraded: Boolean = diagnostics.nonEmpty

object Z3Diagnostics:
  private val sinks = DynamicVariable(List.empty[mutable.ArrayBuffer[Z3Diagnostic]])

  /** Publish every degradation at the point where it is observed. Capturing
    * callers additionally receive structured data, but ordinary analysis must
    * not turn the solver's one-second `unknown/timeout` into a silent fallback.
    */
  private[morkl] def emit(diagnostic: Z3Diagnostic): Unit =
    sinks.value.foreach(_ += diagnostic)
    Console.err.println(diagnostic.show)

  /** Capture solver degradation as data suitable for reports. Diagnostics are
    * also forwarded to an enclosing capture, so nested spatial/size analyses
    * cannot hide a timeout. */
  def capture[A](body: => A): Z3AnalysisReport[A] =
    val collected = mutable.ArrayBuffer.empty[Z3Diagnostic]
    val value = sinks.withValue(collected :: sinks.value)(body)
    Z3AnalysisReport(value, collected.toVector)

private[morkl] object Z3Executable:
  private val executable = Option(System.getProperty("morkl.z3")).filter(_.nonEmpty).getOrElse("z3")
  private val timeoutMillis = Option(System.getProperty("morkl.z3.timeoutMillis"))
    .flatMap(_.toLongOption).getOrElse(1000L).max(1L)

  private[morkl] def runCommand(
    command: Seq[String],
    script: String,
    waitMillis: Long = timeoutMillis + 500L
  ): Option[String] =
    val process =
      try ProcessBuilder(command*).redirectErrorStream(true).start()
      catch
        case error: java.io.IOException =>
          throw MissingZ3Executable(
            s"unable to start Z3 command '${command.mkString(" ")}'. Install Z3 or set -Dmorkl.z3=/path/to/z3",
            error
          )
    val output = ByteArrayOutputStream()
    val writerFailure = AtomicReference[Throwable | Null](null)
    val readerFailure = AtomicReference[Throwable | Null](null)
    val writerTask: Runnable = () =>
      try
        val writer = process.outputWriter(StandardCharsets.UTF_8)
        try writer.write(script)
        finally writer.close()
      catch case error: Throwable => writerFailure.set(error)
    val readerTask: Runnable = () =>
      try
        process.getInputStream.transferTo(output)
        ()
      catch case error: Throwable => readerFailure.set(error)
    val writerThread = new Thread(writerTask, "morkl-z3-stdin")
    val readerThread = new Thread(readerTask, "morkl-z3-stdout")
    writerThread.setDaemon(true)
    readerThread.setDaemon(true)
    writerThread.start()
    readerThread.start()
    if !process.waitFor(waitMillis, TimeUnit.MILLISECONDS) then
      process.descendants().forEach(child =>
        child.destroyForcibly()
        ()
      )
      process.destroyForcibly()
      process.waitFor(50L, TimeUnit.MILLISECONDS)
      // Closing while another thread is blocked in write can wait on the
      // stream monitor. Destroy first so the writer is released by EPIPE.
      try process.getOutputStream.close() catch case _: Throwable => ()
      try process.getInputStream.close() catch case _: Throwable => ()
      writerThread.join(50L)
      readerThread.join(50L)
      val diagnostic = Z3Diagnostic.ProcessTimeout(command.toVector, waitMillis)
      Z3Diagnostics.emit(diagnostic)
      None
    else
      // Normally process exit closes both pipes immediately. Keep an explicit
      // secondary deadline for a hostile descendant that inherited a pipe;
      // partial output is rejected rather than returned as a successful solve.
      val ioJoinMillis = waitMillis.max(250L)
      writerThread.join(ioJoinMillis)
      readerThread.join(ioJoinMillis)
      if writerThread.isAlive || readerThread.isAlive then
        // These are daemon helpers. Do not synchronously close a stream while
        // its helper owns the stream monitor; interruption plus a degraded
        // result keeps this call bounded and the OS closes the pipe at EOF.
        writerThread.interrupt()
        readerThread.interrupt()
        val channels = Vector(
          Option.when(writerThread.isAlive)("stdin"),
          Option.when(readerThread.isAlive)("stdout/stderr"),
        ).flatten.mkString("+")
        val diagnostic = Z3Diagnostic.ProcessIoFailure(
          command.toVector, channels, s"pipe did not reach EOF within ${ioJoinMillis}ms")
        Z3Diagnostics.emit(diagnostic)
        return None
      val rendered = new String(output.toByteArray, StandardCharsets.UTF_8)
      val ioFailure = Option(writerFailure.get()).map("stdin" -> _)
        .orElse(Option(readerFailure.get()).map("stdout" -> _))
      if ioFailure.nonEmpty then
        val (channel, error) = ioFailure.get
        val diagnostic = Z3Diagnostic.ProcessIoFailure(
          command.toVector, channel, Option(error.getMessage).getOrElse(error.getClass.getSimpleName))
        Z3Diagnostics.emit(diagnostic)
        None
      else if process.exitValue() == 0 then Some(rendered)
      else
        val diagnostic = Z3Diagnostic.NonZeroExit(command.toVector, process.exitValue())
        Z3Diagnostics.emit(diagnostic)
        None

  def run(script: String): Option[String] =
    runCommand(Vector(executable, "-in", "-smt2"), script)

  def timeoutOption: String = s"(set-option :timeout $timeoutMillis)\n"
  def solverTimeoutMillis: Long = timeoutMillis

  private[morkl] def reportSolverUnknown(output: String, obligation: String): Boolean =
    val unknown = output.contains("unknown")
    if unknown then
      if !output.contains(":reason-unknown") || output.toLowerCase.contains("timeout") then
        Z3Diagnostics.emit(Z3Diagnostic.SolverTimeout(obligation, timeoutMillis))
      else
        val reason = output.linesIterator.find(_.contains(":reason-unknown")).getOrElse("unknown")
        Z3Diagnostics.emit(Z3Diagnostic.SolverUnknown(obligation, reason))
    unknown

case class Z3CardinalityProblem(
  formula: Z3SetFormula,
  atoms: Vector[ResultSizeEstimate],
  relations: Vector[Z3AtomRelation] = Vector.empty
):
  def show: String =
    val shownRelations = if relations.isEmpty then "" else relations.map(_.render).mkString("; relations=", ",", "")
    s"${formula.render}; atoms=${atoms.size}$shownRelations"

  def solve(direction: Z3BoundDirection)(using
    pc: PathContext,
    sc: SpaceContext,
    rc: PartialFunction[RoutinePtr, Routine]
  ): Option[BigInt] =
    val bounds = atoms.map { atom => atom.lower.evaluate -> atom.upper.evaluate }
    Z3CardinalitySolver.solve(formula, bounds, relations, direction)

  /** Solve from abstract atom annotations only. Opaque atoms remain unknown
    * instead of being measured by the concrete evaluator. */
  def solveAnnotated(direction: Z3BoundDirection): Option[BigInt] =
    val bounds = atoms.map { atom =>
      atom.lower.annotatedBound(Z3BoundDirection.Lower) -> atom.upper.annotatedBound(Z3BoundDirection.Upper)
    }
    Z3CardinalitySolver.solve(formula, bounds, relations, direction)

private object Z3CardinalitySolver:
  private case class Solution(lower: Option[BigInt], upper: Option[BigInt])
  private val cache = TrieMap.empty[String, Solution]
  private val integerPattern = raw"\(\(result (-?[0-9]+)\)\)".r

  private def sum(terms: Iterable[String]): String =
    val values = terms.toVector
    values match
      case Vector() => "0"
      case Vector(value) => value
      case _ => values.mkString("(+ ", " ", ")")

  private def sectionValue(output: String, marker: String): Option[BigInt] =
    output.split(marker, 2).lift(1).flatMap { suffix =>
      val section = suffix.split("(?:LOWER|UPPER)", 2).headOption.getOrElse(suffix)
      integerPattern.findFirstMatchIn(section).map(m => BigInt(m.group(1)))
    }

  private def query(
    formula: Z3SetFormula,
    bounds: Vector[(Option[BigInt], Option[BigInt])],
    relations: Vector[Z3AtomRelation]
  ): Solution =
    val atomCount = bounds.size
    if atomCount == 0 then return Solution(Some(BigInt(0)), Some(BigInt(0)))
    if atomCount >= 30 then return Solution(None, None)
    val masks = 1 until (1 << atomCount)
    val declarations = masks.map(mask => s"(declare-const r$mask Int)\n(assert (>= r$mask 0))").mkString("\n")
    val constraints = bounds.indices.flatMap { atom =>
      val cardinality = sum(masks.iterator.filter(mask => (mask & (1 << atom)) != 0).map(mask => s"r$mask").toVector)
      val (lower, upper) = bounds(atom)
      lower.map(value => s"(assert (>= $cardinality $value))").toVector ++
        upper.map(value => s"(assert (<= $cardinality $value))").toVector
    }.mkString("\n")
    val relationConstraints = relations.flatMap {
      case Z3AtomRelation.Subset(left, right) =>
        masks.iterator
          .filter(mask => (mask & (1 << left)) != 0 && (mask & (1 << right)) == 0)
          .map(mask => s"(assert (= r$mask 0))")
          .toVector
      case Z3AtomRelation.Disjoint(left, right) =>
        masks.iterator
          .filter(mask => (mask & (1 << left)) != 0 && (mask & (1 << right)) != 0)
          .map(mask => s"(assert (= r$mask 0))")
          .toVector
    }.distinct.mkString("\n")
    val objective = sum(masks.iterator.filter(formula.contains).map(mask => s"r$mask").toVector)
    val canMaximize = bounds.forall(_._2.nonEmpty)
    val upperQuery =
      if canMaximize then
        s"""(echo "UPPER")
           |(push)
           |(maximize result)
           |(check-sat)
           |(get-value (result))
           |(pop)
           |""".stripMargin
      else ""
    val script =
      s"""${Z3Executable.timeoutOption}(set-logic QF_LIA)
         |$declarations
         |$constraints
         |$relationConstraints
         |(define-fun result () Int $objective)
         |(echo "LOWER")
         |(push)
         |(minimize result)
         |(check-sat)
         |(get-value (result))
         |(pop)
         |$upperQuery
         |""".stripMargin
    Z3Executable.run(script) match
      case Some(output) if !output.contains("unknown") && !output.contains("error") =>
        Solution(sectionValue(output, "LOWER"), if canMaximize then sectionValue(output, "UPPER") else None)
      case Some(output) if Z3Executable.reportSolverUnknown(output, "cardinality optimization") =>
        Solution(None, None)
      case _ => Solution(None, None)

  def solve(
    formula: Z3SetFormula,
    bounds: Vector[(Option[BigInt], Option[BigInt])],
    relations: Vector[Z3AtomRelation],
    direction: Z3BoundDirection
  ): Option[BigInt] =
    if bounds.exists { case (Some(lower), Some(upper)) => lower > upper; case _ => false } then None
    else
      val key = formula.render +
        bounds.map { case (lower, upper) => s":${lower.getOrElse("_")}:${upper.getOrElse("_")}" }.mkString +
        relations.map(relation => s":${relation.render}").mkString
      val solution = cache.get(key).getOrElse {
        val computed = query(formula, bounds, relations)
        // A degraded result must be retried and re-reported on the next
        // analysis, rather than becoming an unmarked process-wide cache hit.
        if computed.lower.nonEmpty || computed.upper.nonEmpty then cache.putIfAbsent(key, computed).getOrElse(computed)
        else computed
      }
      direction match
        case Z3BoundDirection.Lower => solution.lower
        case Z3BoundDirection.Upper => solution.upper

private object Z3BooleanRelations:
  case class Relations(leftSubsetRight: Boolean, rightSubsetLeft: Boolean, disjoint: Boolean)

  private val cache = TrieMap.empty[String, Option[Relations]]

  private def status(output: String, marker: String): Option[String] =
    output.split(marker, 2).lift(1).flatMap(_.linesIterator.map(_.trim).find(line => line == "sat" || line == "unsat" || line == "unknown"))

  def solve(left: Z3SetFormula, right: Z3SetFormula, atomCount: Int): Option[Relations] =
    val key = s"$atomCount:${left.render}:${right.render}"
    cache.get(key).getOrElse {
      val declarations = (0 until atomCount).map(index => s"(declare-const a$index Bool)").mkString("\n")
      def check(marker: String, counterexample: String): String =
        s"""(echo "$marker")
           |(push)
           |(assert $counterexample)
           |(check-sat)
           |(pop)
           |""".stripMargin
      val script =
        s"""${Z3Executable.timeoutOption}(set-logic QF_UF)
           |$declarations
           |${check("LEFT_SUBSET", s"(and ${left.render} (not ${right.render}))")}
           |${check("RIGHT_SUBSET", s"(and ${right.render} (not ${left.render}))")}
           |${check("DISJOINT", s"(and ${left.render} ${right.render})")}
           |""".stripMargin
      val computed = Z3Executable.run(script).flatMap { output =>
        Z3Executable.reportSolverUnknown(output, "Boolean relation checks")
        for
          leftStatus <- status(output, "LEFT_SUBSET")
          rightStatus <- status(output, "RIGHT_SUBSET")
          disjointStatus <- status(output, "DISJOINT")
          if leftStatus != "unknown" && rightStatus != "unknown" && disjointStatus != "unknown"
        yield Relations(leftStatus == "unsat", rightStatus == "unsat", disjointStatus == "unsat")
      }
      computed.foreach(value => cache.putIfAbsent(key, Some(value)))
      computed
    }

object Z3ResultSpaceSize:
  private val maxAtoms = Option(System.getProperty("morkl.z3.maxCardinalityAtoms"))
    .flatMap(_.toIntOption).getOrElse(8).max(1).min(16)
  private val maxBooleanNodes = Option(System.getProperty("morkl.z3.maxBooleanNodes"))
    .flatMap(_.toIntOption).getOrElse(256).max(1)

  private case class Encoding(
    formula: Z3SetFormula,
    atoms: Vector[Space],
    occurrences: Vector[Int],
    relations: Vector[Z3AtomRelation]
  )
  private case class CorrelationScan(
    repeated: Boolean,
    relational: Boolean,
    booleanNodes: Int,
    operationOpportunity: Boolean
  )

  /** Content-free subset facts exported by operations whose result selects
    * paths from an input.  These facts cross the opaque-atom boundaries of the
    * Boolean cardinality encoding.
    */
  private def structurallySubset(left: Space, right: Space, fuel: Int = 64): Boolean =
    if fuel <= 0 then false
    else if left == Space.Empty || left == right then true
    else left match
      case Space.Union(a, b) =>
        structurallySubset(a, right, fuel - 1) && structurallySubset(b, right, fuel - 1)
      case Space.Intersection(a, b) =>
        structurallySubset(a, right, fuel - 1) || structurallySubset(b, right, fuel - 1)
      case Space.Subtraction(a, _) => structurallySubset(a, right, fuel - 1)
      case Space.Restriction(a, _) => structurallySubset(a, right, fuel - 1)
      case Space.Raffination(a, _) => structurallySubset(a, right, fuel - 1)
      case Space.Range(a, _, _) => structurallySubset(a, right, fuel - 1)
      case _ => right match
        case Space.Union(a, b) =>
          structurallySubset(left, a, fuel - 1) || structurallySubset(left, b, fuel - 1)
        case Space.Intersection(a, b) =>
          structurallySubset(left, a, fuel - 1) && structurallySubset(left, b, fuel - 1)
        case _ => false

  private def structurallyDisjoint(left: Space, right: Space, fuel: Int = 64): Boolean =
    if fuel <= 0 then false
    else if left == Space.Empty || right == Space.Empty then true
    else (left, right) match
      case (Space.Union(a, b), other) =>
        structurallyDisjoint(a, other, fuel - 1) && structurallyDisjoint(b, other, fuel - 1)
      case (other, Space.Union(a, b)) =>
        structurallyDisjoint(other, a, fuel - 1) && structurallyDisjoint(other, b, fuel - 1)
      case (Space.Intersection(a, b), other) =>
        structurallyDisjoint(a, other, fuel - 1) || structurallyDisjoint(b, other, fuel - 1)
      case (other, Space.Intersection(a, b)) =>
        structurallyDisjoint(other, a, fuel - 1) || structurallyDisjoint(other, b, fuel - 1)
      case (Space.Subtraction(_, removed), other) if structurallySubset(other, removed, fuel - 1) => true
      case (other, Space.Subtraction(_, removed)) if structurallySubset(other, removed, fuel - 1) => true
      case (Space.Restriction(source, prefixes), Space.Raffination(otherSource, otherPrefixes)) =>
        source == otherSource && prefixes == otherPrefixes
      case (Space.Raffination(source, prefixes), Space.Restriction(otherSource, otherPrefixes)) =>
        source == otherSource && prefixes == otherPrefixes
      case _ => false

  private def strengthen(baseline: ResultSizeEstimate, refinement: ResultSizeEstimate): ResultSizeEstimate =
    if baseline == refinement then baseline
    else if refinement.exact &&
        SizeExpr.provablyNoGreater(baseline.lower, refinement.lower) &&
        SizeExpr.provablyNoGreater(refinement.upper, baseline.upper) then refinement
    else ResultSizeEstimate(
      if baseline.upper == refinement.upper then baseline.upper else SizeExpr.minimum(baseline.upper, refinement.upper),
      if baseline.lower == refinement.lower then baseline.lower else SizeExpr.maximum(baseline.lower, refinement.lower)
    )

  /** A linear fast-path guard.  Z3 can improve a component when an atom repeats
    * or when an operation exposes a subset/disjointness relation.  Avoid
    * rebuilding and re-encoding the common uncorrelated case (in particular
    * large unions of distinct leaves).
    */
  private def scanCorrelation(space: Space): CorrelationScan =
    var repeated = false
    var relational = false
    var booleanNodes = 0
    var operationOpportunity = false

    def component(value: Space, atoms: mutable.HashSet[Space]): Unit =
      if booleanNodes <= maxBooleanNodes then value match
        case Space.Empty => ()
        case Space.Union(left, right) =>
          booleanNodes += 1
          relational = relational || structurallySubset(left, right) || structurallySubset(right, left) || structurallyDisjoint(left, right)
          component(left, atoms)
          component(right, atoms)
        case Space.Intersection(left, right) =>
          booleanNodes += 1
          relational = relational || structurallySubset(left, right) || structurallySubset(right, left) || structurallyDisjoint(left, right)
          component(left, atoms)
          component(right, atoms)
        case Space.Subtraction(left, right) =>
          booleanNodes += 1
          relational = relational || structurallySubset(left, right) || structurallyDisjoint(left, right)
          component(left, atoms)
          component(right, atoms)
        case other =>
          if atoms.contains(other) then repeated = true
          else
            // Pairwise operation relations are useful only while this
            // component can still fit in the cardinality solver.  Keeping the
            // comparison under maxAtoms preserves the linear fast path for
            // large unions of unrelated leaves.
            if atoms.size < maxAtoms then
              relational = relational || atoms.exists { existing =>
                structurallySubset(other, existing) ||
                structurallySubset(existing, other) ||
                structurallyDisjoint(other, existing)
              }
            atoms.add(other)
            nested(other)

    def fresh(value: Space): Unit = component(value, mutable.HashSet.empty)

    def nested(value: Space): Unit = value match
      case Space.Call(_, _, mentions) => mentions.foreach(fresh)
      case Space.Restriction(left, right) => fresh(left); fresh(right)
      case Space.Raffination(left, right) => fresh(left); fresh(right)
      case Space.Composition(left, right) => fresh(left); fresh(right)
      case Space.Iteration(src, _, _, templates) =>
        operationOpportunity = true
        fresh(src); fresh(templates)
      case Space.Fold(src, _, _, _, _, templates, _) => fresh(src); fresh(templates)
      case Space.Fixpoint(initial, _, step) => fresh(initial); fresh(step)
      case Space.Wrap(src, _) => fresh(src)
      case Space.Unwrap(src, _) =>
        operationOpportunity = true
        fresh(src)
      case Space.TailsUnion(src) =>
        operationOpportunity = true
        fresh(src)
      case Space.TailsIntersection(src) => fresh(src)
      case Space.PrefixClosure(src) =>
        operationOpportunity = true
        fresh(src)
      case Space.SuffixClosure(src) =>
        operationOpportunity = true
        fresh(src)
      case Space.TailsClosure(src) =>
        operationOpportunity = true
        fresh(src)
      case Space.GroundedSS(src, _) => fresh(src)
      case Space.Range(src, _, _) => fresh(src)
      case _ => ()

    fresh(space)
    CorrelationScan(repeated, relational, booleanNodes, operationOpportunity)

  private def encode(space: Space): Encoding =
    val atomIds = mutable.LinkedHashMap.empty[Space, Int]
    val counts = mutable.ArrayBuffer.empty[Int]
    def atom(value: Space): Z3SetFormula =
      val index = atomIds.getOrElseUpdate(value, {
        counts += 0
        atomIds.size
      })
      counts(index) += 1
      Z3SetFormula.Atom(index)
    def rec(value: Space): Z3SetFormula = value match
      case Space.Empty => Z3SetFormula.False
      case Space.Union(left, right) => Z3SetFormula.Or(rec(left), rec(right))
      case Space.Intersection(left, right) => Z3SetFormula.And(rec(left), rec(right))
      case Space.Subtraction(left, right) => Z3SetFormula.And(rec(left), Z3SetFormula.Not(rec(right)))
      case other => atom(other)
    val formula = rec(space)
    val atoms = atomIds.keys.toVector
    val atomRelations = (for
      left <- atoms.indices
      right <- atoms.indices
      if left < right
      relation <-
        if structurallyDisjoint(atoms(left), atoms(right)) then
          Vector(Z3AtomRelation.Disjoint(left, right))
        else
          Vector(
            Option.when(structurallySubset(atoms(left), atoms(right)))(Z3AtomRelation.Subset(left, right)),
            Option.when(structurallySubset(atoms(right), atoms(left)))(Z3AtomRelation.Subset(right, left))
          ).flatten
    yield relation).toVector
    Encoding(formula, atoms, counts.toVector, atomRelations)

  private def relations(left: Space, right: Space): Option[Z3BooleanRelations.Relations] =
    val structural = Z3BooleanRelations.Relations(
      structurallySubset(left, right),
      structurallySubset(right, left),
      structurallyDisjoint(left, right)
    )
    val atomIds = mutable.LinkedHashMap.empty[Space, Int]
    val leftAtoms = mutable.Set.empty[Int]
    val rightAtoms = mutable.Set.empty[Int]
    def rec(value: Space, side: mutable.Set[Int]): Z3SetFormula = value match
      case Space.Empty => Z3SetFormula.False
      case Space.Union(a, b) => Z3SetFormula.Or(rec(a, side), rec(b, side))
      case Space.Intersection(a, b) => Z3SetFormula.And(rec(a, side), rec(b, side))
      case Space.Subtraction(a, b) => Z3SetFormula.And(rec(a, side), Z3SetFormula.Not(rec(b, side)))
      case other =>
        val index = atomIds.getOrElseUpdate(other, atomIds.size)
        side += index
        Z3SetFormula.Atom(index)
    val l = rec(left, leftAtoms)
    val r = rec(right, rightAtoms)
    val boolean =
      if atomIds.size > maxAtoms then None
      else if leftAtoms.intersect(rightAtoms).isEmpty && left != Space.Empty && right != Space.Empty then None
      else Z3BooleanRelations.solve(l, r, atomIds.size)
    boolean match
      case Some(value) => Some(Z3BooleanRelations.Relations(
        structural.leftSubsetRight || value.leftSubsetRight,
        structural.rightSubsetLeft || value.rightSubsetLeft,
        structural.disjoint || value.disjoint
      ))
      case None if structural.leftSubsetRight || structural.rightSubsetLeft || structural.disjoint => Some(structural)
      case None => None

  private def normalizeBoolean(space: Space): Space =
    subs(space)(spost = {
      case node @ Space.Union(left, right) =>
        relations(left, right) match
          case Some(result) if result.leftSubsetRight => right
          case Some(result) if result.rightSubsetLeft => left
          case _ => node
      case node @ Space.Intersection(left, right) =>
        relations(left, right) match
          case Some(result) if result.disjoint => Space.Empty
          case Some(result) if result.leftSubsetRight => left
          case Some(result) if result.rightSubsetLeft => right
          case _ => node
      case node @ Space.Subtraction(left, right) =>
        relations(left, right) match
          case Some(result) if result.leftSubsetRight => Space.Empty
          case Some(result) if result.disjoint => left
          case _ => node
    })

  def estimate(
    space: Space,
    assumptions: Map[SpaceMention, ResultSizeEstimate] = Map.empty
  ): ResultSizeEstimate =
    val baseline = ResultSpaceSize.estimateBaseline(space, assumptions)
    val scan = scanCorrelation(space)
    val operationEstimate =
      if scan.operationOpportunity then ResultSpaceSize.estimateOperationLaws(space, assumptions)
      else baseline
    val withOperationLaws = strengthen(baseline, operationEstimate)
    if (!scan.repeated && !scan.relational) || scan.booleanNodes > maxBooleanNodes then return withOperationLaws
    val normalized = normalizeBoolean(space)
    val normalizedEstimate = ResultSpaceSize.estimateOperationLaws(normalized, assumptions)
    val encoding = encode(normalized)
    val hasCorrelation = encoding.occurrences.exists(_ > 1) || encoding.relations.nonEmpty
    val solverEstimate =
      if hasCorrelation && encoding.atoms.nonEmpty && encoding.atoms.size <= maxAtoms then
        val atomEstimates = encoding.atoms.map(ResultSpaceSize.estimateOperationLaws(_, assumptions))
        val problem = Z3CardinalityProblem(encoding.formula, atomEstimates, encoding.relations)
        ResultSizeEstimate(
          SizeExpr.Z3Cardinality(problem, Z3BoundDirection.Upper, normalizedEstimate.upper),
          SizeExpr.Z3Cardinality(problem, Z3BoundDirection.Lower, normalizedEstimate.lower)
        )
      else normalizedEstimate
    strengthen(withOperationLaws, solverEstimate)
