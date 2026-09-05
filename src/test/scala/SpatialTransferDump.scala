package morkl

import munit.FunSuite
import morkl.Space.*

/** THE CHECKER'S INPUT. Every exact-tier transfer of the correlated domain, over the whole small
 *  universe (paths over {a, b} of length ≤ 2, at most 3 per value), one row per (operation, inputs) with
 *  the abstract result the domain computed — and, for the pricing, one row per (operation, backend,
 *  inputs) with the counted component totals and the A4 interval.  `proofs/spatial/check_transfers.py`
 *  re-derives every concrete result INDEPENDENTLY (its own path-set algebra, its own range normalisation)
 *  and re-checks every containment, then writes `proofs/spatial/STATUS.tsv`.  The universe and the row
 *  order are deterministic, so two dumps are byte-identical. */
class SpatialTransferDump extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")
  val out = java.nio.file.Paths.get("proofs/spatial/out")

  def show(v: SpaceValue): String =
    if v.paths.isEmpty then "{}" else v.paths.toVector.map(_.items.mkString(".")).map(s => if s.isEmpty then "ε" else s).sorted.mkString("{", " ", "}")
  lazy val universe: Vector[SpaceValue] = SpatialGamma.universe(Vector("a", "b"), 2).filter(_.paths.size <= 3).sortBy(show)

  test("dump: the exact-tier transfers over the small universe") {
    java.nio.file.Files.createDirectories(out)
    val d = new Domain(DomainBudget())
    val sb = new StringBuilder
    sb ++= "# op\tlhs\trhs\tresult\n"
    def one(op: String, l: String, r: String, res: XNode): Unit =
      val v = d.enumerate(res).getOrElse(fail(s"$op: not enumerable")).map(show).sorted.mkString("|")
      sb ++= s"$op\t$l\t$r\t$v\n"
    for a <- universe; b <- universe do
      val (x, y) = (d.alpha(a), d.alpha(b))
      one("union", show(a), show(b), d.union(x, y))
      one("inter", show(a), show(b), d.inter(x, y))
      one("sub", show(a), show(b), d.sub(x, y))
      one("restrict", show(a), show(b), d.restrict(x, y))
      one("raff", show(a), show(b), d.raff(x, y))
      one("comp", show(a), show(b), d.comp(x, y))
    for a <- universe do
      val x = d.alpha(a)
      one("tails-union", show(a), "-", d.tailsUnion(x))
      one("tails-inter", show(a), "-", d.tailsInter(x))
      one("wrap", show(a), "w", d.wrap(List("w"), x))
      one("unwrap", show(a), "a", d.unwrap(x, List("a")))
      for (lo, hi) <- Vector((0, 0), (0, 1), (-1, 0), (1, 2), (2, 0), (0, -1), (-2, -1), (1, 3)) do
        one("range", show(a), s"$lo,$hi", d.range(x, lo, hi))
      // the alias short circuits: the same object on both sides
      one("union-same", show(a), show(a), d.unionA(Abs(x, Alias.Is(SpaceMention("m"))), Abs(x, Alias.Is(SpaceMention("m")))).node)
      one("inter-same", show(a), show(a), d.interA(Abs(x, Alias.Is(SpaceMention("m"))), Abs(x, Alias.Is(SpaceMention("m")))).node)
      one("sub-same", show(a), show(a), d.subA(Abs(x, Alias.Is(SpaceMention("m"))), Abs(x, Alias.Is(SpaceMention("m")))).node)
    java.nio.file.Files.writeString(out.resolve("transfers.tsv"), sb.result())
    println(s"A6: wrote ${sb.result().linesIterator.size - 1} transfer rows to proofs/spatial/out/transfers.tsv")
  }

  test("dump: the pricing's containment rows — counted component totals against the A4 intervals") {
    java.nio.file.Files.createDirectories(out)
    val sb = new StringBuilder
    sb ++= "# op\tbackend\tlhs\trhs\tcomponent\tcounted\tlo\thi\n"
    val s0 = SpaceMention("s0"); val s1 = SpaceMention("s1")
    val binops: Vector[(String, (Space, Space) => Space)] = Vector(
      "union" -> Union.apply, "inter" -> Intersection.apply, "sub" -> Subtraction.apply,
      "restrict" -> Restriction.apply, "raff" -> Raffination.apply, "comp" -> Composition.apply)
    val unops: Vector[(String, Space => Space)] = Vector(
      "tails-union" -> TailsUnion.apply, "tails-inter" -> TailsIntersection.apply,
      "wrap" -> (x => Wrap(x, Path.Constant(PathValue(List("w"))))), "unwrap" -> (x => Unwrap(x, Path.Constant(PathValue(List("a"))))),
      "range-first" -> (x => Range(x, 0, 1)), "range-last" -> (x => Range(x, -1, 0)), "range-full" -> (x => Range(x, 0, 0)))
    val sample = universe.zipWithIndex.collect { case (v, i) if i % 4 == 0 => v }   // 16 of 64 values for the binary rows
    def rows(op: String, prog: Space, spaces: Map[SpaceMention, SpaceValue], l: String, r: String): Unit =
      val pc = PathContextMap(Map.empty); val sc = SpaceContextMap(spaces)
      val ic = spaces.view.mapValues(ITrie.fromSpaceValue).toMap
      given PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
      eval(prog)(using pc, sc); val re = EffortSink.events(eval(prog)(using pc, sc))
      evalI(prog)(using pc, ic); val te = EffortSink.events(evalI(prog)(using pc, ic))
      execZ(prog)(using pc, ic); val ze = EffortSink.events(execZ(prog)(using pc, ic))
      val inputs = CostSem.Inputs(values = spaces)
      for (b, ev) <- Vector(Backend.Reference -> re, Backend.Trie -> te, Backend.Zipper -> ze) do
        val rep = CostSem.analyze(prog, inputs, b)
        for c <- EffortEvent.calibratedComponents do
          val i = rep.component(c)
          sb ++= s"$op\t${b.slug}\t$l\t$r\t$c\t${ev.component(c)}\t${i.lo}\t${if i.hi >= Ivl.INF then "inf" else i.hi}\n"
    for (name, op) <- binops; a <- sample; b <- sample do
      rows(name, op(Mention(s0), Mention(s1)), Map(s0 -> a, s1 -> b), show(a), show(b))
    for (name, op) <- unops; a <- universe do
      rows(name, op(Mention(s0)), Map(s0 -> a), show(a), "-")
    java.nio.file.Files.writeString(out.resolve("bounds.tsv"), sb.result())
    println(s"A6: wrote ${sb.result().linesIterator.size - 1} containment rows to proofs/spatial/out/bounds.tsv")
  }
end SpatialTransferDump
