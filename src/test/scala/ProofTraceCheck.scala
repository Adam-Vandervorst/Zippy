package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions
import morkl.Space.*

/** Typed proof traces replay, and every mutation of a matcher, a side condition, an
 *  endpoint term or a dependency makes the replay FAIL. */
class ProofTraceCheck extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(10, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def lit(ps: PathValue*): Space = Literal(SpaceValue(ps.toSet))

  /** a recursive routine the supercompiler drives, folds and (with a growing argument) generalizes */
  val m = SpaceMention("m")
  val suf = Routine(RoutinePtr("suf"), Vector.empty, Vector(m), Union(Mention(m), Call(RoutinePtr("suf"), Vector.empty, Vector(TailsUnion(Mention(m))))))
  val defs: PartialFunction[RoutinePtr, Routine] = Map(suf.name -> suf)
  // the argument carries a law instance (two literals unioned: `literal-space-ops` folds them) so the
  // top trace has a LawInstance node beside the unfold/fold/generalization nodes
  val conf: Space = Call(suf.name, Vector.empty, Vector(Union(Union(lit(p("a", "b")), lit(p("c"))), Mention(SpaceMention("x")))))

  def run(): (SC.State, Residual) =
    val (res, st, _) = SC.run(conf, defs, SC.Config(trace = true))
    (st, res)

  test("REPLAY: every residual node's trace and the top trace check, and end at the body") {
    val (st, res) = run()
    assert(st.traces.nonEmpty, "the run created residual nodes")
    for (g, tid) <- st.traces do
      val dag = st.traceBuilder.dag(tid)
      val bad = ProofTrace.Checker.check(dag, defs, st.nodeTable)
      assert(bad.isEmpty, s"${g.s}:\n  ${bad.mkString("\n  ")}\n${dag.render.take(3000)}")
      assertEquals(dag.dst, res.routines(g).body, s"${g.s}: the trace ends at the residual body")
      assert(dag.leaves.exists(_.kind == "Unfold"), s"${g.s}: the trace starts with the node's one unfold")
      println(s"TRACE ${g.s}: ${dag.size} nodes, kinds ${dag.nodes.map(_.kind).groupBy(identity).view.mapValues(_.size).toMap}")
    val top = st.topTraceDag.get
    val badTop = ProofTrace.Checker.check(top, defs, st.nodeTable)
    assert(badTop.isEmpty, s"top:\n  ${badTop.mkString("\n  ")}")
    assertEquals(top.src, conf); assertEquals(top.dst, res.top)
    println(top.render.linesIterator.take(20).mkString("\n"))
  }

  test("RENDERING is deterministic and round-trips its node count") {
    val (st1, _) = run(); val (st2, _) = run()
    val a = st1.topTraceDag.get.render; val b = st2.topTraceDag.get.render
    assertEquals(a, b, "two runs render the same trace")
    assert(a.linesIterator.count(_.startsWith("T\t")) >= 2, "the term table is present")
  }

  test("MUTATIONS: a changed matcher, side condition, endpoint or dependency fails the replay") {
    val (st, _) = run()
    // every DAG of the run: the top trace and each node's trace; a mutation is applied to the first DAG
    // that has a node of the mutated kind
    val dags: Vector[ProofTrace.Dag] = st.topTraceDag.toVector ++ st.traces.values.toVector.map(st.traceBuilder.dag)
    val dag = dags.head
    def mutate(f: PartialFunction[(ProofTrace.Node, Int), ProofTrace.Node]): Option[ProofTrace.Dag] =
      dags.iterator.flatMap { d =>
        var done = false
        val nodes = d.nodes.zipWithIndex.map { case (n, i) => if !done && f.isDefinedAt((n, i)) then { done = true; f((n, i)) } else n }
        if done then Some(ProofTrace.Dag(nodes, d.root)) else None
      }.nextOption()
    val junk = lit(p("mutation"))
    val mutations0: Vector[(String, Option[ProofTrace.Dag])] = Vector(
      "law instance: wrong law name" -> mutate { case (ProofTrace.Node.LawInstance(_, b, a, ch, gs), _) => ProofTrace.Node.LawInstance("iter-tails", b, a, ch, gs) },
      "law instance: forged matcher position" -> mutate { case (ProofTrace.Node.LawInstance(l, b, a, ch, gs), _) if ch.nonEmpty => ProofTrace.Node.LawInstance(l, b, a, ch.map((p, x, y) => (p, junk, y)), gs) },
      "law instance: changed after-term" -> mutate { case (ProofTrace.Node.LawInstance(l, b, _, ch, gs), _) => ProofTrace.Node.LawInstance(l, b, junk, ch, gs) },
      "unfold: wrong body" -> mutate { case (ProofTrace.Node.Unfold(r, c, _, ms, ps, res), _) => ProofTrace.Node.Unfold(r, c, junk, ms, ps, res) },
      "unfold: changed argument substitution" -> mutate { case (ProofTrace.Node.Unfold(r, c, b, ms, ps, res), _) if ms.nonEmpty => ProofTrace.Node.Unfold(r, c, b, ms.map((n, _) => (n, junk)), ps, res) },
      "fold: forged theta" -> mutate { case (ProofTrace.Node.Fold(n, c, tm, tp, i, call), _) if tm.nonEmpty => ProofTrace.Node.Fold(n, c, tm.map((k, _) => (k, junk)), tp, i, call) },
      "fold: wrong node" -> mutate { case (ProofTrace.Node.Fold(_, c, tm, tp, i, call), _) => ProofTrace.Node.Fold(RoutinePtr("nobody"), c, tm, tp, i, call) },
      "positional: dependency swapped" -> mutate { case (ProofTrace.Node.Positional(b, pos, a, by), i) if i > 1 && by != 0 => ProofTrace.Node.Positional(b, pos, a, 0) },
      "compose: endpoint changed" -> mutate { case (ProofTrace.Node.Compose(s, b, _), _) => ProofTrace.Node.Compose(s, b, junk) },
      "generalization: forged theta" -> mutate { case (ProofTrace.Node.Generalization(sk, tm, tp, i, r, st, h, res), _) if tm.nonEmpty => ProofTrace.Node.Generalization(sk, tm.map((k, _) => (k, junk)), tp, i, r, st, h, res) })
    val missing = mutations0.collect { case (l, None) => l }
    println(s"MUTATIONS without a matching node in this run: ${missing.mkString(", ")}")
    val mutations = mutations0.collect { case (l, Some(d)) => (l, d) }
    assert(mutations.exists(_._1.startsWith("law instance")), "the fixture must exercise a law instance")
    var applied = 0
    for (label, mutated) <- mutations do
      val bad = ProofTrace.Checker.check(mutated, defs, st.nodeTable)
      assert(bad.nonEmpty, s"$label: the checker accepted a mutated trace")
      applied += 1
      println(s"MUTATION $label -> ${bad.head}")
    assert(applied >= 6)
    // a forward reference is not a DAG
    val cyc = ProofTrace.Dag(dag.nodes.updated(0, ProofTrace.Node.Compose(Vector(dag.nodes.length - 1), dag.nodes(0).src, dag.nodes(0).dst)), dag.root)
    assert(ProofTrace.Checker.check(cyc, defs, st.nodeTable).exists(_.contains("not earlier")))
    // an identity claim needs both halves
    val idOnly = ProofTrace.Dag(Vector(ProofTrace.Node.AlphaEquivalence(conf, conf)), 0)
    assert(ProofTrace.Checker.check(idOnly, defs).exists(_.contains("identity claim")), "an alpha-equivalence alone is not an identity certificate")
    val idFull = ProofTrace.Dag(Vector(ProofTrace.Node.AlphaEquivalence(lit(p("a")), lit(p("a"))), ProofTrace.Node.OptimizerNoOp(lit(p("a"))),
                                       ProofTrace.Node.Compose(Vector(0, 1), lit(p("a")), lit(p("a")))), 2)
    assertEquals(ProofTrace.Checker.check(idFull, defs), Vector.empty[String])
    // a marker artifact is not a backend obligation
    val marker = new java.io.File(RunEnvironment.repoRoot, "target/artifact-scratch/marker-only.smt2"); marker.getParentFile.mkdirs()
    java.nio.file.Files.writeString(marker.toPath, "; TRUSTS: -\n; TRIVIAL-NO-OBLIGATION: nothing here\n")
    val mk = ProofTrace.Dag(Vector(ProofTrace.Node.BackendRefinement("graph", "graph", "target/artifact-scratch/marker-only.smt2", "x", lit(p("a")), lit(p("b")))), 0)
    assert(ProofTrace.Checker.check(mk, defs).exists(_.contains("marker")), "a marker is rejected as an obligation")
  }
end ProofTraceCheck
