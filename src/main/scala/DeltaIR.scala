package morkl

import scala.collection.mutable

/** ==================================================================================================
 *  THE STRATIFIED DELTA-FIXPOINT IR (tasks.md A2).
 *
 *  ONE explicit recursive representation, shared by execution, analysis, proof and residual
 *  generation, for every certified `Fixpoint` and every recursive `Call` component:
 *
 *    1. [[Variance]] — the signed dependency of a term on a mention: `+` (monotone), `-` (antitone),
 *       `0` (unknown / non-monotone), `·` (absent), by COMPOSITIONAL variance analysis of the actual
 *       constructors ([[Variance.of]]), with routine PARAMETER variances solved as a least fixpoint over
 *       the routine table ([[Variance.routineTable]]).  Positive-or-absent is the fragment
 *       `Positive.lean`'s `posB` accepts; the Lean twin of the four-valued analysis is `Delta.lean`'s
 *       `varB`, and `varB_sound` is the theorem that `+` really is monotone and `-` really antitone.
 *    2. [[DepGraph]] — the dependency graph over the bound space mentions (one node per flattenable
 *       `Fixpoint` binder), the routines, and the frozen inputs, every edge labelled by its variance,
 *       collapsed into SCCs and STRATIFIED: a recursive SCC is CERTIFIED only when every edge internal
 *       to it is `+`; a `-` or `0` edge is admitted only when it points to a completed lower stratum,
 *       which is what the SCC condensation being a DAG gives by construction; a cycle through a `-`
 *       or `0` edge is REJECTED ([[Verdict.Rejected]]).  A recursive `Call` SCC whose calls do not pass
 *       the parameters through is a different failure — not representable as a finite system — and is
 *       reported as [[Verdict.Unsupported]], never confused with a negative cycle.
 *    3. [[EqSystem]] — a positive SCC as a SIMULTANEOUS least-post-fixpoint system
 *       `X_i = init_i ∪ body_i(X̄; frozen)`; unary `Space.Fixpoint` is the one-equation case, and a
 *       recursive `Call` SCC with passthrough arguments lowers to the same equations (the identity-base
 *       self-recursion `r(m) = m ∪ r(next(m))` lowers, via `asFixpoint`, to exactly the equation the
 *       explicit `Fixpoint(m, m, next(m))` does — `DeltaIRCheck` holds the two alpha-equal).  Lower-
 *       stratum values are FROZEN parameters of the system.
 *    4. [[Exec]] — the IR's explicit state: accumulator, current delta, round, routine environment,
 *       backend SCHEDULE ([[Schedule.Naive]] / [[Schedule.Delta]]), provenance (the round that
 *       introduced each element) and the counted events of each round.  The reference recurrence is
 *       `A(0) = init`, `new(n+1) = F(A(n)) \ A(n)`, `A(n+1) = A(n) ∪ new(n+1)`; the delta schedule
 *       computes `new(n+1)` as `deltaStep(F, A(n), lastDelta) \ A(n)` through the compositional
 *       DIFFERENTIAL TRANSFER [[Delta.dden]], and the step equation
 *       `A ∪ deltaStep(F, A, lastDelta) = A ∪ F(A)` (Delta.lean `delta_step_eq`) is what makes the two
 *       schedules agree at EVERY round boundary — which [[Exec.run]] can re-check at run time
 *       (`verify = true`) and `DeltaIRCheck` does on every fixture.
 *    5. [[Premises]] — every accepted instance carries, as data, the variance labels and the strata it
 *       was accepted on and the Lean theorems the acceptance rests on; [[Premises.replay]] recomputes
 *       the labels from the term so the premise is checked, not remembered.
 *
 *  ==THE DIFFERENTIAL TRANSFER, RULE BY RULE (Delta.lean `dden`)==
 *  For environments `old ≤ new` on the changing variables (`new(X) = old(X) ∪ Δ(X)`), `dden s`
 *  satisfies (D1) `⟦s⟧new ⊆ ⟦s⟧old ∪ dden s` and (D2) `dden s ⊆ ⟦s⟧new`:
 *
 *    Mention X          Δ(X) if X changes, ∅ otherwise
 *    a ∪ b              dden a ∪ dden b
 *    a ∩ b              (dden a ∩ ⟦b⟧new) ∪ (⟦a⟧new ∩ dden b)        — every term with ≥1 changed argument
 *    a · b              (dden a · ⟦b⟧new) ∪ (⟦a⟧new · dden b)          — the delta is NOT substituted for
 *    a <| b             (dden a <| ⟦b⟧new) ∪ (⟦a⟧new <| dden b)          every occurrence; nonlinear bodies
 *    a ∖ b, a ∖| b      dden a ∖ ⟦b⟧, dden a ∖| ⟦b⟧   (b frozen: `-` position)   enumerate the mixed terms
 *    wrap/unwrap/tails  the operation applied to dden of the operand (image-like: distributes)
 *    iteration          old heads: dden of the body under (rest := old tails, new tails); NEW heads: the
 *                       whole body at the new environment
 *    nested fixpoint    (under a binder, not flattened) the whole new value — sound, not incremental
 *    call               frozen callee: the whole new value when an argument changes
 *    frozen subterm     ∅
 *
 *  `Delta.lean` proves D1/D2 for each rule and `delta_step_eq` from them; `Strata.lean` proves the
 *  tagged-product form of the simultaneous system, its componentwise least solution, and the unary
 *  correspondence.  `terminating/REGISTRY.tsv` rows A2-VAR / A2-STRAT / A2-DELTA cite them.
 *  ================================================================================================== */

enum Variance:
  case Absent, Pos, Neg, Zero
  def flip: Variance = this match { case Pos => Neg; case Neg => Pos; case v => v }
  /** both occurrences at once: `+ ⊔ - = 0`, absent is the identity, unknown absorbs */
  def join(o: Variance): Variance = (this, o) match
    case (Absent, v) => v
    case (v, Absent) => v
    case (Zero, _) | (_, Zero) => Zero
    case (Pos, Pos) => Pos
    case (Neg, Neg) => Neg
    case _ => Zero
  def monotone: Boolean = this == Absent || this == Pos
  def antitone: Boolean = this == Absent || this == Neg
  def occurs: Boolean = this != Absent
  def show: String = this match { case Absent => "·"; case Pos => "+"; case Neg => "-"; case Zero => "0" }

object Variance:
  /** the variance of an argument seen through a position of polarity `pol` */
  def compose(pol: Variance, inner: Variance): Variance = (pol, inner) match
    case (_, Absent) => Absent
    case (Absent, _) => Absent
    case (Pos, v) => v
    case (Neg, v) => v.flip
    case (Zero, _) => Zero

  /** a routine's parameter variances: one per mention parameter.  Unknown routine ⇒ `0` everywhere. */
  type RoutineTable = RoutinePtr => Option[Vector[Variance]]
  val noRoutines: RoutineTable = _ => None

  private def occursInPath(p: Path, m: SpaceMention): Boolean = p match
    case Path.Deref(_) | Path.Constant(_) => false
    case Path.Concat(l, r) => occursInPath(l, m) || occursInPath(r, m)
    case Path.GroundedPP(q, _) => occursInPath(q, m)
    case Path.GroundedSP(s, _) => Matching.freeMentions(s).contains(m)
  private def pathVar(p: Path, m: SpaceMention): Variance = if occursInPath(p, m) then Zero else Absent
  private def opaque(s: Space, m: SpaceMention): Variance = if Matching.freeMentions(s).contains(m) then Zero else Absent

  // obligation: terminating/REGISTRY.tsv A2-VAR (MECHANIZED: proofs/lean/Zippy/Delta.lean#Zippy.Space.varB_sound —
  // `+` is monotone, `-` antitone, `·` constant; the Lean `varB` is this function arm for arm)
  /** THE COMPOSITIONAL VARIANCE ANALYSIS.  Every arm is the variance table of one constructor; the
   *  binder arms shadow; `Iteration`'s source and `Fixpoint`'s operands are positive positions ONLY
   *  when the body is monotone in the variable the binder introduces (the two refuted arms of
   *  `mono_soundness.smt2`, O3d-X1/X2, and `posB`'s fixpoint arm). */
  def of(s: Space, m: SpaceMention, rt: RoutineTable = noRoutines): Variance =
    import Space.*
    def go(x: Space): Variance = x match
      case Empty | Literal(_) => Absent
      case Singleton(p) => pathVar(p, m)
      case Mention(v) => if v == m then Pos else Absent
      case Union(a, b) => go(a) join go(b)
      case Intersection(a, b) => go(a) join go(b)
      case Composition(a, b) => go(a) join go(b)
      case Restriction(a, b) => go(a) join go(b)
      case Subtraction(a, b) => go(a) join go(b).flip
      case Raffination(a, b) => go(a) join go(b).flip
      case Wrap(src, p) => go(src) join pathVar(p, m)
      case Unwrap(src, p) => go(src) join pathVar(p, m)
      case TailsUnion(src) => go(src)
      case TailsIntersection(src) => compose(Zero, go(src))
      case Range(y, _, _) => compose(Zero, go(y))
      case Iteration(src, _, rest, body) =>
        val vBody = if rest == m then Absent else of(body, m, rt)
        val pol = if of(body, rest, rt).monotone then Pos else Zero
        compose(pol, go(src)) join vBody
      case Fixpoint(init, rec, body) =>
        val vBody = if rec == m then Absent else of(body, m, rt)
        val pol = if of(body, rec, rt).monotone then Pos else Zero
        compose(pol, go(init) join vBody)
      case Fold(_, _, _, _, _, _, _) => opaque(x, m)
      case Call(r, refs, ms) =>
        val viaRefs = refs.foldLeft(Absent: Variance)((v, p) => v join pathVar(p, m))
        rt(r) match
          case Some(params) if params.length == ms.length =>
            ms.indices.foldLeft(viaRefs)((v, i) => v join compose(params(i), go(ms(i))))
          case _ => ms.foldLeft(viaRefs)((v, a) => v join compose(Zero, go(a)))
      case GroundedPS(p, _) => pathVar(p, m)
      case GroundedSS(y, _) => compose(Zero, go(y))
    go(s)

  /** THE PARAMETER VARIANCES OF EVERY ROUTINE, as the least fixpoint over the finite lattice
   *  (`Absent < Pos, Neg < Zero`): start every parameter at `·`, re-derive each routine's body under
   *  the current table, stop when nothing moves.  Monotone, hence it terminates. */
  def routineTable(rc: PartialFunction[RoutinePtr, Routine], roots: Iterable[RoutinePtr]): Map[RoutinePtr, Vector[Variance]] =
    val reach = mutable.LinkedHashMap.empty[RoutinePtr, Routine]
    def gather(r: RoutinePtr): Unit =
      if rc.isDefinedAt(r) && !reach.contains(r) then
        val d = rc(r); reach(r) = d
        callees(d.body).foreach(gather)
    roots.foreach(gather)
    var table: Map[RoutinePtr, Vector[Variance]] = reach.view.mapValues(r => r.mentions.map(_ => Absent)).toMap
    var changed = true
    var rounds = 0
    while changed && rounds < 64 do
      changed = false; rounds += 1
      val rt: RoutineTable = r => table.get(r)
      for (r, d) <- reach do
        val next = d.mentions.map(m => table(r)(d.mentions.indexOf(m)) join of(d.body, m, rt))
        if next != table(r) then { table = table.updated(r, next); changed = true }
    table

// ==================================================================================================
// THE DEPENDENCY GRAPH, ITS SCCs, THE STRATA
// ==================================================================================================

/** a node of the dependency graph */
enum DepNode:
  /** a `Fixpoint` binder at the top level of the term (flattened into the system) */
  case Fix(v: SpaceMention)
  /** a routine of the table */
  case Rout(r: RoutinePtr)
  /** a free mention of the term: a frozen input */
  case Input(m: SpaceMention)
  def show: String = this match
    case Fix(v) => s"fix ${v.s}"
    case Rout(r) => s"routine ${r.s}"
    case Input(m) => s"input ${m.s}"

final case class DepEdge(from: DepNode, to: DepNode, variance: Variance):
  def show: String = s"${from.show} --${variance.show}--> ${to.show}"

// obligation: terminating/REGISTRY.tsv A2-STRAT (MECHANIZED: proofs/lean/Zippy/Strata.lean — a positive SCC is a
// simultaneous least-post-fixpoint system; a `-`/`0` edge to a lower stratum is a frozen constant)
/** one strongly connected component with its stratum index (0 = lowest: depends on nothing recursive) */
final case class Scc(index: Int, nodes: Vector[DepNode], recursive: Boolean, internal: Vector[DepEdge]):
  def certified: Boolean = !recursive || internal.forall(_.variance == Variance.Pos)
  def offending: Vector[DepEdge] = internal.filterNot(_.variance == Variance.Pos)
  def show: String =
    s"stratum $index: {${nodes.map(_.show).mkString(", ")}}" +
      (if recursive then s" recursive, ${if certified then "CERTIFIED (all internal edges +)" else s"REJECTED: ${offending.map(_.show).mkString("; ")}"}" else "")

final case class DepGraph(nodes: Vector[DepNode], edges: Vector[DepEdge], sccs: Vector[Scc]):
  def stratumOf(n: DepNode): Int = sccs.find(_.nodes.contains(n)).map(_.index).getOrElse(-1)
  def show: String = sccs.map(_.show).mkString("\n")

object DepGraph:
  /** Tarjan's SCCs in dependency order (a component comes after every component it depends on), then
   *  the stratum index is the component's position in that order. */
  def build(nodes: Vector[DepNode], edges: Vector[DepEdge]): DepGraph =
    val idx = mutable.HashMap.empty[DepNode, Int]
    val low = mutable.HashMap.empty[DepNode, Int]
    val onStack = mutable.HashSet.empty[DepNode]
    val stack = mutable.Stack.empty[DepNode]
    val comps = mutable.ArrayBuffer.empty[Vector[DepNode]]
    var counter = 0
    val succ: Map[DepNode, Vector[DepNode]] = edges.groupBy(_.from).view.mapValues(_.map(_.to)).toMap
    def strong(v: DepNode): Unit =
      idx(v) = counter; low(v) = counter; counter += 1
      stack.push(v); onStack += v
      for w <- succ.getOrElse(v, Vector.empty).distinct do
        if !idx.contains(w) then { strong(w); low(v) = low(v) min low(w) }
        else if onStack(w) then low(v) = low(v) min idx(w)
      if low(v) == idx(v) then
        val comp = mutable.ArrayBuffer.empty[DepNode]
        var w: DepNode = null
        while { w = stack.pop(); onStack -= w; comp += w; w != v } do ()
        comps += comp.toVector
    nodes.foreach(v => if !idx.contains(v) then strong(v))
    // Tarjan emits components in REVERSE topological order of the condensation: the first component
    // emitted depends on no later one, which is exactly stratum order
    val sccs = comps.zipWithIndex.map { (comp, i) =>
      val set = comp.toSet
      val internal = edges.filter(e => set(e.from) && set(e.to))
      val recursive = comp.length > 1 || internal.nonEmpty
      Scc(i, comp, recursive, internal)
    }.toVector
    DepGraph(nodes, edges, sccs)

// ==================================================================================================
// THE SYSTEM
// ==================================================================================================

/** one equation `v = init ∪ body(...)` of a simultaneous least-post-fixpoint system */
final case class Equation(v: SpaceMention, init: Space, body: Space):
  def show: String = s"${v.s} = ${init.show.replace('\n', ' ')} ∪ ${body.show.replace('\n', ' ')}"

/** A positive SCC as a simultaneous system.  `frozen` are the free mentions of the equations that are
 *  not system variables: lower-stratum values and inputs, bound by the environment the system is
 *  solved in and never changed by it.  `routines` names the SCC routines an equation stands for, so a
 *  `Call` to one of them is answered by the system's projection on that variable. */
final case class EqSystem(stratum: Int, eqs: Vector[Equation], frozen: Set[SpaceMention],
                        routines: Map[RoutinePtr, SpaceMention] = Map.empty):
  def vars: Vector[SpaceMention] = eqs.map(_.v)
  def show: String = s"system@$stratum {${eqs.map(_.show).mkString("; ")}} frozen=${frozen.map(_.s).mkString(",")}"
  /** alpha-normal form of the equations, for the "same IR" comparison across lowerings */
  def canonical: Vector[(Space, Space)] =
    val renaming = vars.zipWithIndex.map((v, i) => v -> Space.Mention(SpaceMention(s"#sys#$i"))).toMap
    eqs.map(e => (Matching.canon(Subst.apply(e.init, renaming)), Matching.canon(Subst.apply(e.body, renaming))))

/** why a term did or did not lower */
enum Verdict:
  /** every recursive component is positive; the systems are the IR */
  case Accepted(program: Lowered)
  /** a cycle through a `-` or `0` edge: outside the certified language */
  case Rejected(graph: DepGraph, offending: Vector[DepEdge])
  /** a recursive `Call` SCC whose calls change their arguments: not a finite system */
  case Unsupported(graph: DepGraph, why: String)
  def show: String = this match
    case Accepted(p) => s"ACCEPTED\n${p.show}"
    case Rejected(g, off) => s"REJECTED — negative/unknown cycle: ${off.map(_.show).mkString("; ")}\n${g.show}"
    case Unsupported(g, why) => s"UNSUPPORTED — $why\n${g.show}"

/** THE PREMISES an accepted instance carries: the labels it was accepted on and the theorems that
 *  make acceptance mean something.  `replay` recomputes the labels from the term. */
final case class Premises(variances: Vector[DepEdge], strata: Vector[Scc], theorems: Vector[String]):
  def replay(recompute: => Vector[DepEdge]): Boolean =
    val again = recompute
    again.toSet == variances.toSet && strata.forall(_.certified)
  def show: String =
    s"premises: ${variances.length} labelled edges, ${strata.count(_.recursive)} recursive strata; " +
      s"rests on ${theorems.mkString(", ")}"

object Premises:
  val theorems: Vector[String] = Vector(
    "proofs/lean/Zippy/Delta.lean#Zippy.Space.varB_sound",
    "proofs/lean/Zippy/Strata.lean#Zippy.Sim.Sys.tagged_lfp",
    "proofs/lean/Zippy/Strata.lean#Zippy.Sim.unary_eq",
    "proofs/lean/Zippy/Strata.lean#Zippy.Sim.stratum_frozen_sound",
    "proofs/lean/Zippy/Delta.lean#Zippy.Delta.delta_step_eq",
    "proofs/lean/Zippy/Delta.lean#Zippy.Delta.delta_iteration_eq_naive")

/** the lowered program: the term with its top-level fixpoints replaced by system variables, the
 *  systems (in stratum order), the routine table, the graph and the premises */
final case class Lowered(term: Space, systems: Vector[EqSystem], routines: PartialFunction[RoutinePtr, Routine],
                         graph: DepGraph, premises: Premises):
  def systemOfVar(v: SpaceMention): Option[EqSystem] = systems.find(_.vars.contains(v))
  /** THE ALPHA-NORMAL FORM OF THE WHOLE PROGRAM: every system variable renamed by its position, the
   *  term and every equation canonicalised under that one renaming — what "the same IR" means when two
   *  lowerings are compared (`DeltaIRCheck`) */
  def canonical: (Space, Vector[Vector[(Space, Space)]]) =
    val renaming = systems.flatMap(_.vars).zipWithIndex.map((v, i) => v -> Space.Mention(SpaceMention(s"#sys#$i"))).toMap
    (Matching.canon(Subst.apply(term, renaming)),
     systems.map(_.eqs.map(e => (Matching.canon(Subst.apply(e.init, renaming)), Matching.canon(Subst.apply(e.body, renaming))))))
  def systemOfRoutine(r: RoutinePtr): Option[EqSystem] = systems.find(_.routines.contains(r))
  def show: String =
    s"term: ${term.show.replace('\n', ' ')}\n" + systems.map("  " + _.show).mkString("\n") + s"\n${graph.show}\n${premises.show}"

// ==================================================================================================
// THE LOWERING
// ==================================================================================================

object DeltaIR:
  import Space.*

  /** the top-level `Fixpoint` binders of a term — those not under an `Iteration`/`Fold` binder (whose
   *  bound head or tail set they could read) — renamed to unique variables and replaced by them.
   *  Returns the term and the equations, outermost first.  The variable names are a function of the
   *  term (numbered in traversal order), so two lowerings of one term produce one IR — which is what
   *  makes `Premises.replay` a comparison rather than a coincidence. */
  private def flatten(s: Space): (Space, Vector[Equation]) =
    val eqs = mutable.ArrayBuffer.empty[Equation]
    var fresh = 0
    def freshVar(): SpaceMention = { fresh += 1; SpaceMention(s"#fix#$fresh") }
    def go(x: Space, underBinder: Boolean): Space = x match
      case Fixpoint(init, rec, body) if !underBinder =>
        val v = freshVar()
        val init2 = go(init, false)
        val body2 = go(Subst.mention(body, rec, Mention(v)), false)
        eqs += Equation(v, init2, body2)
        Mention(v)
      case Union(a, b) => Union(go(a, underBinder), go(b, underBinder))
      case Intersection(a, b) => Intersection(go(a, underBinder), go(b, underBinder))
      case Subtraction(a, b) => Subtraction(go(a, underBinder), go(b, underBinder))
      case Restriction(a, b) => Restriction(go(a, underBinder), go(b, underBinder))
      case Raffination(a, b) => Raffination(go(a, underBinder), go(b, underBinder))
      case Composition(a, b) => Composition(go(a, underBinder), go(b, underBinder))
      case Wrap(src, p) => Wrap(go(src, underBinder), p)
      case Unwrap(src, p) => Unwrap(go(src, underBinder), p)
      case TailsUnion(src) => TailsUnion(go(src, underBinder))
      case TailsIntersection(src) => TailsIntersection(go(src, underBinder))
      case Range(y, lo, hi) => Range(go(y, underBinder), lo, hi)
      case Iteration(src, sym, rest, body) => Iteration(go(src, underBinder), sym, rest, go(body, true))
      case Fold(src, i, a, sym, rest, body, u) => Fold(go(src, underBinder), i, a, sym, rest, go(body, true), u)
      case Fixpoint(init, rec, body) => Fixpoint(go(init, true), rec, go(body, true))
      case Call(r, refs, ms) => Call(r, refs, ms.map(go(_, underBinder)))
      case other => other
    val t = go(s, false)
    (t, eqs.toVector)

  /** LOWER a term over a routine table to the IR.  See the file header for the three verdicts. */
  def lower(term: Space, rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Verdict =
    // ---- the routines reachable from the term, with the identity-base self-recursion pre-lowered
    //      (asFixpoint: `r(m) = m ∪ r(next(m))` IS the equation `m' = m ∪ next(m')`), and every
    //      ACYCLIC routine inlined into the term and into the recursive bodies, exactly as
    //      `lowerCalls` does — so a recursion written as a routine and one written as a `Fixpoint`
    //      reach the same equations ----
    val reach0 = mutable.LinkedHashMap.empty[RoutinePtr, Routine]
    def gather(r: RoutinePtr): Unit =
      if rc.isDefinedAt(r) && !reach0.contains(r) then
        val d = asFixpoint(rc(r)).getOrElse(rc(r)); reach0(r) = d
        callees(d.body).foreach(gather)
    callees(term).foreach(gather)
    def cyclic(m: Map[RoutinePtr, Routine]): Set[RoutinePtr] =
      val es = m.view.mapValues(r => callees(r.body).filter(m.contains)).toMap
      def reaches(start: RoutinePtr): Set[RoutinePtr] =
        val out = mutable.Set.empty[RoutinePtr]; val st = mutable.Stack.from(es(start))
        while st.nonEmpty do { val x = st.pop(); if out.add(x) then es(x).foreach(st.push) }
        out.toSet
      m.keySet.filter(r => reaches(r).contains(r))
    val recursiveRs = cyclic(reach0.toMap)
    val acyclic: PartialFunction[RoutinePtr, Routine] = { case r if reach0.contains(r) && !recursiveRs(r) => reach0(r) }
    val inlinedTerm = inlineCalls(term, acyclic)
    val reach = mutable.LinkedHashMap.from(reach0.iterator.filter((r, _) => recursiveRs(r)).map((r, d) => r -> d.copy(body = inlineCalls(d.body, acyclic))))
    val (flat, fixEqs) = flatten(inlinedTerm)
    val fixVars = fixEqs.map(_.v).toSet
    val rcLowered: PartialFunction[RoutinePtr, Routine] = { case r if reach.contains(r) => reach(r) }
    val paramVar = Variance.routineTable(rcLowered, reach.keys)
    val rt: Variance.RoutineTable = r => paramVar.get(r)
    // ---- nodes ----
    val inputs = (Matching.freeMentions(flat) ++ fixEqs.flatMap(e => Matching.freeMentions(e.init) ++ Matching.freeMentions(e.body)))
      .filterNot(fixVars).toVector.sortBy(_.s)
    val nodes: Vector[DepNode] = fixEqs.map(e => DepNode.Fix(e.v)) ++ reach.keys.map(DepNode.Rout(_)).toVector ++ inputs.map(DepNode.Input(_))
    // ---- edges: every reference from an equation's init/body, labelled ----
    val edges = mutable.ArrayBuffer.empty[DepEdge]
    def refsOf(from: DepNode, body: Space): Unit =
      for m <- Matching.freeMentions(body).toVector.sortBy(_.s) do
        val v = Variance.of(body, m, rt)
        if v.occurs then edges += DepEdge(from, if fixVars(m) then DepNode.Fix(m) else DepNode.Input(m), v)
      for r <- callees(body).toVector.sortBy(_.s) if reach.contains(r) do
        // the variance of a routine's value in the CALL: positive when every call to it sits in a
        // positive position — decided by the call-positivity discipline (SC.callPositive's arms)
        edges += DepEdge(from, DepNode.Rout(r), callVariance(body, r, rt))
    for e <- fixEqs do
      refsOf(DepNode.Fix(e.v), Union(e.init, e.body))
    for (r, d) <- reach do
      // a routine's own parameters are its frozen inputs: not graph edges (they are bound per call);
      // its body's free mentions that are not parameters would be unbound — ignored here
      for c <- callees(d.body).toVector.sortBy(_.s) if reach.contains(c) do
        edges += DepEdge(DepNode.Rout(r), DepNode.Rout(c), callVariance(d.body, c, rt))
    val graph = DepGraph.build(nodes, edges.toVector.distinct)
    val bad = graph.sccs.filter(s => s.recursive && !s.certified)
    if bad.nonEmpty then return Verdict.Rejected(graph, bad.flatMap(_.offending))
    // ---- systems: one per recursive SCC, in stratum order ----
    val systems = mutable.ArrayBuffer.empty[EqSystem]
    for scc <- graph.sccs if scc.recursive do
      val fixes = scc.nodes.collect { case DepNode.Fix(v) => v }
      val routs = scc.nodes.collect { case DepNode.Rout(r) => r }
      if routs.nonEmpty then
        // a recursive Call SCC: representable iff every SCC call passes the parameters through
        val sig = reach(routs.head)
        val passRefs = sig.refs.map(Path.Deref(_))
        val passMentions = sig.mentions.map(Mention(_))
        val sameSig = routs.forall(r => reach(r).refs == sig.refs && reach(r).mentions == sig.mentions)
        def sccCalls(s: Space): Vector[Call] = collect(s)({ case c: Call if routs.contains(c.r) => c })._1.map(_._2.asInstanceOf[Call])
        val passthrough = routs.forall(r => sccCalls(reach(r).body).forall(c => c.refs == passRefs && c.mentions == passMentions))
        if fixes.nonEmpty then
          return Verdict.Unsupported(graph, s"a recursive component mixing a top-level Fixpoint with routines ${routs.map(_.s).mkString(",")}")
        if !sameSig || !passthrough then
          return Verdict.Unsupported(graph,
            s"the recursive call component {${routs.map(_.s).mkString(",")}} changes its arguments across calls; " +
            "a finite simultaneous system needs passthrough parameters (Bekić); not representable — left to the executors' own Call rule")
        val vars = routs.map(r => r -> SpaceMention(s"#rec#${r.s}")).toMap
        val eqs = routs.map { r =>
          val body = subs(reach(r).body)(spost = { case c: Call if vars.contains(c.r) => Mention(vars(c.r)) })
          Equation(vars(r), Empty, body)
        }
        val frozen = (sig.mentions.toSet ++ eqs.flatMap(e => Matching.freeMentions(e.body))).filterNot(vars.values.toSet)
        systems += EqSystem(scc.index, eqs, frozen, vars)
      else
        val eqs = fixEqs.filter(e => fixes.contains(e.v))
        val frozen = eqs.flatMap(e => Matching.freeMentions(e.init) ++ Matching.freeMentions(e.body)).toSet.filterNot(fixes.toSet)
        systems += EqSystem(scc.index, eqs, frozen)
    // non-recursive top-level fixpoints (a `Fixpoint` whose body does not read its own variable) are
    // one-round systems too: the equation is kept so the term stays uniform
    for e <- fixEqs if !systems.exists(_.vars.contains(e.v)) do
      val idx = graph.stratumOf(DepNode.Fix(e.v))
      systems += EqSystem(idx, Vector(e), (Matching.freeMentions(e.init) ++ Matching.freeMentions(e.body)) - e.v)
    val ordered = systems.toVector.sortBy(_.stratum)
    val premises = Premises(graph.edges, graph.sccs, Premises.theorems)
    Verdict.Accepted(Lowered(flat, ordered, rcLowered, graph, premises))

  /** the variance of a routine's VALUE in a body that calls it: `+` when every call sits in a
   *  call-positive position (the discipline `SC.callPositive` checks: positive constructors above the
   *  call, call-free arguments, call-free negative operands), `0` otherwise */
  def callVariance(body: Space, r: RoutinePtr, rt: Variance.RoutineTable): Variance =
    // replace every call to `r` by a probe mention and read the probe's variance
    val probe = SpaceMention(s"#probe#${r.s}")
    val probed = subs(body)(spost = { case c: Call if c.r == r =>
      // arguments that call `r` themselves make the position unknown
      if c.mentions.exists(a => callees(a).contains(r)) then Range(Mention(probe), 0, 1)   // a `0` position
      else Mention(probe) })
    Variance.of(probed, probe, rt)

// ==================================================================================================
// THE DIFFERENTIAL TRANSFER
// ==================================================================================================

// obligation: terminating/REGISTRY.tsv A2-DELTA (MECHANIZED: proofs/lean/Zippy/Delta.lean#Zippy.Delta.dden_sound,
// #Zippy.Delta.delta_step_eq, #Zippy.Delta.delta_iteration_eq_naive — D1/D2 per rule, the step equation, and
// the round-for-round agreement of the two schedules)
object Delta:
  import Space.*

  /** `dden s`: the differential denotation over the reference semantics.  `old`/`nw` bind the same
   *  names; the `changing` variables satisfy `old(X) ⊆ nw(X)`.  Every arm is a rule of the file
   *  header; `leaf` evaluates a subterm in full at an environment (the reference `eval`). */
  def dden(s: Space, changing: Set[SpaceMention], old: SpaceContext, nw: SpaceContext, pc: PathContext,
           rc: PartialFunction[RoutinePtr, Routine]): Set[PathValue] =
    def full(x: Space, ctx: SpaceContext): Set[PathValue] = eval(x)(using pc, ctx, rc).paths
    def free(x: Space): Boolean = Matching.freeMentions(x).exists(changing)
    def go(x: Space): Set[PathValue] =
      if !free(x) then Set.empty
      else x match
        case Mention(v) => if changing(v) then nw.resolve(v).paths -- old.resolve(v).paths else Set.empty
        case Union(a, b) => go(a) union go(b)
        case Intersection(a, b) => (go(a) intersect full(b, nw)) union (full(a, nw) intersect go(b))
        case Composition(a, b) =>
          val bn = full(b, nw); val an = full(a, nw)
          (for e1 <- go(a); e2 <- bn yield PathValue(e1.items ++ e2.items)) union
            (for e1 <- an; e2 <- go(b) yield PathValue(e1.items ++ e2.items))
        case Restriction(a, b) =>
          val bn = full(b, nw); val an = full(a, nw)
          go(a).filter(v => bn.exists(q => v.items.startsWith(q.items))) union
            { val db = go(b); an.filter(v => db.exists(q => v.items.startsWith(q.items))) }
        case Subtraction(a, b) =>
          require(!free(b), "differential transfer: the subtrahend must be frozen (a `-` position)")
          go(a) removedAll full(b, nw)
        case Raffination(a, b) =>
          require(!free(b), "differential transfer: the raffination prefix set must be frozen")
          val bn = full(b, nw)
          go(a).filterNot(v => bn.exists(q => v.items.startsWith(q.items)))
        case Wrap(src, p) => val pv = eval(Singleton(p))(using pc, nw, rc).paths.head.items; go(src).map(v => PathValue(pv ++ v.items))
        case Unwrap(src, p) =>
          val pv = eval(Singleton(p))(using pc, nw, rc).paths.head.items
          go(src).collect { case v if v.items.startsWith(pv) => PathValue(v.items.drop(pv.length)) }
        case TailsUnion(src) => go(src).collect { case PathValue(_ :: r) => PathValue(r) }
        case Iteration(src, sym, rest, body) =>
          val srcOld = full(src, old); val srcNew = full(src, nw)
          def groups(v: Set[PathValue]) = v.collect { case PathValue(h :: t) => PathValue(h :: Nil) -> PathValue(t) }.groupMap(_._1)(_._2).view.mapValues(_.toSet).toMap
          val gOld = groups(srcOld); val gNew = groups(srcNew)
          gNew.iterator.flatMap { (h, tailsNew) =>
            val pc2 = pc.grown(Map(sym -> h))
            gOld.get(h) match
              case Some(tailsOld) =>
                // an old head: the body's differential under (rest := old tails → new tails)
                dden(body, changing + rest, old.grown(Map(rest -> SpaceValue(tailsOld))), nw.grown(Map(rest -> SpaceValue(tailsNew))), pc2, rc)
              case None =>
                // a NEW head: the whole body at the new environment
                eval(body)(using pc2, nw.grown(Map(rest -> SpaceValue(tailsNew))), rc).paths
          }.toSet
        // sound, not incremental: a nested fixpoint, a call to a frozen callee, an unknown-variance
        // operator — the whole new value (D1 and D2 hold trivially)
        case _ => full(x, nw)
    go(s)

// ==================================================================================================
// EXECUTION: NAIVE AND DELTA SCHEDULES, ROUND FOR ROUND
// ==================================================================================================

enum Schedule:
  case Naive, Delta

/** the IR's state at one round boundary */
final case class Round(n: Int, acc: Map[SpaceMention, SpaceValue], delta: Map[SpaceMention, SpaceValue],
                       events: Events):
  def show: String = s"round $n: " + acc.toVector.sortBy(_._1.s).map((v, a) => s"${v.s}=${a.paths.size}(+${delta(v).paths.size})").mkString(" ")

/** the trace of one system solve: every round boundary, the provenance, the stationary value */
final case class Solve(system: EqSystem, schedule: Schedule, rounds: Vector[Round],
                       introducedAt: Map[SpaceMention, Map[PathValue, Int]]):
  def value: Map[SpaceMention, SpaceValue] = rounds.last.acc
  def events: Events = rounds.foldLeft(Events.zero)(_ + _.events)
  def show: String = s"${schedule} ${rounds.length} rounds — " + rounds.map(_.show).mkString("; ")

object Exec:
  import Space.*

  /** SOLVE one system under an environment binding its frozen mentions.  `verify` re-checks the step
   *  equation `A ∪ deltaStep = A ∪ F(A)` at every round of the delta schedule against a full
   *  evaluation, and the value against the naive schedule at the end. */
  def solve(sys: EqSystem, schedule: Schedule, env: SpaceContext, pc: PathContext,
            rc: PartialFunction[RoutinePtr, Routine], verify: Boolean = false, countEvents: Boolean = false,
            maxRounds: Int = 100000): Solve =
    def counted[A](body: => A): (A, Events) =
      if countEvents then EffortSink.count(body) else (body, Events.zero)
    val vars = sys.vars
    def ctxOf(acc: Map[SpaceMention, SpaceValue]): SpaceContext = env.grown(acc)
    val rounds = mutable.ArrayBuffer.empty[Round]
    val introduced = mutable.Map.empty[SpaceMention, mutable.Map[PathValue, Int]]
    def record(n: Int, delta: Map[SpaceMention, SpaceValue]): Unit =
      for (v, d) <- delta; p <- d.paths do introduced.getOrElseUpdate(v, mutable.Map.empty).getOrElseUpdate(p, n)
    // A(0) = init
    val (init, e0) = counted(vars.zip(sys.eqs).map((v, e) => v -> eval(e.init)(using pc, env, rc)).toMap)
    var acc = init
    var delta = init                                  // at round 0 everything is new
    record(0, delta)
    rounds += Round(0, acc, delta, e0)
    var prev: Map[SpaceMention, SpaceValue] = vars.map(_ -> SpaceValue(Set.empty)).toMap   // A(-1)
    var n = 0
    var stop = false
    while !stop && n < maxRounds do
      n += 1
      val (stepped, ev) = counted {
        schedule match
          case Schedule.Naive =>
            vars.zip(sys.eqs).map((v, e) => v -> SpaceValue(eval(e.body)(using pc, ctxOf(acc), rc).paths -- acc(v).paths)).toMap
          case Schedule.Delta =>
            if n == 1 then
              // the first step is full: it establishes the invariant F(A(0)) ⊆ A(1)
              vars.zip(sys.eqs).map((v, e) => v -> SpaceValue(eval(e.body)(using pc, ctxOf(acc), rc).paths -- acc(v).paths)).toMap
            else
              val changing = vars.filter(v => delta(v).paths.nonEmpty).toSet
              vars.zip(sys.eqs).map((v, e) =>
                v -> SpaceValue(Delta.dden(e.body, changing, ctxOf(prev), ctxOf(acc), pc, rc) -- acc(v).paths)).toMap
      }
      if verify && schedule == Schedule.Delta && n > 1 then
        for (v, e) <- vars.zip(sys.eqs) do
          val fullStep = eval(e.body)(using pc, ctxOf(acc), rc).paths
          val lhs = acc(v).paths union stepped(v).paths
          val rhs = acc(v).paths union fullStep
          require(lhs == rhs, s"STEP EQUATION VIOLATED at round $n for ${v.s}: A ∪ deltaStep ≠ A ∪ F(A) " +
                              s"(${(lhs diff rhs).size} extra, ${(rhs diff lhs).size} missing)")
      prev = acc
      acc = vars.map(v => v -> SpaceValue(acc(v).paths union stepped(v).paths)).toMap
      delta = stepped
      record(n, delta)
      rounds += Round(n, acc, delta, ev)
      stop = delta.values.forall(_.paths.isEmpty)
    require(stop, s"system did not reach its stationary point in $maxRounds rounds")
    val out = Solve(sys, schedule, rounds.toVector, introduced.view.mapValues(_.toMap).toMap)
    if verify && schedule == Schedule.Delta then
      val naive = solve(sys, Schedule.Naive, env, pc, rc)
      require(naive.value == out.value, "the delta and naive schedules disagree on the stationary value")
      require(naive.rounds.length == out.rounds.length, "the delta and naive schedules disagree on the round count")
      for (a, b) <- naive.rounds.zip(out.rounds) do
        require(a.acc == b.acc, s"the delta and naive accumulators disagree at round ${a.n}")
    out

  /** RUN a lowered program under the reference semantics: solve the systems in stratum order under the
   *  input environment, then evaluate the term with the system variables bound and every `Call` to an
   *  SCC routine answered by solving its system at the call's arguments. */
  def run(p: Lowered, schedule: Schedule, env: SpaceContext, pc: PathContext = PathContextMap(Map.empty),
          verify: Boolean = false, countEvents: Boolean = false): (SpaceValue, Vector[Solve]) =
    val solves = mutable.ArrayBuffer.empty[Solve]
    def evalWithSystems(s: Space, ctx: SpaceContext, pctx: PathContext): SpaceValue =
      // Calls to system routines are intercepted syntactically: rewrite them into GroundedSS nodes
      // whose function solves the system.  The rewrite is on the TERM being evaluated, so nested
      // occurrences inside iteration bodies are rewritten before the body runs.
      val rewritten = subs(s)(spost = { case c: Call if p.systemOfRoutine(c.r).isDefined =>
        val sys = p.systemOfRoutine(c.r).get
        val d = p.routines(c.r)
        val tagged = c.mentions.zipWithIndex.map((m, i) => Wrap(m, Path.Constant(PathValue(List(s"#arg$i#"))))).reduceOption(Union(_, _)).getOrElse(Empty)
        GroundedSS(tagged, args => {
          val bound = d.mentions.zipWithIndex.map((m, i) =>
            m -> SpaceValue(args.paths.collect { case PathValue(t :: rest) if t == s"#arg$i#" => PathValue(rest) })).toMap
          val innerEnv = ctx.grown(bound)
          val sol = solve(sys, schedule, innerEnv, pctx, p.routines, verify, countEvents)
          solves += sol
          sol.value(sys.routines(c.r))
        }) })
      eval(rewritten)(using pctx, ctx, p.routines)
    var ctx = env
    for sys <- p.systems if sys.routines.isEmpty do
      val sol = solve(sys, schedule, ctx, pc, p.routines, verify, countEvents)
      solves += sol
      ctx = ctx.grown(sol.value)
    val v = evalWithSystems(p.term, ctx, pc)
    (v, solves.toVector)

/** READABLE RENDERING of the IR */
object DeltaIRRender:
  def render(v: Verdict): String = v match
    case Verdict.Accepted(p) =>
      val sb = new StringBuilder
      sb ++= "== stratified delta-fixpoint IR ==\n"
      sb ++= s"term: ${p.term.show.replace('\n', ' ')}\n"
      for s <- p.systems do
        sb ++= s"stratum ${s.stratum}:\n"
        for e <- s.eqs do sb ++= s"  ${e.show}\n"
        if s.frozen.nonEmpty then sb ++= s"  frozen: ${s.frozen.map(_.s).toVector.sorted.mkString(", ")}\n"
        if s.routines.nonEmpty then sb ++= s"  routines: ${s.routines.map((r, v) => s"${r.s}→${v.s}").mkString(", ")}\n"
      sb ++= "dependency graph:\n"
      for e <- p.graph.edges do sb ++= s"  ${e.show}\n"
      sb ++= p.graph.show + "\n"
      sb ++= p.premises.show + "\n"
      sb.result()
    case other => other.show
