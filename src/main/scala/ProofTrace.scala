package morkl

import scala.collection.mutable

/** TYPED, COMPOSITIONAL PROOF TRACES (tasks.md C3).
 *
 *  A transformation claim `a ≡ b` is a finite DAG of typed nodes whose leaves are universal theorems
 *  (a certified optimiser law, applied at named positions with its exact instance), definitional steps
 *  (an unfold — the substitution theorem `SubstSem.lean`; a fold — the instance lemma; an
 *  alpha-equivalence) or direct backend obligations (an SMT/egg artifact with a real goal), and whose
 *  inner nodes are positional replacements and transitive compositions (`Drive.lean`: `Ctx.plug_congr`,
 *  `Chain`).  Every node carries its two endpoint terms, so a checker can replay it INDEPENDENTLY of the
 *  code that produced it: re-apply the law, re-run the substitution, re-check the instance, re-read the
 *  artifact, re-compose the endpoints.  What a trace never contains: a marker deferring to another marker,
 *  a single-side observation, or an identity claim without both an alpha-equivalence and a verified
 *  optimiser no-op.  The rendering is deterministic (terms by digest, nodes in id order). */
object ProofTrace:
  import Space.*

  /** a position: child indices from the root, in `SpatialAnalysis.childrenOf` order */
  type Pos = Vector[Int]

  enum Node:
    /** a certified optimiser law applied as a whole-term rewrite.  `changed` are the positions whose
     *  subterms differ, each with its local (instance of the law's left side, right side) pair — the
     *  exact matcher; `guards` names the side conditions the law checked (empty when it has none). */
    case LawInstance(law: String, before: Space, after: Space, changed: Vector[(Pos, Space, Space)], guards: Vector[String])
    /** alpha-equivalent terms denote the same */
    case AlphaEquivalence(a: Space, b: Space)
    /** ONE UNFOLD: `call` to `routine` denotes `body` with the arguments substituted (`Subst`) — O6a */
    case Unfold(routine: RoutinePtr, call: Space, body: Space, mentions: Vector[(String, Space)], paths: Vector[(String, Path)], result: Space)
    /** A FOLD: the configuration `conf` of residual node `node`, under θ, is `instance`; the residual
     *  call `call` denotes it (`Drive.lean` `fold_step`).  A NEW node is the same step with θ the identity. */
    case Fold(node: RoutinePtr, conf: Space, thetaM: Vector[(String, Space)], thetaP: Vector[(String, Path)], instance: Space, call: Space)
    /** A GENERALIZATION (whistle): `instance` is `skeleton·θ`; the skeleton was driven to `residual`
     *  (trace `skeletonTrace`, endpoints skeleton-call → `residual`); each hole `h ↦ orig` was driven to
     *  `driven` (trace ids); the result is `residual` with the driven holes substituted. */
    case Generalization(skeleton: Space, thetaM: Vector[(String, Space)], thetaP: Vector[(String, Path)], instance: Space,
                        residual: Space, skeletonTrace: Int, holes: Vector[(String, Space, Space, Int)], result: Space)
    /** a positional replacement justified by node `by`, whose endpoints are the two subterms at `pos` */
    case Positional(before: Space, pos: Pos, after: Space, by: Int)
    /** a direct backend obligation: the artifact carries the goal (a REAL cell) or a law-justified chain */
    case BackendRefinement(backend: String, boundary: String, artifact: String, obligation: String, before: Space, after: Space)
    /** the optimiser is the identity on `term` (no source law fires) — half of an identity claim */
    case OptimizerNoOp(term: Space)
    /** the operation-graph optimiser is the identity on `routine`: its plain and optimised graphs read
     *  back as `plain` and `optimized`, alpha-equal — the graph boundary's half of an identity claim */
    case GraphOptimizerNoOp(routine: Routine, plain: Space, optimized: Space)
    /** transitive composition: `after` of each step is `before` of the next */
    case Compose(steps: Vector[Int], before: Space, after: Space)

    def src: Space = this match
      case LawInstance(_, b, _, _, _) => b
      case AlphaEquivalence(a, _) => a
      case Unfold(_, c, _, _, _, _) => c
      case Fold(_, _, _, _, i, _) => i
      case Generalization(_, _, _, i, _, _, _, _) => i
      case Positional(b, _, _, _) => b
      case BackendRefinement(_, _, _, _, b, _) => b
      case OptimizerNoOp(t) => t
      case GraphOptimizerNoOp(_, pl, _) => pl
      case Compose(_, b, _) => b
    def dst: Space = this match
      case LawInstance(_, _, a, _, _) => a
      case AlphaEquivalence(_, b) => b
      case Unfold(_, _, _, _, _, r) => r
      case Fold(_, _, _, _, _, c) => c
      case Generalization(_, _, _, _, _, _, _, r) => r
      case Positional(_, _, a, _) => a
      case BackendRefinement(_, _, _, _, _, a) => a
      case OptimizerNoOp(t) => t
      case GraphOptimizerNoOp(_, _, op) => op
      case Compose(_, _, a) => a
    def kind: String = this match
      case _: LawInstance => "LawInstance"
      case _: AlphaEquivalence => "AlphaEquivalence"
      case _: Unfold => "Unfold"
      case _: Fold => "Fold"
      case _: Generalization => "Generalization"
      case _: Positional => "Positional"
      case _: BackendRefinement => "BackendRefinement"
      case _: OptimizerNoOp => "OptimizerNoOp"
      case _: GraphOptimizerNoOp => "GraphOptimizerNoOp"
      case _: Compose => "Compose"
    /** the node ids this node depends on */
    def deps: Vector[Int] = this match
      case Positional(_, _, _, by) => Vector(by)
      case Generalization(_, _, _, _, _, st, holes, _) => st +: holes.map(_._4)
      case Compose(steps, _, _) => steps
      case _ => Vector.empty

  /** a hash-consed trace DAG: nodes in id order, every dependency an earlier id */
  final case class Dag(nodes: Vector[Node], root: Int):
    def apply(i: Int): Node = nodes(i)
    def src: Space = nodes(root).src
    def dst: Space = nodes(root).dst
    def leaves: Vector[Node] = nodes.filter(_.deps.isEmpty)
    def size: Int = nodes.length
    /** DETERMINISTIC RENDERING: one line per node (terms by digest), then the term table */
    def render: String =
      val terms = mutable.LinkedHashMap.empty[String, String]
      def sha(s: Space): String = { val h = ProofTrace.sha(s); terms.getOrElseUpdate(h, ProofTrace.structural(Matching.canon(s))); h }
      def kv(pairs: Iterable[(String, String)]): String = pairs.map((k, v) => s"$k=$v").mkString(";")
      val sb = new StringBuilder
      sb ++= "# PROOF TRACE (tasks.md C3) — a typed DAG; every node carries its endpoint terms by digest, every\n"
      sb ++= "# dependency is an earlier id, every leaf is a law instance, a definitional step or a backend obligation.\n"
      sb ++= "# Replay: morkl.ProofTrace.Checker (Scala, re-runs each step); scripts/check_traces.py (structural, independent).\n"
      sb ++= s"# root\t$root\n# id\tkind\tbefore\tafter\tfields\tdeps\n"
      for (n, i) <- nodes.zipWithIndex do
        val fields = n match
          case Node.LawInstance(law, _, _, changed, guards) =>
            kv(Vector("law" -> law, "changed" -> changed.map((p, l, r) => s"${p.mkString(".")}:${sha(l)}:${sha(r)}").mkString(","), "guards" -> guards.mkString(",")))
          case Node.AlphaEquivalence(_, _) => "-"
          case Node.Unfold(r, _, body, ms, ps, _) =>
            kv(Vector("routine" -> r.s, "body" -> sha(body), "mentions" -> ms.map((m, t) => s"$m:${sha(t)}").mkString(","), "paths" -> ps.map((p, t) => s"$p:${ProofTrace.shaP(t)}").mkString(",")))
          case Node.Fold(node, conf, tm, tp, _, _) =>
            kv(Vector("node" -> node.s, "conf" -> sha(conf), "thetaM" -> tm.map((m, t) => s"$m:${sha(t)}").mkString(","), "thetaP" -> tp.map((p, t) => s"$p:${ProofTrace.shaP(t)}").mkString(",")))
          case Node.Generalization(sk, tm, tp, _, resid, st, holes, _) =>
            kv(Vector("skeleton" -> sha(sk), "thetaM" -> tm.map((m, t) => s"$m:${sha(t)}").mkString(","), "thetaP" -> tp.map((p, t) => s"$p:${ProofTrace.shaP(t)}").mkString(","),
                      "residual" -> sha(resid), "skeletonTrace" -> st.toString, "holes" -> holes.map((h, o, d, t) => s"$h:${sha(o)}:${sha(d)}:$t").mkString(",")))
          case Node.Positional(_, pos, _, by) => kv(Vector("pos" -> pos.mkString("."), "by" -> by.toString))
          case Node.BackendRefinement(be, bd, art, ob, _, _) => kv(Vector("backend" -> be, "boundary" -> bd, "artifact" -> art, "obligation" -> ob))
          case Node.OptimizerNoOp(_) => "-"
          case Node.GraphOptimizerNoOp(r, _, _) => kv(Vector("routine" -> r.name.s, "refs" -> r.refs.map(_.s).mkString(","), "mentions" -> r.mentions.map(_.s).mkString(","), "body" -> sha(r.body)))
          case Node.Compose(steps, _, _) => kv(Vector("steps" -> steps.mkString(",")))
        val deps = if n.deps.isEmpty then "-" else n.deps.mkString(",")
        sb ++= s"$i\t${n.kind}\t${sha(n.src)}\t${sha(n.dst)}\t$fields\t$deps\n"
      sb ++= "# terms\n"
      for (h, t) <- terms do sb ++= s"T\t$h\t${t.replace('\n', ' ').replace('\t', ' ')}\n"
      sb.result()

  /** Terms are digested ALPHA-CANONICALLY (binders renamed by `Matching.canon`) so a trace does not
   *  depend on the fresh names a particular run happened to draw, and in the STRUCTURAL rendering so
   *  an independent reader can parse constructors out of the term table (tasks.md D1). */
  def sha(s: Space): String = digest(structural(Matching.canon(s)))

  /** THE STRUCTURAL RENDERING of a term: every constructor by its name, fully parenthesised, binders
   *  and names quoted — `Union(Iteration(Mention("s"),Deref("h"),"r",Wrap(Mention("r"),Deref("h"))),…)`.
   *  Unlike `show` it has no infix operators, so `Ctor(` is exactly one constructor occurrence and a
   *  tokenizer with no knowledge of MORKL can count them (`scripts/check_coverage.py`). */
  def structural(s: Space): String =
    val sb = new StringBuilder
    def q(x: String): Unit = { sb += '"'; sb ++= x.replace("\\", "\\\\").replace("\"", "\\\""); sb += '"' }
    def pv(v: PathValue): Unit = { sb += '['; sb ++= v.items.map(i => i.toString.replace("\\", "\\\\").replace("\"", "\\\"")).map("\"" + _ + "\"").mkString(","); sb += ']' }
    def p(x: Path): Unit = x match
      case Path.Deref(pr) => sb ++= "Deref("; q(pr.s); sb += ')'
      case Path.Constant(v) => sb ++= "Constant("; pv(v); sb += ')'
      case Path.Concat(l, r) => sb ++= "Concat("; p(l); sb += ','; p(r); sb += ')'
      case Path.GroundedPP(a, _) => sb ++= "GroundedPP("; p(a); sb += ')'
      case Path.GroundedSP(a, _) => sb ++= "GroundedSP("; g(a); sb += ')'
    def g(x: Space): Unit = x match
      case Empty => sb ++= "Empty"
      case Call(r, refs, ms) => sb ++= "Call("; q(r.s); for a <- refs do { sb += ','; p(a) }; sb += ';'; for m <- ms do { sb += ','; g(m) }; sb += ')'
      case Mention(m) => sb ++= "Mention("; q(m.s); sb += ')'
      case Singleton(a) => sb ++= "Singleton("; p(a); sb += ')'
      case Literal(v) => sb ++= "Literal(["; sb ++= v.paths.toVector.map(_.show).sorted.map(x => "\"" + x.replace("\\", "\\\\").replace("\"", "\\\"") + "\"").mkString(","); sb ++= "])"
      case Union(a, b) => bin("Union", a, b)
      case Intersection(a, b) => bin("Intersection", a, b)
      case Subtraction(a, b) => bin("Subtraction", a, b)
      case Restriction(a, b) => bin("Restriction", a, b)
      case Raffination(a, b) => bin("Raffination", a, b)
      case Composition(a, b) => bin("Composition", a, b)
      case Iteration(src, sym, rest, body) => sb ++= "Iteration("; g(src); sb += ','; q(sym.s); sb += ','; q(rest.s); sb += ','; g(body); sb += ')'
      case Fixpoint(init, rec, body) => sb ++= "Fixpoint("; g(init); sb += ','; q(rec.s); sb += ','; g(body); sb += ')'
      case Fold(src, ini, acc, sym, rest, body, upd) => sb ++= "Fold("; g(src); sb += ','; p(ini); sb += ','; q(acc.s); sb += ','; q(sym.s); sb += ','; q(rest.s); sb += ','; g(body); sb += ','; p(upd); sb += ')'
      case Wrap(a, w) => sb ++= "Wrap("; g(a); sb += ','; p(w); sb += ')'
      case Unwrap(a, w) => sb ++= "Unwrap("; g(a); sb += ','; p(w); sb += ')'
      case TailsUnion(a) => sb ++= "TailsUnion("; g(a); sb += ')'
      case TailsIntersection(a) => sb ++= "TailsIntersection("; g(a); sb += ')'
      case GroundedPS(a, _) => sb ++= "GroundedPS("; p(a); sb += ')'
      case GroundedSS(a, _) => sb ++= "GroundedSS("; g(a); sb += ')'
      case Range(a, lo, hi) => sb ++= "Range("; g(a); sb ++= s",$lo,$hi)"
    def bin(n: String, a: Space, b: Space): Unit = { sb ++= n; sb += '('; g(a); sb += ','; g(b); sb += ')' }
    g(s)
    sb.result()
  def shaP(p: Path): String = digest(p.toString)
  private def digest(text: String): String =
    val md = java.security.MessageDigest.getInstance("SHA-256").digest(text.getBytes("UTF-8"))
    md.take(6).map(b => f"${b & 0xff}%02x").mkString

  /** hash-consing builder: structurally equal nodes are one id */
  final class Builder:
    private val index = mutable.LinkedHashMap.empty[Node, Int]
    def add(n: Node): Int =
      for d <- n.deps do require(d >= 0 && d < index.size, s"trace node depends on an id not yet built: $d")
      index.getOrElseUpdate(n, index.size)
    def node(i: Int): Node = index.keys.toVector(i)
    def size: Int = index.size
    def dag(root: Int): Dag = Dag(index.keys.toVector, root)
    /** SPLICE another DAG into this builder: every node re-added in id order with its dependencies
     *  remapped through the ids this builder assigned (hash-consing may merge a node with an existing
     *  equal one, so a fixed offset would be wrong); returns the new id of `inner`'s root */
    def splice(inner: Dag): Int =
      val map = mutable.Map.empty[Int, Int]
      for (n, i) <- inner.nodes.zipWithIndex do
        val remapped = n match
          case Node.Positional(bf, pos, af, by) => Node.Positional(bf, pos, af, map(by))
          case Node.Compose(steps, bf, af) => Node.Compose(steps.map(map), bf, af)
          case Node.Generalization(sk, tm, tp, i0, r, st, holes, res) =>
            Node.Generalization(sk, tm, tp, i0, r, map(st), holes.map((h, o, d, t) => (h, o, d, map(t))), res)
          case other => other
        map(i) = add(remapped)
      map(inner.root)
    /** a chain of already-built steps, as one Compose (or the single step itself) */
    def compose(steps: Vector[Int], before: Space, after: Space): Int =
      if steps.length == 1 && node(steps.head).src == before && node(steps.head).dst == after then steps.head
      else add(Node.Compose(steps, before, after))

  // ---- terms: children, rebuild, positions --------------------------------------------------------
  def children(s: Space): Vector[Space] = SpatialAnalysis.childrenOf(s)
  def rebuild(s: Space, kids: Vector[Space]): Space = s match
    case Union(_, _) => Union(kids(0), kids(1))
    case Intersection(_, _) => Intersection(kids(0), kids(1))
    case Subtraction(_, _) => Subtraction(kids(0), kids(1))
    case Restriction(_, _) => Restriction(kids(0), kids(1))
    case Raffination(_, _) => Raffination(kids(0), kids(1))
    case Composition(_, _) => Composition(kids(0), kids(1))
    case Wrap(_, p) => Wrap(kids(0), p)
    case Unwrap(_, p) => Unwrap(kids(0), p)
    case TailsUnion(_) => TailsUnion(kids(0))
    case TailsIntersection(_) => TailsIntersection(kids(0))
    case Range(_, lo, hi) => Range(kids(0), lo, hi)
    case Iteration(_, sym, rest, _) => Iteration(kids(0), sym, rest, kids(1))
    case Fold(_, i, acc, sym, rest, _, u) => Fold(kids(0), i, acc, sym, rest, kids(1), u)
    case Fixpoint(_, rec, _) => Fixpoint(kids(0), rec, kids(1))
    case Call(r, refs, _) => Call(r, refs, kids)
    case leaf => leaf
  /** the top slot of an operation graph, read back as a term (`untranspile`) */
  def untranspileTop(g: RecursiveOpGraph): Space =
    val st = mutable.Stack(new Array[Path | Space | Null](g.nodes.length))
    untranspile(g, st)
    st.top.last.asInstanceOf[Space]
  def subtermAt(s: Space, pos: Pos): Option[Space] = SpatialPipeline.subtermAt(s, pos)
  def replaceAt(s: Space, pos: Pos, repl: Space): Option[Space] = SpatialPipeline.replaceAt(s, pos, repl)
  /** the maximal positions where two terms differ (a differing subtree is one position) */
  def diffPositions(a: Space, b: Space): Vector[(Pos, Space, Space)] =
    def go(x: Space, y: Space, pos: Pos): Vector[(Pos, Space, Space)] =
      if x == y then Vector.empty
      else
        val (kx, ky) = (children(x), children(y))
        val sameShape = kx.length == ky.length && kx.nonEmpty && rebuild(x, ky) == y
        if !sameShape then Vector((pos, x, y))
        else kx.indices.toVector.flatMap(i => go(kx(i), ky(i), pos :+ i))
    go(a, b, Vector.empty)

  /** a law step as a node: the whole-term rewrite plus its differing positions */
  def lawNode(law: String, before: Space, after: Space, guards: Vector[String] = Vector.empty): Node =
    Node.LawInstance(law, before, after, diffPositions(before, after), guards)

  // ---- THE CHECKER -----------------------------------------------------------------------------
  /** the residual nodes' configurations, for `Fold` nodes: name → (configuration, ref params, mention params) */
  type NodeTable = Map[RoutinePtr, (Space, Vector[PathRef], Vector[SpaceMention])]

  object Checker:
    lazy val lawRegistry: Set[String] =
      val f = new java.io.File(RunEnvironment.repoRoot, "proofs/laws/REGISTRY.tsv")
      if !f.isFile then Set.empty
      else scala.io.Source.fromFile(f).getLines().filter(l => l.nonEmpty && !l.startsWith("#") && !l.startsWith("law\t")).map(_.split("\t")(0)).toSet

    /** every failure the DAG has; empty is a replayed proof of `dag.src ≡ dag.dst` */
    def check(dag: Dag, rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty, nodes: NodeTable = Map.empty,
              root: java.io.File = RunEnvironment.repoRoot): Vector[String] =
      val bad = Vector.newBuilder[String]
      val laws = SC.sourceLaws.toMap
      if dag.root < 0 || dag.root >= dag.nodes.length then bad += s"root $dag.root is not a node"
      for (n, i) <- dag.nodes.zipWithIndex do
        for d <- n.deps do
          if d < 0 || d >= dag.nodes.length then bad += s"node $i: dependency $d is not a node"
          else if d >= i then bad += s"node $i: dependency $d is not earlier (the trace must be a DAG)"
        n match
          case Node.LawInstance(law, before, after, changed, _) =>
            laws.get(law) match
              case None => bad += s"node $i: `$law` is not a source law"
              case Some(f) => if f(before) != after then bad += s"node $i: re-applying `$law` does not reproduce `after`"
            if !lawRegistry.contains(law) then bad += s"node $i: `$law` has no row in proofs/laws/REGISTRY.tsv"
            if changed.isEmpty then bad += s"node $i: a law instance that changed nothing"
            for (pos, l, r) <- changed do
              if !subtermAt(before, pos).contains(l) then bad += s"node $i: position ${pos.mkString(".")} of `before` is not the recorded instance"
              if !subtermAt(after, pos).contains(r) then bad += s"node $i: position ${pos.mkString(".")} of `after` is not the recorded result"
              if l == r then bad += s"node $i: an instance that is its own result"
            val rebuilt = changed.foldLeft(Option(before))((acc, c) => acc.flatMap(t => replaceAt(t, c._1, c._3)))
            if !rebuilt.contains(after) then bad += s"node $i: the recorded instances do not account for the whole rewrite"
          case Node.AlphaEquivalence(a, b) =>
            if !Matching.alphaEqual(a, b) then bad += s"node $i: the two sides are not alpha-equivalent"
          case Node.Unfold(r, call, body, ms, ps, result) =>
            call match
              case Call(r2, refs, args) if r2 == r =>
                if !rc.isDefinedAt(r) then bad += s"node $i: unknown routine ${r.s}"
                else
                  val d = rc(r)
                  if d.body != body then bad += s"node $i: the recorded body is not ${r.s}'s"
                  if d.refs.length != refs.length || d.mentions.length != args.length then bad += s"node $i: arity mismatch"
                  else
                    val sm = d.mentions.zip(args).toMap; val pm = d.refs.zip(refs).toMap
                    if ms != d.mentions.zip(args).map((m, t) => m.s -> t) then bad += s"node $i: the recorded mention substitution is not the call's arguments"
                    if ps != d.refs.zip(refs).map((p, t) => p.s -> t) then bad += s"node $i: the recorded path substitution is not the call's arguments"
                    val re = Subst(body, sm, pm)
                    if !(re == result || Matching.alphaEqual(re, result)) then bad += s"node $i: re-running the substitution does not reproduce the unfolding"
              case _ => bad += s"node $i: `call` is not a call to ${r.s}"
          case Node.Fold(node, conf, tm, tp, instance, call) =>
            nodes.get(node) match
              case None => bad += s"node $i: ${node.s} is not a residual node of this run"
              case Some((conf2, refs, ments)) =>
                if !Matching.alphaEqual(conf, conf2) then bad += s"node $i: the recorded configuration is not ${node.s}'s"
                val sm = tm.map((m, t) => SpaceMention(m) -> t).toMap
                val pm = tp.map((p, t) => PathRef(p) -> t).toMap
                if !Matching.alphaEqual(Matching.subst(conf, sm, pm), instance) then bad += s"node $i: the configuration under θ is not the folded instance"
                val expected = Call(node, refs.map(pr => pm.getOrElse(pr, Path.Deref(pr))), ments.map(m => sm.getOrElse(m, Mention(m))))
                if call != expected then bad += s"node $i: the residual call does not pass θ's arguments to ${node.s}"
          case Node.Generalization(sk, tm, tp, instance, resid, st, holes, result) =>
            val sm = tm.map((m, t) => SpaceMention(m) -> t).toMap
            val pm = tp.map((p, t) => PathRef(p) -> t).toMap
            if !Matching.alphaEqual(Matching.subst(sk, sm, pm), instance) then bad += s"node $i: the skeleton under θ is not the generalized configuration"
            if st >= 0 && st < dag.nodes.length then
              val t = dag.nodes(st)
              if t.src != sk then bad += s"node $i: the skeleton trace does not start at the skeleton"
              if t.dst != resid then bad += s"node $i: the skeleton trace does not end at the residual"
            for (h, orig, driven, tid) <- holes do
              if !sm.get(SpaceMention(h)).contains(orig) then bad += s"node $i: hole $h is not θ's value"
              if tid >= 0 && tid < dag.nodes.length then
                val t = dag.nodes(tid)
                if t.src != orig || t.dst != driven then bad += s"node $i: hole $h's trace endpoints are not (orig, driven)"
            val drivenMap = holes.map((h, _, d, _) => SpaceMention(h) -> d).toMap
            val expected = Matching.subst(resid, drivenMap ++ sm.filterNot((m, _) => drivenMap.contains(m)), pm)
            if !(expected == result || Matching.alphaEqual(expected, result)) then bad += s"node $i: the result is not the residual with the driven holes substituted"
          case Node.Positional(before, pos, after, by) =>
            if by >= 0 && by < i then
              val j = dag.nodes(by)
              if !subtermAt(before, pos).contains(j.src) then bad += s"node $i: the subterm at ${pos.mkString(".")} is not the justifying node's `before`"
              if !replaceAt(before, pos, j.dst).contains(after) then bad += s"node $i: replacing at ${pos.mkString(".")} does not give `after`"
          case Node.BackendRefinement(backend, boundary, artifact, obligation, _, _) =>
            if !Set("space", "zipper", "graph").contains(boundary) then bad += s"node $i: unknown boundary $boundary"
            if obligation.isEmpty then bad += s"node $i: a backend refinement without an obligation id"
            val f = new java.io.File(root, artifact)
            if !f.isFile then bad += s"node $i: artifact $artifact does not exist"
            else
              val text = scala.io.Source.fromFile(f).getLines().mkString("\n")
              val hasGoal = text.contains("(assert (not") || text.contains("(check ") || text.contains("LAW-JUSTIFIED-NO-RESIDUAL") || text.contains("LAW-JUSTIFIED:")
              val markerOnly = (text.contains("TRIVIAL-NO-OBLIGATION") || text.contains("IDENTICAL-STRUCTURE") || text.contains("IDENTICAL-LITERAL") || text.contains("SINGLE-SIDE-OBSERVATION")) && !hasGoal
              if markerOnly then bad += s"node $i: $artifact is a marker, not an obligation (a marker deferring to a marker certifies nothing)"
              else if !hasGoal then bad += s"node $i: $artifact carries no goal and no law-justified chain"
          case Node.OptimizerNoOp(term) =>
            if SC.reduce(term) != term then bad += s"node $i: the optimiser is not the identity on the term"
          case Node.GraphOptimizerNoOp(r, plain, optimized) =>
            try
              val pl = untranspileTop(transpile(r)); val op = untranspileTop(optimize(transpile(r)))
              if !Matching.alphaEqual(pl, plain) then bad += s"node $i: the recorded plain graph is not ${r.name.s}'s"
              if !Matching.alphaEqual(op, optimized) then bad += s"node $i: the recorded optimised graph is not ${r.name.s}'s"
              if !Matching.alphaEqual(pl, op) then bad += s"node $i: the graph optimiser is not the identity on ${r.name.s}"
            catch case e: Throwable => bad += s"node $i: the graph could not be rebuilt: ${e.getMessage}"
          case Node.Compose(steps, before, after) =>
            if steps.isEmpty then bad += s"node $i: an empty composition"
            else
              val ok = steps.forall(s => s >= 0 && s < i)
              if ok then
                val ns = steps.map(dag.nodes)
                if ns.head.src != before then bad += s"node $i: the composition does not start at `before`"
                if ns.last.dst != after then bad += s"node $i: the composition does not end at `after`"
                for k <- 0 until ns.length - 1 do
                  if ns(k).dst != ns(k + 1).src && !Matching.alphaEqual(ns(k).dst, ns(k + 1).src) then
                    bad += s"node $i: step ${steps(k)} does not compose with step ${steps(k + 1)}"
      // an IDENTITY claim (before == after at the root) must rest on an alpha-equivalence AND a verified no-op
      if dag.nodes.nonEmpty && dag.root < dag.nodes.length then
        val r = dag.nodes(dag.root)
        val identity = r.src == r.dst || Matching.alphaEqual(r.src, r.dst)
        val kinds = reachable(dag, dag.root).map(dag.nodes(_).kind).toSet
        if identity && !(kinds.contains("AlphaEquivalence") && (kinds.contains("OptimizerNoOp") || kinds.contains("GraphOptimizerNoOp"))) &&
           !kinds.exists(k => k == "LawInstance" || k == "Fold" || k == "Unfold" || k == "Generalization" || k == "BackendRefinement") then
          bad += s"root: an identity claim must carry an independent alpha-equivalence AND a verified optimiser no-op"
      bad.result()

    def reachable(dag: Dag, from: Int): Set[Int] =
      val seen = mutable.Set.empty[Int]
      def go(i: Int): Unit = if seen.add(i) then dag.nodes(i).deps.foreach(go)
      go(from); seen.toSet
