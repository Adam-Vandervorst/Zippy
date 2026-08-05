package morkl

/** z3-powered path-LENGTH bounds (the length twin of [[SizeZ3]], design mirrored from
 *  design_size_constraints.md): translate the term's length facts into a z3 OPTIMIZATION
 *  problem and read the root's `[min |p|, max |p|]` interval off the objectives.
 *
 *  Every distinct subterm (hash-consed by value after [[SizeZ3.alphaRename]]) gets integer
 *  variables `lo`/`hi` (the realized minimum/maximum path length, over ALL bindings a binder
 *  body sees), a Bool `emp` (does the subterm denote ∅), and a unary predicate
 *  `len(l)` — a define-fun OVER-APPROXIMATING the subterm's length set.  The predicates keep
 *  DISJUNCTIVE structure through ∪/∩/wrap/unwrap/tails, which is what the compositional
 *  interval baseline [[Lower.lenBounds]] cannot do: in
 *  `((({len 10} ∪ {len 25}) ∩ {len 15}) ∪ {ε}) · {len 2, len 6}` the meet's predicate
 *  `(l=10 ∨ l=25) ∧ l=15` is unsatisfiable, so z3 forces `emp`, the union collapses to `{ε}`,
 *  and the composition is pinned to `[2, 6]` — the hull-based baseline can only say `[2, 21]`.
 *
 *  Soundness model: every reality (a binding of the free mentions/refs) induces a model where
 *  each node's `lo`/`hi` are its true extreme lengths and `emp` its true emptiness — each
 *  emitted constraint is a true length fact under that reading — so `minimize lo_root` /
 *  `maximize hi_root` are outer bounds over all realities.  Bounds are ∀-quantified over
 *  paths, so they are vacuous for empty realities; the objectives therefore run under
 *  `¬emp_root` (unsat ⇒ the root is provably empty ⇒ the baseline is returned, vacuously
 *  sound).  Every node also asserts its baseline interval, so a sat optimum can only be
 *  equal-or-tighter; on ANY failure the baseline is returned unchanged — tighter everywhere,
 *  unsound nowhere, by construction.
 *
 *  Macro discipline: define-funs are macros, and a node referenced by many parents (pooled
 *  sharing, `x ∪ x`) would expand exponentially — nodes whose estimated expansion exceeds
 *  [[LenZ3.ExpansionCap]] degrade to their interval predicate `lo ≤ l ≤ hi` (cost 1),
 *  cutting the blowup while staying sound. */
object LenZ3:
  import Lower.LenBounds
  private val INF = LenBounds.INF
  private val ExpansionCap = 50000
  private val LenSetCap = 64          // max distinct lengths kept as an exact disjunction

  export SizeZ3.available

  def bounds(s: Space, timeoutSec: Int = 8): LenBounds = boundsWithStatus(s, timeoutSec)._1

  def boundsWithStatus(s0: Space, timeoutSec: Int = 8): (LenBounds, SizeZ3.Status) =
    val base = Lower.lenBounds(s0)
    if !available then return (base, SizeZ3.Status.NoSolver)
    if base.isEmpty then return (base, SizeZ3.Status.Solved)   // provably empty: bounds vacuous
    val s = SizeZ3.alphaRename(s0)
    SizeZ3.scopesProblem(s) match
      case Some(reason) => (base, SizeZ3.Status.ScopeLimited(reason))
      case None =>
        try
          val out = SizeZ3.runZ3(encode(s).text, timeoutSec)
          if out.linesIterator.exists(_.trim == "unsat") then (base, SizeZ3.Status.Solved)  // root provably ∅
          else parseObjectives(out) match
            case Some((zlo, zhi)) =>
              val lo2 = zlo.getOrElse(0L) max base.lo
              val hi2 = zhi.fold(base.hi)(_ min base.hi)
              if lo2 > hi2 then (base, SizeZ3.Status.SolverFailed("inconsistent objectives"))
              else (LenBounds(lo2, hi2), SizeZ3.Status.Solved)
            case None =>
              val head = out.linesIterator.filter(_.nonEmpty).take(1).mkString
              (base, SizeZ3.Status.SolverFailed(if head.isEmpty then "no output" else head))
        catch case e: Throwable => (base, SizeZ3.Status.SolverFailed(e.getClass.getSimpleName))

  /** the lowered SMT text (diagnostics/tooling) — exactly what the solver sees */
  private[morkl] def encodeText(s: Space): String = encode(SizeZ3.alphaRename(s)).text

  // ---- ground folding ---------------------------------------------------------------------
  /** exact length facts of a CLOSED subterm (same closedness + size budget as SizeZ3's fold):
   *  (isEmpty, min, max, distinct length set — None when over [[LenSetCap]]). */
  private val foldCache = new java.util.concurrent.ConcurrentHashMap[Space, Option[(Boolean, Long, Long, Option[Vector[Long]])]]()
  private def groundFold(sp: Space): Option[(Boolean, Long, Long, Option[Vector[Long]])] =
    foldCache.computeIfAbsent(sp, { sp =>
      val closed =
        val (calls, _) = collect(sp)(
          { case Space.Call(_, _, _) | Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => () },
          PartialFunction.empty)
        calls.isEmpty && Matching.freeMentions(sp).isEmpty && Matching.freeRefs(sp).isEmpty
      if !closed || Lower.sizeBounds(sp).hi > 200000 then None
      else
        try
          val lens = eval(sp).paths.iterator.map(_.items.length.toLong).toVector
          if lens.isEmpty then Some((true, 0L, 0L, None))
          else
            val d = lens.distinct.sorted
            Some((false, d.head, d.last, if d.length <= LenSetCap then Some(d) else None))
        catch case _: Throwable => None
    })

  // ---- encoding ------------------------------------------------------------------------------
  private final case class Enc(text: String)

  private def encode(root: Space): Enc =
    val ids = collection.mutable.LinkedHashMap.empty[Space, Int]
    def id(sp: Space): Int = ids.getOrElseUpdate(sp, { SizeZ3.children(sp).foreach(id); ids.size })
    id(root)
    val nodes = ids.toVector.sortBy(_._2)
    val base = nodes.map((sp, _) => Lower.lenBounds(sp))
    val sizeB = nodes.map((sp, _) => Lower.sizeBounds(sp))
    val folded = nodes.map((sp, _) => groundFold(sp))
    // rest-binder refinement: a rest mention's paths are one head-group's tails of the source
    val restSrc = collection.mutable.Map.empty[SpaceMention, Space]
    for (sp, _) <- nodes do sp match
      case Space.Iteration(src, _, rest, _) if rest.s != "_" => restSrc(rest) = src
      case Space.Fold(src, _, _, _, rest, _, _) if rest.s != "_" => restSrc(rest) = src
      case _ => ()

    inline def lo(i: Int) = s"lo$i"
    inline def hi(i: Int) = s"hi$i"
    inline def emp(i: Int) = s"emp$i"
    def L(c: Space)(t: String) = s"(len${ids(c)} $t)"
    def NE(c: Space) = s"(not emp${ids(c)})"

    // expansion-cost estimate (memoized on ids); nodes over the cap degrade to interval predicates
    val cost = new Array[Long](nodes.length)
    val degraded = new Array[Boolean](nodes.length)
    for (sp, i) <- nodes do
      def c(x: Space): Long = cost(ids(x))
      val structural: Long = folded(i) match
        case Some((_, _, _, Some(d))) => d.length.toLong
        case Some(_) => 1L
        case None => sp match
          case Space.Union(a, b) => 1 + c(a) + c(b)
          case Space.Intersection(a, b) => 1 + c(a) + c(b)
          case Space.Fixpoint(init, _, b) => 1 + c(init) + c(b)
          case Space.Subtraction(a, _) => 1 + c(a)
          case Space.Restriction(x, _) => 1 + c(x)
          case Space.Raffination(x, _) => 1 + c(x)
          case Space.Range(x, _, _) => 1 + c(x)
          case Space.Wrap(a, p) => if Lower.pathItemLen(p).isDefined then 1 + c(a) else 1
          case Space.Unwrap(a, p) => if Lower.pathItemLen(p).isDefined then 1 + c(a) else 1
          case Space.TailsUnion(a) => 1 + c(a)
          case Space.TailsIntersection(a) => 1 + c(a)
          case Space.Iteration(_, _, _, b) => 1 + c(b)
          case Space.Fold(_, _, _, _, _, b, _) => 1 + c(b)
          case Space.Mention(m) if restSrc.contains(m) => 1 + c(restSrc(m))
          case Space.Literal(SpaceValue(ps)) => 1 + ps.iterator.map(_.items.length).toSet.size.toLong
          case _ => 1L
      degraded(i) = structural > ExpansionCap
      cost(i) = if degraded(i) then 1L else structural

    val sb = new StringBuilder
    sb ++= "(set-option :opt.priority box)\n"
    for (sp, i) <- nodes do
      sb ++= s"(declare-const lo$i Int)\n(declare-const hi$i Int)\n(declare-const emp$i Bool)\n"

      // the length predicate: folded-exact > degraded-interval > structural
      val body: String = folded(i) match
        case Some((true, _, _, _)) => "false"
        case Some((false, mn, mx, Some(d))) =>
          if d.length == 1 then s"(= l ${d.head})" else s"(or ${d.map(v => s"(= l $v)").mkString(" ")})"
        case Some((false, mn, mx, None)) => s"(and (>= l $mn) (<= l $mx))"
        case None if degraded(i) => s"(and (>= l lo$i) (<= l hi$i))"
        case None => sp match
          case Space.Empty => "false"
          case Space.Singleton(p) =>
            val k = Lower.pathLenBounds(p)
            if k.lo == k.hi then s"(= l ${k.lo})"
            else if k.hi == INF then s"(>= l ${k.lo})"
            else s"(and (>= l ${k.lo}) (<= l ${k.hi}))"
          case Space.Literal(SpaceValue(ps)) =>
            if ps.isEmpty then "false"
            else
              val d = ps.iterator.map(_.items.length.toLong).toVector.distinct.sorted
              if d.length == 1 then s"(= l ${d.head})"
              else if d.length <= LenSetCap then s"(or ${d.map(v => s"(= l $v)").mkString(" ")})"
              else s"(and (>= l ${d.head}) (<= l ${d.last}))"
          case Space.Union(a, b) => s"(or (and ${NE(a)} ${L(a)("l")}) (and ${NE(b)} ${L(b)("l")}))"
          case Space.Intersection(a, b) => s"(and ${NE(a)} ${NE(b)} ${L(a)("l")} ${L(b)("l")})"
          case Space.Subtraction(a, _) => s"(and ${NE(a)} ${L(a)("l")})"
          case Space.Restriction(x, y) => s"(and ${NE(x)} ${NE(y)} ${L(x)("l")} (>= l ${lo(ids(y))}))"
          case Space.Raffination(x, _) => s"(and ${NE(x)} ${L(x)("l")})"
          case Space.Composition(a, b) =>
            s"(and ${NE(a)} ${NE(b)} (>= l (+ ${lo(ids(a))} ${lo(ids(b))})) (<= l (+ ${hi(ids(a))} ${hi(ids(b))})))"
          case Space.Wrap(a, p) => Lower.pathItemLen(p) match
            case Some(k) => s"(and ${NE(a)} ${L(a)(s"(- l $k)")})"
            case None =>
              val kb = Lower.pathLenBounds(p)
              val up = if kb.hi == INF then "" else s" (<= l (+ ${kb.hi} ${hi(ids(a))}))"
              s"(and ${NE(a)} (>= l (+ ${kb.lo} ${lo(ids(a))}))$up)"
          case Space.Unwrap(a, p) => Lower.pathItemLen(p) match
            case Some(k) => s"(and ${NE(a)} ${L(a)(s"(+ l $k)")})"
            case None =>
              val kb = Lower.pathLenBounds(p)
              val lb = if kb.hi == INF then "" else s" (>= l (- ${lo(ids(a))} ${kb.hi}))"
              s"(and ${NE(a)} (>= l 0) (<= l (- ${hi(ids(a))} ${kb.lo}))$lb)"
          case Space.TailsUnion(a) => s"(and ${NE(a)} ${L(a)("(+ l 1)")})"
          case Space.TailsIntersection(a) => s"(and ${NE(a)} ${L(a)("(+ l 1)")})"
          case Space.Range(x, _, _) => s"(and ${NE(x)} ${L(x)("l")})"
          case Space.Iteration(_, _, _, b) => s"(and ${NE(b)} ${L(b)("l")})"
          case Space.Fold(_, _, _, _, _, b, _) => s"(and ${NE(b)} ${L(b)("l")})"
          case Space.Fixpoint(init, _, b) => s"(or (and ${NE(init)} ${L(init)("l")}) (and ${NE(b)} ${L(b)("l")}))"
          case Space.Mention(m) if restSrc.contains(m) =>
            val src = restSrc(m)
            s"(and ${NE(src)} ${L(src)("(+ l 1)")})"
          case _ => "(>= l 0)"   // free Mention / Call / Grounded: any lengths
      sb ++= s"(define-fun len$i ((l Int)) Bool $body)\n"

      // witnesses: when nonempty, the extreme lengths are realized lengths inside the baseline
      sb ++= s"(assert (=> (not emp$i) (and (>= lo$i 0) (<= lo$i hi$i) (len$i lo$i) (len$i hi$i))))\n"
      val b = base(i)
      if b.isEmpty then sb ++= s"(assert emp$i)\n"
      else
        if b.lo > 0 then sb ++= s"(assert (=> (not emp$i) (>= lo$i ${b.lo})))\n"
        if b.hi != INF then sb ++= s"(assert (=> (not emp$i) (<= hi$i ${b.hi})))\n"
      // size-analysis cross-facts: provable emptiness / nonemptiness
      if sizeB(i).hi == 0 then sb ++= s"(assert emp$i)\n"
      if sizeB(i).lo >= 1 then sb ++= s"(assert (not emp$i))\n"
      folded(i) match
        case Some((true, _, _, _)) => sb ++= s"(assert emp$i)\n"
        case Some((false, mn, mx, _)) => sb ++= s"(assert (and (not emp$i) (= lo$i $mn) (= hi$i $mx)))\n"
        case None => ()

      // structural emptiness facts (only the TRUE directions)
      sp match
        case Space.Empty => sb ++= s"(assert emp$i)\n"
        case Space.Singleton(_) => sb ++= s"(assert (not emp$i))\n"
        case Space.Literal(SpaceValue(ps)) => sb ++= s"(assert ${if ps.isEmpty then s"emp$i" else s"(not emp$i)"})\n"
        case Space.Union(a, b) => sb ++= s"(assert (= emp$i (and emp${ids(a)} emp${ids(b)})))\n"
        case Space.Intersection(a, b) => sb ++= s"(assert (=> (or emp${ids(a)} emp${ids(b)}) emp$i))\n"
        case Space.Subtraction(a, _) => sb ++= s"(assert (=> emp${ids(a)} emp$i))\n"
        case Space.Restriction(x, y) => sb ++= s"(assert (=> (or emp${ids(x)} emp${ids(y)}) emp$i))\n"
        case Space.Raffination(x, _) => sb ++= s"(assert (=> emp${ids(x)} emp$i))\n"
        case Space.Composition(a, b) => sb ++= s"(assert (= emp$i (or emp${ids(a)} emp${ids(b)})))\n"
        case Space.Wrap(a, _) => sb ++= s"(assert (= emp$i emp${ids(a)}))\n"
        case Space.Unwrap(a, _) => sb ++= s"(assert (=> emp${ids(a)} emp$i))\n"
        case Space.TailsUnion(a) =>
          sb ++= s"(assert (=> emp${ids(a)} emp$i))\n(assert (=> (and (not emp${ids(a)}) (= hi${ids(a)} 0)) emp$i))\n"
        case Space.TailsIntersection(a) =>
          sb ++= s"(assert (=> emp${ids(a)} emp$i))\n(assert (=> (and (not emp${ids(a)}) (= hi${ids(a)} 0)) emp$i))\n"
        case Space.Range(x, _, _) => sb ++= s"(assert (=> emp${ids(x)} emp$i))\n"
        case Space.Iteration(src, _, _, b) =>
          sb ++= s"(assert (=> emp${ids(src)} emp$i))\n(assert (=> (and (not emp${ids(src)}) (= hi${ids(src)} 0)) emp$i))\n"
          sb ++= s"(assert (=> emp${ids(b)} emp$i))\n"
        case Space.Fold(src, _, _, _, _, b, _) =>
          sb ++= s"(assert (=> emp${ids(src)} emp$i))\n(assert (=> (and (not emp${ids(src)}) (= hi${ids(src)} 0)) emp$i))\n"
          sb ++= s"(assert (=> emp${ids(b)} emp$i))\n"
        case Space.Fixpoint(init, _, b) =>
          sb ++= s"(assert (=> (not emp${ids(init)}) (not emp$i)))\n(assert (=> (and emp${ids(init)} emp${ids(b)}) emp$i))\n"
        case _ => ()

    val r = ids(root)
    sb ++= s"(assert (not emp$r))\n"                      // bounds quantify over paths: vacuous when ∅
    sb ++= s"(minimize lo$r)\n(maximize hi$r)\n(check-sat)\n(get-objectives)\n"
    Enc(sb.toString)

  /** box-mode objectives in declaration order: min lo, max hi (`oo` = unbounded). */
  private def parseObjectives(out: String): Option[(Option[Long], Option[Long])] =
    if !out.linesIterator.exists(_.trim == "sat") then return None
    val body = out.substring(out.indexOf("(objectives") match { case -1 => return None; case ix => ix })
    val vals = raw"\(\s*[^()\s]+\s+(\(- \d+\)|\(?-? ?oo\)?|\d+)\s*\)".r.findAllMatchIn(body).map(_.group(1)).toVector
    if vals.length != 2 then return None
    def num(v: String): Option[Long] =
      val t = v.trim
      if t.contains("oo") then None
      else if t.startsWith("(-") then Some(-t.stripPrefix("(-").stripSuffix(")").trim.toLong)
      else t.toLongOption
    Some((num(vals(0)), num(vals(1))))
end LenZ3
