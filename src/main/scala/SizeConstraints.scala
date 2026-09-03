package morkl

/** Tier 2 of the size analysis (design_size_constraints.md): translate the term's cardinality
 *  facts into a z3 OPTIMIZATION problem and read the root's size interval off the objectives.
 *
 *  Every distinct subterm (hash-consed by value, so the two `x` in `x ∪ (x∩y)` are ONE node)
 *  gets integer variables `n` (size) and `e ∈ {0,1}` (is ε in the result; the headed count is
 *  the derived `n − e`).  Constraints are the per-constructor cardinality laws of the design doc
 *  plus the saturated subset relation (⊑) — the piece the compositional baseline cannot see.
 *  The system stays LINEAR: multiplicative bounds use the baseline's constant endpoints as
 *  coefficients, never a product of two variables.
 *
 *  The baseline interval of EVERY node is asserted into the system, so the optimum can only be
 *  equal or tighter than [[Lower.sizeBounds]]; on any failure (no z3, scoping ambiguity, timeout,
 *  unsat, parse) the baseline is returned unchanged — tighter everywhere, unsound nowhere,
 *  by construction *given* each emitted constraint is a true cardinality law (each is either
 *  certified in proofs/laws or a direct set fact; the corpus gate re-checks empirically).
 *
 *  Binder discipline: variables stand for "the value of this subterm under ANY binding", and the
 *  min/max objectives treat them adversarially, which is sound for interval extraction as long as
 *  no variable is forced to stand for two DIFFERENT bindings at once.  `scopesOk` therefore
 *  rejects terms where hash-consing could conflate scopes (duplicate binder names, a binder name
 *  also used free, or a referenced `_` binder) — those fall back to the baseline. */
object SizeZ3:
  import Lower.SizeBounds
  private val INF = SizeBounds.INF

  /** How a bounds query was answered.  `Solved` dominates the baseline by construction; every
   *  other status means the answer IS the baseline — reported, not hidden, so measurement can
   *  show the limits in scope instead of silently mixing in the syntactic approximation. */
  enum Status:
    case Solved
    /** SOME objectives were established and the rest kept their baseline endpoint: the answer is
     *  still sound and still dominates the baseline, but it is not the full optimum, so it is
     *  reported separately rather than passed off as `Solved`. */
    case PartiallySolved(detail: String)
    case ScopeLimited(reason: String)
    case NoSolver
    case SolverFailed(detail: String)

  /** is a usable z3 available?  Resolved once by [[Tools]] ($Z3, then PATH, then the conventional
   *  locations) — never by an absolute path baked into this file. */
  lazy val available: Boolean = Tools.z3.isAvailable

  def bounds(s: Space, timeoutSec: Int = 8): SizeBounds = boundsWithStatus(s, timeoutSec)._1

  /** `rc` makes the per-node BASELINE seeds interprocedural (Call parameters bound to argument
   *  bounds), so this tier stays at least as tight as tier-1 when a routine table is available. */
  def boundsWithStatus(s0: Space, timeoutSec: Int = 8,
                       rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): (SizeBounds, Status) =
    val base = Lower.sizeBounds(s0, rc)
    if !available then return (base, Status.NoSolver)
    val s = alphaRename(s0)   // binder reuse (e.g. both GoL arms binding `ys`) must not block encoding
    scopesProblem(s) match
      case Some(reason) => (base, Status.ScopeLimited(reason))
      case None =>
        try
          val enc = encode(s, rc)
          // Each objective gets its OWN solver call.  z3's box-mode multi-objective search was the
          // dominant cost, not the constraint system: on the expanded n-queens one box solve took
          // 12.2s while the three single-objective solves take ~1.7s together, and the expanded
          // puzzle-3 went from a hard timeout to a complete answer that also BEATS the baseline
          // upper (17445 vs 18469).  A per-objective failure degrades that one endpoint to the
          // baseline instead of losing the whole query.
          val lo = solveObjective(enc, s"(minimize ${enc.root})", timeoutSec)
          val hi = solveObjective(enc, s"(maximize ${enc.root})", timeoutSec)
          val loHd = solveObjective(enc, s"(minimize ${enc.hdRoot})", timeoutSec)
          if lo.isEmpty && hi.isEmpty && loHd.isEmpty then (base, Status.SolverFailed("all objectives failed"))
          else
            val hi2 = hi.flatten.fold(base.hi)(h => h min base.hi)
            val lo2 = (lo.flatten.getOrElse(0L) max base.lo) min hi2
            val loHd2 = (loHd.flatten.getOrElse(0L) max base.loHeaded) min lo2
            val missing = List(("min" -> lo), ("max" -> hi), ("minHd" -> loHd)).collect { case (k, None) => k }
            val st = if missing.isEmpty then Status.Solved
                     else Status.PartiallySolved(s"kept baseline for ${missing.mkString(",")}")
            (SizeBounds(lo2, loHd2, hi2), st)
        catch case e: Throwable => (base, Status.SolverFailed(e.getClass.getSimpleName))

  // ---- α-renaming ---------------------------------------------------------------------------
  /** Rename every binder apart (post-order, so an inner binder shadowing the same name is
   *  renamed first and the outer substitution cannot capture).  α-equivalence preserves sizes,
   *  and unique binders are what make value-level hash-consing scope-safe. */
  private[morkl] def alphaRename(root: Space): Space =
    var k = 0
    def freshP(old: PathRef): PathRef =
      k += 1
      if old.lengthHint >= 0 then PathRef(s"~a$k").known(old.lengthHint) else PathRef(s"~a$k")
    def freshM(old: SpaceMention): SpaceMention =
      k += 1
      if old.sizeHint >= 0 then SpaceMention(s"~m$k").known(old.sizeHint) else SpaceMention(s"~m$k")
    def go(sp: Space): Space = sp match
      case Space.Iteration(src, sym, rest, b) =>
        val b1 = go(b)
        val (ns, nr) = (freshP(sym), freshM(rest))
        // THROUGH `Subst`, and SIMULTANEOUSLY.  This is an alpha-rename, i.e. a substitution of a
        // name by a name, and the blind `subs` walker got the right answer here only BY ACCIDENT OF
        // ORDER: `go(b)` runs FIRST and bottom-up, so every inner binder has already been renamed to
        // a fresh `~m`/`~p` by the time the outer rename descends, and there is nothing left for it
        // to shadow.  That is a real argument but it was nowhere written down, and it evaporates the
        // moment someone makes this pass top-down.  `Subst` honours shadowing itself, so the
        // correctness stops depending on the traversal order.  The two maps also go in ONE call:
        // renaming `rest` and `sym` in two passes is sequential composition, and `Path.Deref(ns)`
        // could be reached by the second pass if `ns` collided with `rest`'s replacement.
        Space.Iteration(go(src), ns, nr,
          Subst(b1, Map(rest -> Space.Mention(nr)), Map(sym -> Path.Deref(ns))))
      case Space.Fold(src, init, acc, sym, rest, b, upd) =>
        val b1 = go(b)
        val nr = freshM(rest)
        Space.Fold(go(src), init, acc, sym, nr,
          Subst.mention(b1, rest, Space.Mention(nr)), upd)
      case Space.Fixpoint(init, rec, b) =>
        val b1 = go(b)
        val nr = freshM(rec)
        Space.Fixpoint(go(init), nr,
          Subst.mention(b1, rec, Space.Mention(nr)))
      case Space.Union(a, b) => Space.Union(go(a), go(b))
      case Space.Intersection(a, b) => Space.Intersection(go(a), go(b))
      case Space.Subtraction(a, b) => Space.Subtraction(go(a), go(b))
      case Space.Restriction(a, b) => Space.Restriction(go(a), go(b))
      case Space.Raffination(a, b) => Space.Raffination(go(a), go(b))
      case Space.Composition(a, b) => Space.Composition(go(a), go(b))
      case Space.Wrap(a, pp) => Space.Wrap(go(a), pp)
      case Space.Unwrap(a, pp) => Space.Unwrap(go(a), pp)
      case Space.TailsUnion(a) => Space.TailsUnion(go(a))
      case Space.TailsIntersection(a) => Space.TailsIntersection(go(a))
      case Space.Range(a, x, y) => Space.Range(go(a), x, y)
      case other => other
    go(root)

  // ---- scoping validation -------------------------------------------------------------------
  /** binder names must be globally unique, never also occur free, and `_` binders never
   *  referenced — otherwise value-level hash-consing would conflate distinct bindings.
   *  Returns the FIRST problem (for the limits-in-scope report), or None when encodable. */
  private[morkl] def scopesProblem(s: Space): Option[String] =
    // a binder name may recur ONLY as value-identical copies of the same binding subtree (pooled
    // reuse duplicates whole subtrees; hash-consing maps them to one node, so nothing conflates) —
    // two DIFFERENT subtrees sharing a binder name would merge distinct bindings.
    val binderAt = collection.mutable.Map.empty[String, Space]
    var dup: Option[String] = None
    def binderNames(sp: Space): Unit = if dup.isEmpty then sp match
      case it @ Space.Iteration(src, _, rest, b) =>
        if rest.s != "_" && binderAt.getOrElseUpdate(rest.s, it) != it then dup = Some(rest.s)
        binderNames(src); binderNames(b)
      case fo @ Space.Fold(src, _, _, _, rest, b, _) =>
        if rest.s != "_" && binderAt.getOrElseUpdate(rest.s, fo) != fo then dup = Some(rest.s)
        binderNames(src); binderNames(b)
      case fx @ Space.Fixpoint(init, rec, b) =>
        if rec.s != "_" && binderAt.getOrElseUpdate(rec.s, fx) != fx then dup = Some(rec.s)
        binderNames(init); binderNames(b)
      case other => children(other).foreach(binderNames)
    binderNames(s)
    dup match
      case Some(d) => return Some(s"binder '$d' names two distinct subtrees")
      case None => ()
    val bset = binderAt.keySet.toSet
    var problem: Option[String] = None
    def walk(sp: Space, bound: Set[String]): Unit = if problem.isEmpty then sp match
      case Space.Mention(m) =>
        if m.s == "_" then problem = Some("mention of throwaway binder '_'")
        else if bset(m.s) && !bound(m.s) then problem = Some(s"binder '${m.s}' referenced outside its scope")
      case Space.Iteration(src, _, rest, b) => walk(src, bound); walk(b, bound + rest.s)
      case Space.Fold(src, _, _, _, rest, b, _) => walk(src, bound); walk(b, bound + rest.s)
      case Space.Fixpoint(init, rec, b) => walk(init, bound); walk(b, bound + rec.s)
      case other => children(other).foreach(walk(_, bound))
    walk(s, Set.empty)
    problem

  private[morkl] def children(s: Space): List[Space] = s match
    case Space.Union(a, b) => List(a, b)
    case Space.Intersection(a, b) => List(a, b)
    case Space.Subtraction(a, b) => List(a, b)
    case Space.Restriction(a, b) => List(a, b)
    case Space.Raffination(a, b) => List(a, b)
    case Space.Composition(a, b) => List(a, b)
    case Space.Wrap(a, _) => List(a)
    case Space.Unwrap(a, _) => List(a)
    case Space.TailsUnion(a) => List(a)
    case Space.TailsIntersection(a) => List(a)
    case Space.Range(a, _, _) => List(a)
    case Space.Iteration(src, _, _, b) => List(src, b)
    case Space.Fold(src, _, _, _, _, b, _) => List(src, b)
    case Space.Fixpoint(init, _, b) => List(init, b)
    case Space.Call(_, _, ms) => ms.toList
    case Space.GroundedSS(a, _) => List(a)
    case _ => Nil

  /** the lowered SMT text (diagnostics/tooling) — exactly what the solver sees */
  private[morkl] def encodeText(s: Space): String = encode(s).text

  // ---- encoding -------------------------------------------------------------------------------
  /** the assertion body (no objectives) plus the root's variable names; each objective is solved
   *  in its OWN solver call — see [[solveObjective]] for why. */
  private final case class Enc(body: String, root: String, hdRoot: String):
    /** the full text for ONE objective, so a caller can see exactly what the solver saw */
    def text(objective: String): String = s"$body$objective\n(check-sat)\n(get-objectives)\n"
    def text: String = text(s"(minimize $root)")

  private def encode(root: Space, rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Enc =
    val ids = collection.mutable.LinkedHashMap.empty[Space, Int]
    def id(sp: Space): Int = ids.getOrElseUpdate(sp, { children(sp).foreach(id); ids.size })
    id(root)
    val nodes = ids.toVector.sortBy(_._2)
    val base = nodes.map((sp, _) => Lower.sizeBounds(sp, rc))
    inline def n(i: Int) = s"n$i"
    inline def e(i: Int) = s"e$i"
    inline def hd(i: Int) = s"(- n$i e$i)"

    val sb = new StringBuilder
    for (_, i) <- nodes do
      sb ++= s"(declare-const n$i Int)\n(declare-const e$i Int)\n"
      sb ++= s"(assert (and (>= e$i 0) (<= e$i 1) (<= e$i n$i)))\n"
      val b = base(i)
      sb ++= s"(assert (>= n$i ${b.lo}))\n"                     // baseline/folded seeds ⇒ never looser
      if b.hi != INF then sb ++= s"(assert (<= n$i ${b.hi}))\n"
      if b.loHeaded > 0 then sb ++= s"(assert (>= ${hd(i)} ${b.loHeaded}))\n"

    // subset relation: structural seeds + glb/lub/transitive/wrap-congruence closure
    val sub = collection.mutable.Set.empty[(Int, Int)]        // (t, s): t ⊑ s
    def addSub(t: Int, u: Int): Boolean = t != u && sub.add((t, u))
    for (sp, i) <- nodes do sp match
      case Space.Intersection(a, b) => addSub(i, ids(a)); addSub(i, ids(b))
      case Space.Subtraction(a, _) => addSub(i, ids(a))
      case Space.Restriction(a, _) => addSub(i, ids(a))
      case Space.Raffination(a, _) => addSub(i, ids(a))
      case Space.Union(a, b) => addSub(ids(a), i); addSub(ids(b), i)
      case Space.Range(a, x, y) => if !(x == 0 && y == 0) then addSub(i, ids(a)) else { addSub(i, ids(a)); addSub(ids(a), i) }
      case Space.Fixpoint(init, _, _) => addSub(ids(init), i)
      case _ => ()
    val wrapsByPath = nodes.collect { case (w @ Space.Wrap(a, p), i) => (p, ids(a), i) }
    var grew = true
    while grew do
      grew = false
      val cur = sub.toVector
      for (a, b) <- cur; (b2, c) <- cur if b == b2 do grew |= addSub(a, c)          // transitivity
      for (sp, i) <- nodes do sp match
        case Space.Intersection(a, b) =>                                            // glb
          val (ia, ib) = (ids(a), ids(b))
          for (c, a2) <- cur if a2 == ia && (sub((c, ib)) || c == ib) do grew |= addSub(c, i)
          for (c, b2) <- cur if b2 == ib && (sub((c, ia)) || c == ia) do grew |= addSub(c, i)
          if ia == ib then grew |= addSub(ia, i)                 // x∩x ⊒ x
          if sub((ia, ib)) then grew |= addSub(ia, i)            // a ⊑ b ⟹ a ⊑ a∩b
          if sub((ib, ia)) then grew |= addSub(ib, i)            // b ⊑ a ⟹ b ⊑ a∩b
        case Space.Union(a, b) =>                                                   // lub
          val (ia, ib) = (ids(a), ids(b))
          for (a2, c) <- cur if a2 == ia && (sub((ib, c)) || ib == c) do grew |= addSub(i, c)
          if ia == ib then grew |= addSub(i, ia)                 // x∪x ⊑ x
          if sub((ia, ib)) then grew |= addSub(i, ib)            // a ⊑ b ⟹ a∪b ⊑ b
          if sub((ib, ia)) then grew |= addSub(i, ia)            // b ⊑ a ⟹ a∪b ⊑ a
        case _ => ()
      for (p1, a1, w1) <- wrapsByPath; (p2, a2, w2) <- wrapsByPath
          if w1 != w2 && p1 == p2 && sub((a1, a2)) do grew |= addSub(w1, w2)        // wrap congruence
    // Emit the TRANSITIVE REDUCTION, not the closure.  The closure is needed INTERNALLY (the
    // glb/lub rules and `uppersOf`/`common` below read it), but every edge implied by a two-step
    // path is derivable by the solver's own arithmetic transitivity, so emitting it only adds
    // redundant rows: on the expanded puzzle-3 that is 2505 edges cut to 218, on n-queens 494 to
    // 136, and the reduced system solves several times faster.
    val succ: Map[Int, Set[Int]] = sub.toVector.groupMap(_._1)(_._2).view.mapValues(_.toSet).toMap
    val reduction = sub.filterNot { (a, c) =>
      succ.getOrElse(a, Set.empty).exists(b => b != c && b != a && succ.getOrElse(b, Set.empty).contains(c))
    }
    for (t, u) <- reduction do
      sb ++= s"(assert (<= ${n(t)} ${n(u)}))\n(assert (<= ${e(t)} ${e(u)}))\n"
    val uppersOf: Map[Int, Set[Int]] = succ

    val restrictionAt = nodes.collect { case (Space.Restriction(x, y), i) => ((x, y), i) }.toMap
    val interAt = nodes.collect { case (Space.Intersection(a, b), i) => ((a, b), i) }.toMap
    def meetOf(a: Space, b: Space): Option[Int] = interAt.get((a, b)).orElse(interAt.get((b, a)))
    def partitionPair(a: Space, b: Space): Option[Space] = (a, b) match   // {x<|y, x\|y} ⊎-partition x
      case (Space.Restriction(x1, y1), Space.Raffination(x2, y2)) if x1 == x2 && y1 == y2 => Some(x1)
      case (Space.Raffination(x1, y1), Space.Restriction(x2, y2)) if x1 == x2 && y1 == y2 => Some(x1)
      case _ => None
    def isConstHeadWrap(sp: Space): Option[PathItem] = sp match
      case Space.Wrap(_, Path.Constant(PathValue(h :: _))) => Some(h)
      case _ => None

    for (sp, i) <- nodes do
      def N(c: Space) = n(ids(c)); def E(c: Space) = e(ids(c)); def HD(c: Space) = hd(ids(c))
      def K(c: Space): Long = base(ids(c)).hi
      sp match
        case Space.Empty => sb ++= s"(assert (= n$i 0))\n"
        case Space.Singleton(p) =>
          sb ++= s"(assert (= n$i 1))\n"
          if Lower.pathHeaded(p) then sb ++= s"(assert (= e$i 0))\n"
          else if Lower.pathItemLen(p).contains(0) then sb ++= s"(assert (= e$i 1))\n"
        case Space.Literal(SpaceValue(ps)) =>
          sb ++= s"(assert (= n$i ${ps.size}))\n(assert (= e$i ${if ps.contains(PathValue(Nil)) then 1 else 0}))\n"
        case Space.Union(a, b) =>
          sb ++= s"(assert (<= n$i (+ ${N(a)} ${N(b)})))\n"
          sb ++= s"(assert (>= n$i ${N(a)}))\n(assert (>= n$i ${N(b)}))\n"
          sb ++= s"(assert (<= e$i (+ ${E(a)} ${E(b)})))\n"    // e = ea ∨ eb (≥ via ⊑ seeds)
          (isConstHeadWrap(a), isConstHeadWrap(b)) match       // disjoint cylinders: exact sum
            case (Some(h1), Some(h2)) if h1 != h2 => sb ++= s"(assert (= n$i (+ ${N(a)} ${N(b)})))\n"
            case _ => ()
          partitionPair(a, b).foreach(x => sb ++= s"(assert (= n$i ${N(x)}))\n")
          meetOf(a, b).foreach(m => sb ++= s"(assert (= n$i (- (+ ${N(a)} ${N(b)}) ${n(m)})))\n")  // |a∪b| = |a|+|b|−|a∩b|
        case Space.Intersection(a, b) =>
          sb ++= s"(assert (>= e$i (- (+ ${E(a)} ${E(b)}) 1)))\n"
          val (ia, ib) = (ids(a), ids(b))
          val common = (uppersOf.getOrElse(ia, Set.empty) + ia) intersect (uppersOf.getOrElse(ib, Set.empty) + ib)
          for u <- common.toVector.sorted.take(6) do
            sb ++= s"(assert (>= n$i (- (+ ${N(a)} ${N(b)}) ${n(u)})))\n"  // e = ea ∧ eb (≤ via ⊑)
        case Space.Subtraction(a, b) =>
          sb ++= s"(assert (>= n$i (- ${N(a)} ${N(b)})))\n"
          sb ++= s"(assert (>= e$i (- ${E(a)} ${E(b)})))\n(assert (<= e$i (- 1 ${E(b)})))\n"
          if sub((ids(a), ids(b))) then sb ++= s"(assert (= n$i 0))\n"  // a ⊑ b ⟹ a∖b = ∅
          meetOf(a, b).foreach(m => sb ++= s"(assert (= n$i (- ${N(a)} ${n(m)})))\n")  // |a∖b| = |a|−|a∩b|
        case Space.Restriction(x, y) =>
          sb ++= s"(assert (>= e$i (- (+ ${E(x)} ${E(y)}) 1)))\n(assert (<= e$i ${E(y)}))\n"
          sb ++= s"(assert (=> (= ${N(y)} 0) (= n$i 0)))\n"
        case Space.Raffination(x, y) =>
          sb ++= s"(assert (<= e$i (- 1 ${E(y)})))\n(assert (>= e$i (- ${E(x)} ${E(y)})))\n"
          sb ++= s"(assert (=> (= ${N(y)} 0) (= n$i ${N(x)})))\n"
          restrictionAt.get((x, y)).foreach(r => sb ++= s"(assert (= (+ n$i ${n(r)}) ${N(x)}))\n")  // partition
        case Space.Composition(a, b) =>
          if K(b) != INF then sb ++= s"(assert (<= n$i (* ${N(a)} ${K(b)})))\n"
          if K(a) != INF then sb ++= s"(assert (<= n$i (* ${K(a)} ${N(b)})))\n"
          sb ++= s"(assert (=> (and (>= ${N(a)} 1) (>= ${N(b)} 1)) (and (>= n$i ${N(a)}) (>= n$i ${N(b)}))))\n"
          sb ++= s"(assert (=> (or (= ${N(a)} 0) (= ${N(b)} 0)) (= n$i 0)))\n"
          sb ++= s"(assert (>= e$i (- (+ ${E(a)} ${E(b)}) 1)))\n(assert (<= e$i ${E(a)}))\n(assert (<= e$i ${E(b)}))\n"
        case Space.Wrap(a, p) =>
          sb ++= s"(assert (= n$i ${N(a)}))\n"
          if Lower.pathHeaded(p) then sb ++= s"(assert (= e$i 0))\n"
          else if Lower.pathItemLen(p).contains(0) then sb ++= s"(assert (= e$i ${E(a)}))\n"
        case Space.Unwrap(a, _) =>
          sb ++= s"(assert (<= n$i ${N(a)}))\n(assert (=> (= ${N(a)} 0) (= n$i 0)))\n"
        case Space.TailsUnion(a) =>
          sb ++= s"(assert (<= n$i ${HD(a)}))\n"               // one tail per HEADED path, deduped
          sb ++= s"(assert (=> (>= ${HD(a)} 1) (>= n$i 1)))\n"
        case Space.TailsIntersection(a) =>
          sb ++= s"(assert (<= n$i ${N(a)}))\n(assert (=> (= ${HD(a)} 0) (= n$i 0)))\n"
        case Space.Range(a, x, y) =>
          if x == 0 && y == 0 then sb ++= s"(assert (= n$i ${N(a)}))\n(assert (= e$i ${E(a)}))\n"
          else
            val window = if x == 0 && y > 0 then Some(y.toLong) else if y == 0 && x < 0 then Some(-x.toLong) else None
            window match
              case Some(w) => sb ++= s"(assert (= n$i (ite (<= ${N(a)} $w) ${N(a)} $w)))\n"  // exactly min(size, w)
              case None =>
                sb ++= s"(assert (<= n$i ${N(a)}))\n"
                // same-sign slice: width ≤ y − x (the exactly-k idiom is Range(count, k, k+1))
                if (x > 0 && y >= x) || (x < 0 && y <= 0 && y >= x) then
                  sb ++= s"(assert (<= n$i ${(y - x).toLong}))\n"
        case Space.Iteration(src, _, rest, body) =>
          ids.get(Space.Mention(rest)).foreach(m => sb ++= s"(assert (<= ${n(m)} ${N(src)}))\n")
          sb ++= s"(assert (=> (= ${HD(src)} 0) (= n$i 0)))\n"
          // body variables denote the ARGMAX-body group's binding (a valid witness), so both the
          // lower bound (⊇ that group's body) and the linear dual uppers hold together:
          sb ++= s"(assert (=> (>= ${HD(src)} 1) (>= n$i ${N(body)})))\n"
          if K(body) != INF then sb ++= s"(assert (<= n$i (* ${HD(src)} ${K(body)})))\n"
          if K(src) != INF then sb ++= s"(assert (<= n$i (* ${K(src)} ${N(body)})))\n"   // const·VARIABLE
        case Space.Fold(src, _, _, _, _, body, _) =>
          if K(body) != INF then sb ++= s"(assert (<= n$i (* ${HD(src)} ${K(body)})))\n"
          if K(src) != INF then sb ++= s"(assert (<= n$i (* ${K(src)} ${N(body)})))\n"
        case Space.Fixpoint(init, _, _) =>
          sb ++= s"(assert (>= n$i ${N(init)}))\n(assert (>= e$i ${E(init)}))\n"
        case Space.Mention(_) | Space.Call(_, _, _) | Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => ()

    val r = ids(root)
    sb ++= s"(declare-const hdroot Int)\n(assert (= hdroot (- n$r e$r)))\n"
    Enc(sb.toString, n(r), "hdroot")

  // ---- z3 plumbing ----------------------------------------------------------------------------
  /** Solve ONE objective.  `None` = this endpoint could not be established (timeout/unknown/parse
   *  failure) and the caller keeps the baseline for it; `Some(None)` = the objective is unbounded. */
  private def solveObjective(enc: Enc, objective: String, timeoutSec: Int): Option[Option[Long]] =
    val out = runZ3(enc.text(objective), timeoutSec)
    if !out.linesIterator.exists(_.trim == "sat") then None else parseObjective(out)

  /** the single value of a one-objective `(get-objectives)` block; `oo` ⇒ unbounded ⇒ Some(None) */
  private def parseObjective(out: String): Option[Option[Long]] =
    val ix = out.indexOf("(objectives")
    if ix < 0 then return None
    val body = out.substring(ix)
    raw"\(\s*[^()\s]+\s+(\(- \d+\)|\(?\*? ?\(?-? ?1?\)? ?oo\)?|-?\d+)\s*\)".r.findFirstMatchIn(body).map(_.group(1)) match
      case None => None
      case Some(v) =>
        val t = v.trim
        if t.contains("oo") then Some(None)
        else if t.startsWith("(-") then Some(Some(-t.stripPrefix("(-").stripSuffix(")").trim.toLong))
        else t.toLongOption.map(Some(_))

  private[morkl] def runZ3(smt: String, timeoutSec: Int): String =
    val f = java.io.File.createTempFile("sizebounds", ".smt2")
    try
      val w = new java.io.FileWriter(f); try w.write(smt) finally w.close()
      val p = new ProcessBuilder(Tools.z3.require(), s"-T:$timeoutSec", f.getPath)
        .redirectErrorStream(true).start()
      val out = new String(p.getInputStream.readAllBytes())
      p.waitFor()
      out
    finally f.delete()

  /** box-mode objectives arrive in declaration order: min n, max n, min (n − e).
   *  `oo` / `(- oo)` mean unbounded; any other shape aborts to the baseline. */
  private def parseObjectives(out: String): Option[(Option[Long], Option[Long], Option[Long])] =
    if !out.linesIterator.exists(_.trim == "sat") then return None
    val body = out.substring(out.indexOf("(objectives") match { case -1 => return None; case ix => ix })
    val vals = raw"\(\s*[^()\s]+\s+(\(- \d+\)|\(?-? ?oo\)?|\d+)\s*\)".r.findAllMatchIn(body).map(_.group(1)).toVector
    if vals.length != 3 then return None
    def num(v: String): Option[Long] =
      val t = v.trim
      if t.contains("oo") then None
      else if t.startsWith("(-") then Some(-t.stripPrefix("(-").stripSuffix(")").trim.toLong)
      else t.toLongOption
    Some((num(vals(0)), num(vals(1)), num(vals(2))))
end SizeZ3
