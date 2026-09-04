package morkl

/** The automated equivalence pipeline: Scala programs → egg (equivalence under the certified
 *  rewrite systems) and → z3/vampire (equal outputs for equal inputs, ∀ paths).
 *
 *  Three stages per program instance (program + concrete inputs):
 *    1. SPACE/TERM:   the program vs its Space-level optimisation (`SC.reduce`)
 *    2. ZIPPER:       the Scala zipper program (`transpileZ`) vs the Space/term program
 *    3. TRIE/GRAPH:   the optimised op-graph (`optimize(transpile(..))`) vs the Space/term program
 *  each proved (a) in egg — under formal.egg (set-of-paths reference), zipper.egg (movement spec)
 *  and the bridge (impl) rewrite systems — and (b) in z3+vampire — both sides compiled to their
 *  denotational membership formulas and proved equal for every path.
 *
 *  CONTROL FLOW (Iteration/Fixpoint/Fold/Call/Range) is expanded by [[expand]] before proving:
 *  every expansion step IS the corresponding `exec` evaluation rule for that node (iteration =
 *  union over the source's head groups; fixpoint = unrolling to its convergence depth; call =
 *  argument substitution + eval's stabilised-argument termination rule; Range = the trusted
 *  ordered-slice step, evaluated by the Scala executor and emitted as a literal).  The expansion
 *  is the TRUSTED boundary: what the proofs certify is that the (large) residual local-algebra
 *  programs — where all the set computation happens — are equivalent in all three notions. */
object EquivPipeline:
  import Space.*

  /** The FIRST-ORDER prelude shared by every pipeline SMT file: Path as a datatype and
   *  append/isPrefix as QUANTIFIED AXIOMS (no define-fun-rec/match — vampire does not unfold
   *  those), plus the certified lemma set (append-cons split, append-nil) that lets BOTH z3 and
   *  vampire discharge the equivalences in plain FOL, including for variable-input programs. */
  /** The prelude in three independently-includable blocks.  `append` is reachable only from
   *  `Composition`, `isPrefix` only from `Restriction`/`Raffination`; a file using neither carried
   *  SIX unused quantified axioms (one with a nested existential) — pure saturation fuel for
   *  vampire, and exactly the noise that hid the old degenerate files' PRELUDE-INDEPENDENCE
   *  (plan item 12: stripping the whole prelude left every one of the 18 instance files still
   *  `unsat`).  [[prunedPrelude]] keeps only the blocks a given body actually mentions. */
  val preludeDatatype: String = """(declare-datatypes ((Path 0)) (((nil) (cons (hd Int) (tl Path)))))"""
  val preludeAppend: String = """(declare-fun append (Path Path) Path)
(assert (forall ((q Path)) (= (append nil q) q)))
(assert (forall ((h Int) (t Path) (q Path)) (= (append (cons h t) q) (cons h (append t q)))))
; certified lemmas (proofs/lemma_append_cons.smt2, proofs/lemma_append_nil.smt2 — both PROVED)
(assert (forall ((k2 Int) (p Path) (q Path) (r Path))
  (= (= (cons k2 p) (append q r))
     (or (and (= q nil) (= r (cons k2 p)))
         (exists ((q2 Path)) (and (= q (cons k2 q2)) (= p (append q2 r))))))))
(assert (forall ((q Path)) (= (append q nil) q)))"""
  val preludeIsPrefix: String = """(declare-fun isPrefix (Path Path) Bool)
(assert (forall ((p Path)) (isPrefix nil p)))
(assert (forall ((h Int) (t Path)) (not (isPrefix (cons h t) nil))))
(assert (forall ((h Int) (t Path) (h2 Int) (t2 Path))
  (= (isPrefix (cons h t) (cons h2 t2)) (and (= h h2) (isPrefix t t2)))))"""

  /** the FULL prelude (every block) — the data-agnostic legs quantify over free inputs, so they
   *  cannot decide statically which operators a model will need. */
  val foPrelude: String =
    s"$preludeDatatype\n$preludeAppend\n$preludeIsPrefix\n"

  /** the datatype plus exactly the axiom blocks `body` (the emitted defs + goal) refers to. */
  def prunedPrelude(body: String): String =
    (preludeDatatype ::
      (if body.contains("append") then List(preludeAppend) else Nil) :::
      (if body.contains("isPrefix") then List(preludeIsPrefix) else Nil)).mkString("\n") + "\n"



  // ==============================================================================================
  // Stage 0 — control-flow expansion to pure local algebra over literals
  // ==============================================================================================
  def expand(s: Space)(using pc: PathContext, sc: SpaceContext, rc: PartialFunction[RoutinePtr, Routine]): Space =
    def pv(x: Path): PathValue = PathValue(eval(Space.Singleton(x)).paths.head.items)
    s match
      case Empty => Empty
      case Literal(v) => Literal(v)
      case Mention(m) => Literal(sc.resolve(m))
      case Singleton(p) => Singleton(Path.Constant(pv(p)))
      case Union(a, b) => Union(expand(a), expand(b))
      case Intersection(a, b) => Intersection(expand(a), expand(b))
      case Subtraction(a, b) => Subtraction(expand(a), expand(b))
      case Restriction(a, b) => Restriction(expand(a), expand(b))
      case Raffination(a, b) => Raffination(expand(a), expand(b))
      case Composition(a, b) => Composition(expand(a), expand(b))
      case Wrap(src, p) => Wrap(expand(src), Path.Constant(pv(p)))
      case Unwrap(src, p) => Unwrap(expand(src), Path.Constant(pv(p)))
      case TailsUnion(src) => TailsUnion(expand(src))
      case TailsIntersection(src) => TailsIntersection(expand(src))
      // obligation: terminating/REGISTRY.tsv O9c — the head-group union is `proofs/keyfold_iter.smt2`
      case Iteration(src, sym, rest, body) =>                 // exec's rule: union over head groups
        val srcE = expand(src)
        val groups = eval(srcE).paths.collect { case PathValue(h :: t) => (h, PathValue(t)) }.groupMap(_._1)(_._2)
        val parts = groups.toList.sortBy(_._1).map { (h, tails) =>
          expand(body)(using pc.grown(Map(sym -> PathValue(h :: Nil))),
                        sc.grown(Map(rest -> SpaceValue(tails.toSet))), rc)
        }
        if parts.isEmpty then Empty else parts.reduceLeft(Union.apply)
      // obligation: terminating/fixpoint_is_lfp.smt2 (O1, O9a) — this loop IS the two-sequence
      // Kleene recurrence that file axiomatises, so `expand` computes the same limit `eval` does
      case Fixpoint(init, rec, body) =>                       // exec's rule: unroll to convergence
        val initE = expand(init)
        var cur = eval(initE)
        var acc: Space = initE
        var done = false
        while !done do
          val nxtE = expand(body)(using pc, sc.grown(Map(rec -> cur)), rc)
          val nxt = eval(nxtE)
          if nxt == cur then done = true else { acc = Union(acc, nxtE); cur = nxt }
        acc
      case Fold(src, initial, accR, sym, rest, body, update) => // exec's rule: eager sorted fold
        val srcE = expand(src)
        val groups = eval(srcE).paths.collect { case PathValue(h :: t) => (PathValue(h :: Nil), PathValue(t)) }.groupMap(_._1)(_._2)
        var accV = PathValue(eval(Singleton(initial)).paths.head.items)
        var out: Space = Empty
        for (h, tails) <- groups.toList.sortBy(_._1.show) do
          val pctx = pc.grown(Map(accR -> accV, sym -> h)); val sctx = sc.grown(Map(rest -> SpaceValue(tails.toSet)))
          out = Union(out, expand(body)(using pctx, sctx, rc))
          accV = PathValue(eval(Singleton(update))(using pctx, sctx, rc).paths.head.items)
        out
      case Call(rp, refs, mentions) =>                        // eval's rule incl. stabilised-arg termination
        val refvs = refs.map(p => PathValue(eval(Singleton(p)).paths.head.items))
        val mentionEs = mentions.map(expand)
        val mentionVs = mentionEs.map(e => eval(e))
        val Routine(_, refns, mentionns, body) = rc(rp)
        val pctx = PathContextMap(Map.from(refns zip refvs))
        val sctx = SpaceContextMap(Map.from(mentionns zip mentionVs))
        body match
          case Union(l, Call(`rp`, `refs`, `mentions`))
            if (refs zip refvs).forall((p, v) => v == PathValue(eval(Singleton(p))(using pctx, sctx, rc).paths.head.items)) &&
               (mentions zip mentionVs).forall((m, v) => v == eval(m)(using pctx, sctx, rc)) =>
            expand(l)(using pctx, sctx, rc)
          case _ => expand(body)(using pctx, sctx, rc)
      case other =>                                           // Range / grounded / residual: the trusted
        Literal(eval(other))                                  // executor step, emitted as its result literal

  /** STAGE 0, BINDER-PRESERVING: bind this instance's inputs, but KEEP THE CONTROL FLOW.
   *
   *  [[expand]] evaluates `Iteration` and `Fixpoint` into a union of concrete group bodies, so
   *  every downstream renderer received a precomputed literal and `render(expand(p))` came out
   *  byte-equal to `render(expand(SC.reduce(p)))` whenever the optimiser only touched the parts the
   *  expansion evaluates.  That is the `IDENTICAL-STRUCTURE` / `TRIVIAL` verdict filling
   *  `proofs/pipeline/STATUS.tsv`, and such a cell certifies nothing about the optimiser: the two
   *  sides are the same literal because the EXECUTOR made them so, not because the rewrite is sound.
   *
   *  This does the same input binding — a free `Mention` becomes the instance's `Literal`, a ground
   *  path becomes a constant — and stops there.  `Iteration` and `Fixpoint` survive as BINDERS, so
   *  the renderers get a program and the obligation compares two independently rendered programs.
   *
   *  WHAT IS AND IS NOT KEPT:
   *    * `Iteration`, `Fixpoint` — KEPT, with their bound names threaded so the binder's own
   *      variable is not looked up in the instance environment (which does not contain it);
   *    * `Fold`, `Call`, `Range`, grounded — still executed, exactly as [[expand]] does, and for
   *      the same reason: no renderer models them.  They are executed ONLY when closed; a `Fold` or
   *      a `Range` that reads an enclosing binder's variable cannot be evaluated at all, and this
   *      says so instead of failing obscurely inside `eval`.
   *
   *  GATED BY THE EXECUTOR, like [[expand]]: the caller checks `eval(result) == eval(original)`. */
  def expandKeepBinders(s: Space)(using pc: PathContext, sc: SpaceContext,
                                  rc: PartialFunction[RoutinePtr, Routine]): Space =
    def groundPath(p: Path, bp: Set[String]): Boolean = p match
      case Path.Deref(pr) => !bp(pr.s)
      case Path.Concat(l, r) => groundPath(l, bp) && groundPath(r, bp)
      case _ => true
    def free(x: Space, bm: Set[String], bp: Set[String]): Boolean =
      bm.exists(n => AgnosticPipeline.usesMention(x, n)) ||
        bp.exists(n => AgnosticPipeline.usesPathRef(x, n))
    def cpath(p: Path): Path = Path.Constant(PathValue(eval(Space.Singleton(p)).paths.head.items))
    def go(x: Space, bm: Set[String], bp: Set[String], active: Set[RoutinePtr] = Set.empty): Space =
      def sub(y: Space) = go(y, bm, bp, active)
      x match
        // ---- AN ACYCLIC CALL IS INLINED, NOT REFUSED (plan.md 1D.4, and 2A.2's first clause) ----
        //
        // This arm did not exist and the `Call` fell through to the throw below whenever it read an
        // enclosing binder.  MEASURED: that is what made `puzzle15` and `nqueens` the two
        // cornerstones whose binder census read FALLBACK — the caller had to use `expand`, which
        // EXECUTES the control flow, so both stones' stage-1 artifacts described a ground
        // computation instead of the binder structure.  2 of 7 cornerstones.
        //
        // Inlining needs a SIMULTANEOUS, CAPTURE-AVOIDING substitution and that is the whole reason
        // it could not be done before 1A.1: the arguments are normalised in the CALLER's scope and
        // may mention the very binder the callee body is about to sit under, which is precisely the
        // capture case, and the one-parameter-at-a-time loop `Lower.inline` used would also have
        // collapsed two arguments naming each other's formals.  `Subst` handles both.
        //
        // THE JUSTIFYING LAW, which a reader of the resulting artifact needs: `call_unfold.p` (U63)
        // proves the SEMANTIC half — a call IS its body applied to the argument — and the SYNTACTIC
        // half is `O6a`, beta-soundness of capture-avoiding inlining, which is OPEN as a theorem and
        // carried by `SubstConformance` + `SubstCapture` + `proofs/lean/Zippy/Subst.lean`.  Recording
        // that pair in the emitted artifact's `; TRUSTS:` header is 2A.2's clause; the format is
        // fixed (`Certified.Trust`, plan.md 0.8) and `outside:Call` maps to `O6a`.
        //
        // `active` is the cycle guard: a SELF-recursive callee cannot be inlined (it would not
        // terminate) and falls through to the same honest refusal as before.
        // ONLY A CALL THAT READS AN ENCLOSING BINDER, and the first version of this arm omitted
        // that guard and MADE A CORNERSTONE WORSE.  A CLOSED call was previously EVALUATED by the
        // `other` arm below (`Literal(eval(other))`), which is strictly the better answer — a ground
        // literal is renderable by every renderer and needs no binder machinery at all.  Inlining it
        // instead splices the callee's body into the term and can surface a node that is NOT
        // renderable under a binder: MEASURED, `gol` went from BINDERS KEPT to a fallback on a
        // `Range` that had been inside a closed `Call` and is now exposed.  The guard restores
        // evaluation for the closed case and confines the inlining to exactly the calls that used to
        // throw.
        case Call(rp, refs, mentions)
            if rc.isDefinedAt(rp) && !active(rp) && free(x, bm, bp) =>
          val Routine(_, refns, mentionns, body) = rc(rp)
          go(Subst(body, (mentionns zip mentions.map(sub)).toMap, (refns zip refs).toMap),
             bm, bp, active + rp)
        case Empty => Empty
        case Literal(v) => Literal(v)
        case Mention(m) if bm(m.s) => x                        // the binder's own variable: keep
        case Mention(m) => Literal(sc.resolve(m))
        case Singleton(p) if groundPath(p, bp) => Singleton(cpath(p))
        case Singleton(_) => x                                 // reads a bound head: keep symbolic
        case Union(a, b) => Union(sub(a), sub(b))
        case Intersection(a, b) => Intersection(sub(a), sub(b))
        case Subtraction(a, b) => Subtraction(sub(a), sub(b))
        case Restriction(a, b) => Restriction(sub(a), sub(b))
        case Raffination(a, b) => Raffination(sub(a), sub(b))
        case Composition(a, b) => Composition(sub(a), sub(b))
        case Wrap(src, p) => Wrap(sub(src), if groundPath(p, bp) then cpath(p) else p)
        case Unwrap(src, p) => Unwrap(sub(src), if groundPath(p, bp) then cpath(p) else p)
        case TailsUnion(src) => TailsUnion(sub(src))
        case TailsIntersection(src) => TailsIntersection(sub(src))
        case Iteration(src, sym, rest, body) =>
          Iteration(sub(src), sym, rest, go(body, bm + rest.s, bp + sym.s, active))
        case Fixpoint(init, rec, body) =>
          Fixpoint(sub(init), rec, go(body, bm + rec.s, bp, active))
        case other =>
          // Fold / Call / Range / grounded — the trusted executed steps, as in `expand`.  A closed
          // one is evaluated; one that reads an enclosing binder cannot be, and saying which is the
          // difference between an honest limitation and a confusing `eval` failure.
          if free(other, bm, bp) then
            throw IllegalStateException(
              s"expandKeepBinders: ${other.getClass.getSimpleName} reads a variable bound by an " +
              s"enclosing Iteration/Fixpoint, so it cannot be executed and no renderer models it. " +
              s"Carrying this node symbolically is the open part of the instance tier (plan.md, " +
              s"item 3); the caller must fall back to `expand` and record the marker.  " +
              (other match
                 case Call(rp, _, _) if !rc.isDefinedAt(rp) =>
                   s"This is a Call to `${rp.s}`, which is NOT in the routine table — an ACYCLIC " +
                   "call with a known body is inlined through `Subst` by the arm above, so a Call " +
                   "reaching here is either unknown or self-recursive."
                 case Call(rp, _, _) =>
                   s"This is a SELF-RECURSIVE call to `${rp.s}`: inlining it would not terminate, " +
                   "so the honest options are the residual k-unrolling (`unrollControl`) or a " +
                   "first-class `Space.Fixpoint` (`asFixpointGeneral`)."
                 case _ =>
                   s"There is no inlining for a ${other.getClass.getSimpleName}: `Fold` and `Range` " +
                   "are positional and the grounded forms are opaque closures (T6)."))
          Literal(eval(other))
    go(s, Set.empty, Set.empty)

  // ==============================================================================================
  // Renderers into the three certified egg vocabularies
  // ==============================================================================================
  private def itemsOf(p: Path): List[Int] = p match
    case Path.Constant(v) => Interner.internPath(v.items)
    case other => throw IllegalStateException(s"expand should have made paths constant: $other")

  /** ACCUMULATOR for the program-supplied body rules an `Iteration`/`Fixpoint` needs.
   *
   *  Both binders are DEFUNCTIONALIZED in the egg vocabularies: the body is a TAG (`BodyK i` /
   *  `FBodyK i`) and the program supplies one `App`/`FApp` rewrite per tag — the same discipline
   *  `AgnosticPipeline.RenderCtx` uses for the data-agnostic legs, and the reason `formal.egg` can
   *  carry a binder at all without the e-graph needing binders. */
  final class FormalCtx:
    /** body-rule text keyed by the rule itself, so two occurrences of the same body share a tag */
    val bodyRules = scala.collection.mutable.LinkedHashMap.empty[String, (Int, String)]
    var nextId = 0
    def rule(key: String, mk: Int => String): Int =
      bodyRules.getOrElseUpdate(key, { val i = nextId; nextId += 1; (i, mk(i)) })._1
    def text: String = bodyRules.values.map(_._2).mkString("\n")

  /** formal.egg vocabulary (set-of-paths reference), for a term with NO control flow left.  Kept as
   *  the signature the local-algebra callers use; [[formalOf]] with a [[FormalCtx]] is the one that
   *  can render an `Iteration`/`Fixpoint` binder. */
  def formalOf(s: Space): String =
    def path(ids: List[Int]): String = ids match
      case Nil => "(Eps)"
      case _ => ids.map(i => s"(Item $i)").reduceRight((a, b) => s"(Concat $a $b)")
    def lit(v: SpaceValue): String =
      val ps = v.paths.toList.map(p => Interner.internPath(p.items)).sortBy(_.mkString(","))
      if ps.isEmpty then "(Empty)"
      else
        // BALANCED union tree: distribution rules descend one level per seminaive round, so the
        // round count is the tree DEPTH — log n balanced vs n for a right-nested chain.
        def bal(xs: List[String]): String = xs match
          case x :: Nil => x
          case _ => val (l, r) = xs.splitAt(xs.length / 2); s"(Union ${bal(l)} ${bal(r)})"
        bal(ps.map(ids => s"(Singleton ${path(ids)})"))
    s match
      case Empty => "(Empty)"
      case Literal(v) => lit(v)
      case Singleton(p) => s"(Singleton ${path(itemsOf(p))})"
      case Union(a, b) => s"(Union ${formalOf(a)} ${formalOf(b)})"
      case Intersection(a, b) => s"(Intersection ${formalOf(a)} ${formalOf(b)})"
      case Subtraction(a, b) => s"(Subtraction ${formalOf(a)} ${formalOf(b)})"
      case Restriction(a, b) => s"(Restriction ${formalOf(a)} ${formalOf(b)})"
      case Raffination(a, b) => s"(Raffination ${formalOf(a)} ${formalOf(b)})"
      case Composition(a, b) => s"(Composition ${formalOf(a)} ${formalOf(b)})"
      case Wrap(src, p) => s"(Wrap ${path(itemsOf(p))} ${formalOf(src)})"
      case Unwrap(src, p) => s"(Unwrap ${formalOf(src)} ${path(itemsOf(p))})"
      case TailsUnion(src) => s"(TailsUnion ${formalOf(src)})"
      case TailsIntersection(src) => s"(TailsIntersection ${formalOf(src)})"
      case other => throw IllegalStateException(s"not local algebra (expand first): $other")

  /** formal.egg vocabulary WITH THE CONTROL-FLOW BINDERS KEPT.
   *
   *  This is what makes an instance obligation an obligation.  `EquivPipeline.expand` used to
   *  evaluate every `Iteration` and `Fixpoint` into a union of concrete group bodies before
   *  anything was rendered, so `formalOf(expand(p))` and `formalOf(expand(SC.reduce(p)))` came out
   *  BYTE-EQUAL on every stone whose optimisation touches only the parts the expansion evaluates —
   *  which is the `IDENTICAL-STRUCTURE` verdict filling `proofs/pipeline/STATUS.tsv`, and it
   *  certifies nothing about the optimiser.
   *
   *  Both binders reach the vocabulary as first-class terms:
   *    * `Iteration` → `(Iter src (BodyK i))`, with one `(rewrite (App (BodyK i) h t) …)` per
   *      distinct body.  `h` is the head, `t` the head's group; the four `Iter`/`IterH` rules in
   *      `formal.egg` (certified by `proofs/laws/law_iter_set.smt2`) are what reduce it.
   *    * `Fixpoint`  → `(Fix init (FBodyK i))`, with one `(rewrite (FApp (FBodyK i) x) …)` per
   *      distinct step.  The three `Fix` rules only MERGE e-classes and leastness must be ASKED
   *      for with `(FixCand f c)`, so the caller declares the candidates and runs the `park`
   *      ruleset.
   *
   *  CAPTURES ARE BAKED IN, not passed.  On the instance tier every free input is already a
   *  `Literal`, so a body's captured operands are ground and can be inlined into its rule text;
   *  that is why `BodyK i64` and `FBodyK i64` need no capture lists here, where the agnostic
   *  `renderZ` needs `BodyK i64 IL ZL`.  The rule KEY is the rendered body with the binder's own
   *  variables abstracted, so two structurally equal bodies still share one tag. */
  def formalOf(s: Space, ctx: FormalCtx): String =
    def path(ids: List[Int]): String = ids match
      case Nil => "(Eps)"
      case _ => ids.map(i => s"(Item $i)").reduceRight((a, b) => s"(Concat $a $b)")
    // A PATH IN THIS RENDERER MAY MIX CONSTANTS AND BOUND HEAD VARIABLES.  The local-algebra
    // renderer can assume every path is a `Path.Constant`, because `expand` evaluated the binders
    // away first; here `Singleton`/`Wrap`/`Unwrap` can carry a `Deref` of the enclosing iteration's
    // head, on its own or inside a `Concat` (`aunt`'s query is `child·$person`, which is exactly
    // that shape and is what caught the first draft's Deref-only special cases).
    def pathOf(pt: Path, penv: Map[String, String]): String = pt match
      case Path.Constant(v) => path(Interner.internPath(v.items))
      case Path.Deref(pr) => penv.getOrElse(pr.s, throw IllegalStateException(s"unbound path ref ${pr.s}"))
      case Path.Concat(l, r) =>
        (pathOf(l, penv), pathOf(r, penv)) match
          case ("(Eps)", b) => b
          case (a, "(Eps)") => a
          case (a, b) => s"(Concat $a $b)"
      case other => throw IllegalStateException(s"formal renderer: path $other")
    def go(x: Space, penv: Map[String, String], senv: Map[String, String]): String = x match
      case Iteration(src, sym, rest, body) =>
        // the body sees the head as an i64 pattern variable and the group as a Space one
        val bodyPat = go(body, penv + (sym.s -> "(Item bh)"), senv + (rest.s -> "bt"))
        val id = ctx.rule("iter|" + bodyPat, i => s"(rewrite (App (BodyK $i) bh bt) $bodyPat)")
        s"(Iter ${go(src, penv, senv)} (BodyK $id))"
      case Fixpoint(init, rec, body) =>
        // MONOTONICITY IS THE SIDE CONDITION, for the reason `AgSmt.fixSym` gives: the executors
        // iterate `cur := cur ∪ F(cur)`, so inflationarity is free and monotonicity is what buys
        // LEASTNESS (terminating/fixpoint_is_lfp.smt2, O1).
        if !AgnosticPipeline.monotoneInMention(body, rec) then
          throw IllegalStateException(
            s"formal renderer: Fixpoint body is NOT monotone in ${rec.s} — the recursion variable " +
            "sits under a complement, so the least-post-fixpoint rules would not denote the executor")
        val bodyPat = go(body, penv, senv + (rec.s -> "fx"))
        val id = ctx.rule("fix|" + bodyPat, i => s"(rewrite (FApp (FBodyK $i) fx) $bodyPat)")
        s"(Fix ${go(init, penv, senv)} (FBodyK $id))"
      case Mention(m) => senv.getOrElse(m.s, throw IllegalStateException(s"unbound mention ${m.s}"))
      case Singleton(pt) => s"(Singleton ${pathOf(pt, penv)})"
      case Wrap(src, pt) => s"(Wrap ${pathOf(pt, penv)} ${go(src, penv, senv)})"
      case Unwrap(src, pt) => s"(Unwrap ${go(src, penv, senv)} ${pathOf(pt, penv)})"
      case Union(a, b) => s"(Union ${go(a, penv, senv)} ${go(b, penv, senv)})"
      case Intersection(a, b) => s"(Intersection ${go(a, penv, senv)} ${go(b, penv, senv)})"
      case Subtraction(a, b) => s"(Subtraction ${go(a, penv, senv)} ${go(b, penv, senv)})"
      case Restriction(a, b) => s"(Restriction ${go(a, penv, senv)} ${go(b, penv, senv)})"
      case Raffination(a, b) => s"(Raffination ${go(a, penv, senv)} ${go(b, penv, senv)})"
      case Composition(a, b) => s"(Composition ${go(a, penv, senv)} ${go(b, penv, senv)})"
      case TailsUnion(src) => s"(TailsUnion ${go(src, penv, senv)})"
      case TailsIntersection(src) => s"(TailsIntersection ${go(src, penv, senv)})"
      // no binder and no bound path below: the local-algebra renderer already handles these exactly
      case Empty | Literal(_) => formalOf(x)
      case other => throw IllegalStateException(s"formal renderer: unsupported $other")
    go(s, Map.empty, Map.empty)

  /** zipper.egg movement vocabulary (Z). */
  def zOf(s: Space): String =
    def wrap1(ids: List[Int], inner: String): String = ids.foldRight(inner)((k, acc) => s"(Wrap1 $k $acc)")
    s match
      case Empty => "(Empty)"
      case Literal(v) => ZipperEgg.eggOfTrie(ITrie.fromSpaceValue(v))
      case Singleton(p) => wrap1(itemsOf(p), "(Eps)")
      case Union(a, b) => s"(Union ${zOf(a)} ${zOf(b)})"
      case Intersection(a, b) => s"(Intersection ${zOf(a)} ${zOf(b)})"
      case Subtraction(a, b) => s"(Subtraction ${zOf(a)} ${zOf(b)})"
      case Restriction(a, b) => s"(Restriction ${zOf(a)} ${zOf(b)})"
      case Raffination(a, b) => s"(Raffination ${zOf(a)} ${zOf(b)})"
      case Composition(a, b) => s"(Composition ${zOf(a)} ${zOf(b)})"
      case Wrap(src, p) => wrap1(itemsOf(p), zOf(src))
      case Unwrap(src, p) => itemsOf(p).foldLeft(zOf(src))((acc, k) => s"(Sub $k $acc)")
      case TailsUnion(src) => s"(TailsUnion ${zOf(src)})"
      case TailsIntersection(src) => s"(TailsIntersection ${zOf(src)})"
      case other => throw IllegalStateException(s"not local algebra: $other")

  /** bridge (impl Tr) vocabulary from the OPTIMISED op-graph, preserving DAG sharing as egg lets. */
  def trOfGraph(g: RecursiveOpGraph): (String, String) =
    val sb = new StringBuilder
    def n(i: Int) = s"$$g$i"
    for (nl, i) <- g.nodes.iterator.zipWithIndex do nl match
      case Left(Node(op, constant, kind, inputs)) =>
        def in(j: Int) = n(inputs(j)._2)
        val term = op match
          case "Empty" => "(TNode (F) (CNil))"
          case "Literal" => tnodeOf(iLiteralStr(constant))
          case "Union" => s"(TrU ${in(0)} ${in(1)})"
          case "Intersection" => s"(TrI ${in(0)} ${in(1)})"
          case "Subtraction" => s"(TrS ${in(0)} ${in(1)})"
          case "Restriction" => s"(TrR ${in(0)} ${in(1)})"
          case "Raffination" => s"(TrRaf ${in(0)} ${in(1)})"
          case "Composition" => s"(TrC ${in(0)} ${in(1)})"
          case "Wrap" => internConstStrOf(g, inputs(1)).foldRight(in(0))((k, acc) => s"(TrW $k $acc)")
          case "Unwrap" => internConstStrOf(g, inputs(1)).foldLeft(in(0))((acc, k) => s"(TrUn $k $acc)")
          case "TailsUnion" => s"(TrTU ${in(0)})"
          case "TailsIntersection" => s"(TrTI ${in(0)})"
          case "Singleton" => internConstStrOf(g, inputs(0)).foldRight("(TNode (T) (CNil))")((k, acc) => s"(TrW $k $acc)")
          case "Constant" => "(TNode (F) (CNil))"                       // path constants are consumed by Wrap/Unwrap/Singleton
          case other => throw IllegalStateException(s"graph op not local: $other")
        sb.append(s"(let ${n(i)} $term)\n")
      case Right(_) => throw IllegalStateException("subgraphs should be expanded away")
    (sb.toString, n(g.nodes.length - 1))
  private def internConstStrOf(g: RecursiveOpGraph, coord: (Int, Int)): List[Int] =
    g.nodes(coord._2) match
      case Left(Node("Constant", c, _, _)) => internConstStr(c)
      case other => throw IllegalStateException(s"expected a Constant node, got $other")

  /** ITrie in the bridge's TNode form. */
  def tnodeOf(t: ITrie): String = ZipperEgg.trOfITrie(t).replace("(Node ", "(TNode ")

  /** local-algebra Space → the bridge's implementation (Tr) vocabulary: the EAGER recursion
   *  evaluates it in bounded rounds (unlike the movement observation calculus, which is not an
   *  evaluator — its virtual-restriction observations grow with depth × literal size). */
  def implOfSpace(s: Space): String = s match
    case Space.Empty => "(TNode (F) (CNil))"
    case Space.Literal(v) => tnodeOf(ITrie.fromSpaceValue(v))
    case Space.Singleton(p) => itemsOf(p).foldRight("(TNode (T) (CNil))")((k, acc) => s"(TrW $k $acc)")
    case Space.Union(a, b) => s"(TrU ${implOfSpace(a)} ${implOfSpace(b)})"
    case Space.Intersection(a, b) => s"(TrI ${implOfSpace(a)} ${implOfSpace(b)})"
    case Space.Subtraction(a, b) => s"(TrS ${implOfSpace(a)} ${implOfSpace(b)})"
    case Space.Restriction(a, b) => s"(TrR ${implOfSpace(a)} ${implOfSpace(b)})"
    case Space.Raffination(a, b) => s"(TrRaf ${implOfSpace(a)} ${implOfSpace(b)})"
    case Space.Composition(a, b) => s"(TrC ${implOfSpace(a)} ${implOfSpace(b)})"
    case Space.Wrap(src, p) => itemsOf(p).foldRight(implOfSpace(src))((k, acc) => s"(TrW $k $acc)")
    case Space.Unwrap(src, p) => itemsOf(p).foldLeft(implOfSpace(src))((acc, k) => s"(TrUn $k $acc)")
    case Space.TailsUnion(src) => s"(TrTU ${implOfSpace(src)})"
    case Space.TailsIntersection(src) => s"(TrTI ${implOfSpace(src)})"
    case other => throw IllegalStateException(s"not local algebra: $other")

  // ==============================================================================================
  // SMT denotation compiler: a local-algebra Space term → a membership define-fun over Path
  // ==============================================================================================
  // `EquivPipeline.Smt` — a SECOND, local-algebra-only membership compiler — USED TO LIVE HERE.
  // It had one caller, [[smtEquivalence]], and it threw on `Iteration` and `Fixpoint`, which is why
  // `expand` had to execute both binders away before an instance obligation could be emitted at
  // all — and that is what made the two sides of those obligations precomputed literals.
  //
  // It is gone.  [[smtEquivalence]] now compiles with `AgnosticPipeline.AgSmt`, the compiler the
  // data-agnostic legs already use: it handles every local-algebra arm the deleted class did, PLUS
  // `Iteration` (the group predicate inlined by its `expandTails` pass), `Fixpoint` (the two
  // post-fixpoint axioms plus Park induction) and `Range`.  Keeping two compilers meant the
  // instance tier was permanently the weaker of the two for no reason anybody had written down.
  //
  // ONE THING THE DELETED CLASS DID BETTER, AND HOW IT IS REPLACED.  Its per-subterm macro memo
  // decided structural identity of the two sides for free — equal terms got the same macro name —
  // and that is what let [[smtEquivalence]] refuse to emit `(= (m p) (m p))`.  `AgSmt` shares by
  // `System.identityHashCode`, so it cannot.  [[smtEquivalence]] therefore decides identity in
  // Scala, with `SmtDiff.alphaNorm` — equality MODULO BINDER NAMES, which is strictly stronger
  // than the macro test could ever be, since the macro test could not see binders at all.

  /** A full SMT equivalence file for two local-algebra programs.  With `obs` empty the goal is the
   *  ∀-path equivalence (the STRONGER statement, and measured cheaper for z3 on every stone that
   *  discharges at all: aunt-space 0.02 s ∀ vs 0.09 s over 28 observations, puzzle3-full-zipper
   *  1.22 s vs 6.58 s); with `obs` given the goal is the finite conjunction over the observation
   *  paths — ground-decidable, and the honest FALLBACK when the ∀ form is out of prover reach.
   *
   *  If the two sides compile to the SAME shared macro (structurally identical denotations) the
   *  file carries an IDENTICAL-STRUCTURE-NO-EQUIVALENCE-OBLIGATION marker instead of a goal:
   *  `(= (m p) (m p))` is `true` by macro expansion and the prover does no work — that vacuity
   *  is plan item 12, and it must be recorded, not emitted as a fake obligation. */
  def smtEquivalence(title: String, a: Space, b: Space, obs: List[List[Int]] = Nil): String =
    // IDENTITY, DECIDED IN SCALA AND MODULO BINDER NAMES.  `(= (m p) (m p))` is `true` by macro
    // expansion and no prover does any work on it, so a cell where the two sides really are the
    // same term must say so instead of shipping a fake goal (plan item 12).  `alphaNorm` is the
    // right test now that the binders SURVIVE to here: two iterations differing only in the names
    // of `sym`/`rest` are the same program, and a syntactic `==` would have called them different
    // and emitted an obligation that is trivial for a reason the file did not state.
    if SmtDiff.alphaNorm(a) == SmtDiff.alphaNorm(b) then
      return s"""; AUTO-GENERATED — $title
; IDENTICAL-STRUCTURE-NO-EQUIVALENCE-OBLIGATION: the two sides are the SAME term after
; alpha-normalisation — including their `Iteration`/`Fixpoint` binders — so the goal would expand
; to `true` and no prover would do any work on it.  The structural identity IS the equivalence
; result for this cell (decided in Scala, not asserted here); the optimiser/transpiler comparison
; that is NOT definitional for this stone is carried by the -agnostic twin.
"""
    val smt = new AgnosticPipeline.AgSmt
    val fa = smt.den(a, "p", Map.empty, Map.empty)
    val fb = smt.den(b, "p", Map.empty, Map.empty)
    // name both roots so a fixpoint on ONE side can take the OTHER side as its Park candidate —
    // the case that matters when `SC.reduce` collapses one side to a literal and the other keeps
    // the binder, which is exactly what happens on puzzle3-full
    smt.emitDef(s"(define-fun sideA ((p Path)) Bool $fa)")
    smt.emitDef(s"(define-fun sideB ((p Path)) Bool $fb)")
    smt.emitParkInstances(List("sideA", "sideB"))
    val goal =
      if obs.isEmpty then "(assert (not (forall ((p Path)) (= (sideA p) (sideB p)))))"
      else obs.map(ids => ids.foldRight("nil")((k, acc) => s"(cons $k $acc)"))
              .map(pt => s"(= (sideA $pt) (sideB $pt))").mkString("(assert (not (and ", " ", ")))")
    val body = s"${smt.decls.mkString("\n")}\n${smt.defsText}\n$goal"
    // PRUNE THE PRELUDE.  `append` is reachable only from `Composition` and `isPrefix` only from
    // `Restriction`/`Raffination`, so a file using neither carried SIX unused quantified axioms —
    // one with a nested existential — which is pure saturation fuel for vampire and exactly the
    // noise the pruning was introduced to remove.  Moving this leg onto `AgSmt` dropped the pruning
    // (that compiler serves the data-agnostic legs, which quantify over free inputs and cannot
    // decide statically which operators a model will need, so it uses the full prelude); MEASURED,
    // dropping it cost `gol-zipper` its vampire verdict.
    s"""; AUTO-GENERATED — $title
; INSTANCE leg: the inputs are this instance's literals, but the CONTROL FLOW IS NOT EXECUTED —
; `Iteration` stays a binder (its group predicate inlined) and `Fixpoint` stays the least
; post-fixpoint predicate with the two axioms plus Park induction, so the two sides are
; independently rendered PROGRAMS rather than the same precomputed literal.
; The goal (negated): the programs produce the SAME OUTPUT — ${if obs.isEmpty then "equal membership at EVERY path"
                                                              else s"equal membership at the ${obs.size} observation path(s)"}.
${EquivPipeline.prunedPrelude(body)}
$body
(check-sat)
"""

/** DATA-AGNOSTIC legs of the pipeline: inputs stay FREE (uninterpreted), so the certificates
 *  quantify over all inputs — the instance legs above remain as executor-grounded spot checks.
 *
 *  - Mentions render as opaque sources `(Src (N id))` in egg and as uninterpreted predicates in SMT.
 *  - Iterations stay BINDERS: each distinct body is defunctionalized to `(BodyK id captures…)` with
 *    a program-local `App` rule (egg) / a parameterised `define-fun` (SMT).
 *  - Fixpoints/recursive Calls are k-UNROLLED (k=2), the residual call replaced by a fresh free
 *    input shared by both sides — the certificate states the k-unrollings are equivalent for ALL
 *    inputs (equivalence of the loop RULE, not of one instance's convergence).
 *  - Maximal GROUND subtrees are constant-folded via the executor (the per-op semantics being
 *    folded is exactly what proofs/threeway_* certify universally) — the residual skeleton over
 *    the free inputs is what the provers then connect. */
object AgnosticPipeline:
  import Space.*

  /** THE ONE CAPTURE-AVOIDING SPACE-MENTION SUBSTITUTION.  `Lower.inline` (MORKL.scala) delegates
   *  to it, so there is a single implementation of the binder rules for the whole tree — see the
   *  note at that call site for what the alternative cost.
   *
   *  ==IT DELEGATES TO [[Subst]] NOW, AND WHY THAT WAS NOT OPTIONAL==
   *  This used to be its own walker.  It was TOTAL — `Fold` and `GroundedSS` had fallen through a
   *  `case other => other`, so substitution silently did nothing under them, and
   *  `src/test/scala/SubstConformance.scala` is the differential that found it — but it was only
   *  SHADOW-AWARE: it stopped descending when a binder rebound `m`, and never renamed a binder that
   *  would CAPTURE a free name of `r`.  Shadowing without renaming is half of hygiene:
   *
   *      Iteration(src, y, rest, Mention(rest))  with  outer := Mention(rest)
   *
   *  substitutes an `outer` occurrence for a term whose free `rest` the `Iteration` then binds, and
   *  the replacement silently starts reading the loop variable.  `Subst` alpha-renames the binder;
   *  `SubstCapture` pins the case.  Four implementations of substitution disagreed about exactly
   *  this, and `Subst.scala`'s header lists all four.
   *
   *  The binder rules it encoded are unchanged and are now stated once, in `Subst`:
   *    * `Iteration`  — `rest` binds in `templates` only; `src` is outside;
   *    * `Fixpoint`   — `rec` binds in `body` only; `init` is outside;
   *    * `Fold`       — `rest` binds in `templates` only; `src`, `initial` and `update` are not
   *                     space-mention scopes at all (`update` is a Path);
   *    * `GroundedSS` — an ordinary space operand, no binder.  `GroundedPS` takes a Path only. */
  def substMention(s: Space, m: SpaceMention, r: Space): Space = Subst.mention(s, m, r)

  /** MONOTONICITY of `s` in the space mention `m`: does `X ⊑ Y` imply `s[m↦X] ⊑ s[m↦Y]`?
   *
   *  This is the SIDE CONDITION under which a `Space.Fixpoint`'s executor semantics (⋃ₙ Fⁿ(init),
   *  stopping at the first repeat — [[EquivPipeline.expand]]) coincides with the LEAST POST-FIXPOINT
   *  that the first-class FOL/egg models axiomatise.  Without it those axioms are simply wrong (an
   *  antitone step has iterates that oscillate and no least post-fixpoint above init), so
   *  [[AgSmt.fixSym]] refuses to emit a `Fixpoint` denotation when this returns false rather than
   *  quietly asserting something unsound.
   *
   *  The algebra is monotone EVERYWHERE except three places, each a set complement in disguise:
   *    * `Subtraction(x, y)` in `y`      — x \ y shrinks as y grows;
   *    * `Raffination(x, y)` in `y`      — x \| y = x \ (x <| y), so y is complemented too
   *                                        (x itself IS monotone: each path is judged alone);
   *    * `TailsIntersection(src)`        — ⋂ over the PRESENT heads: one more head can only
   *                                        shrink the meet.
   *  `Range` (the positional ordered slice, outside the certified algebra) and an opaque `Call`
   *  have unknown variance and are treated as non-monotone whenever `m` is free in them. */
  def monotoneInMention(s: Space, m: SpaceMention): Boolean =
    def free(x: Space): Boolean = usesMention(x, m.s)
    def go(x: Space): Boolean = x match
      case Empty | Literal(_) | Singleton(_) | Mention(_) => true
      case Union(a, b) => go(a) && go(b)
      case Intersection(a, b) => go(a) && go(b)
      case Composition(a, b) => go(a) && go(b)
      case Restriction(a, b) => go(a) && go(b)              // monotone in BOTH operands
      case Subtraction(a, b) => go(a) && !free(b)
      case Raffination(a, b) => go(a) && !free(b)
      case Wrap(src, _) => go(src)
      case Unwrap(src, _) => go(src)
      case TailsUnion(src) => go(src)
      case TailsIntersection(src) => !free(src)
      case Iteration(src, _, rest, body) =>
        // monotone in `src` only if the body is monotone in the tails it binds (a bigger source
        // yields bigger tail-sets as well as more head groups)
        (!free(src) || (go(src) && monotoneInMention(body, rest))) && (rest.s == m.s || go(body))
      // THE BODY MUST BE MONOTONE IN ITS OWN RECURSION VARIABLE TOO (proofs/lean/Zippy/Positive.lean,
      // `posB`'s fixpoint arm): the fixpoint's value is monotone in an OUTER variable only if each
      // approximant is, and `chain (n+1) = init ∪ body[rec := chain n]` grows with the outer
      // variable only when `body` grows with `rec`.  The renderers refused a non-monotone body
      // separately (`fixSym`, `formalOf`); this arm now says it here as well, so the Scala decision
      // procedure IMPLIES the Lean one arm for arm (`Zippy.Space.posB_of_notFree` covers the
      // `!free` shortcut).  Strictly more conservative than before.
      case Fixpoint(init, rec, body) =>
        !free(x) || (go(init) && monotoneInMention(body, rec) && (rec.s == m.s || go(body)))
      case other => !free(other)                            // Range / Call / grounded: unknown variance
    go(s)

  // ==============================================================================================
  // RESIDUAL CUTS — a residual is a FUNCTION OF ITS ARGUMENTS, not of its name
  // ==============================================================================================
  /** ONE residual cut: the routine, the depth at which `unrollControl` stopped unrolling it, and
   *  THE ARGUMENTS IT WAS CUT WITH.
   *
   *  WHY THE ARGUMENTS ARE PART OF IT (terminating/REGISTRY.tsv O10c).  The cut replaces
   *  `r(refs; mentions)` past depth `k` with a fresh FREE INPUT, and the obligation the emitters
   *  then state is "the two k-unrollings agree FOR ALL values of that input".  That is sound only
   *  if both sides cut THE SAME THING.  Naming the residual `residual_<routine>_<depth>` and
   *  discarding `refs`/`mentions` — which is what this used to do — makes two cuts of the same
   *  routine at the same depth share one opaque set even when their ARGUMENTS differ, and a
   *  rewrite that changed a recursive argument would then be hidden behind the shared symbol
   *  instead of showing up as a difference.  Comparing the two sides' residual NAME SETS could not
   *  catch that either, because the names carried no argument information to compare.
   *
   *  So the symbol is now keyed by the arguments: `residual_<routine>_<depth>_<digest>`, where the
   *  digest is over the ALPHA-NORMALISED argument terms.  Consequences:
   *    * equal arguments  ⇒ one symbol, and the ∀-quantified obligation is exactly as before;
   *    * differing arguments ⇒ DIFFERENT symbols, so the goal openly compares two unrelated free
   *      inputs and is refutable rather than silently provable.  That is the conservative
   *      direction: a bad rewrite can no longer hide, at the price of an obligation that needs the
   *      argument equivalence proved first ([[residualPairings]] states it as its own obligation).
   *  The full descriptor of every symbol is kept in [[residualCuts]] so emitters can print it and
   *  gates can compare arguments rather than names. */
  /** ==============================================================================================
   *  A CANONICAL, INJECTIVE, STABLE IDENTITY FOR A TERM — what the residual symbol is keyed by.
   *
   *  ==WHY `show` CANNOT BE IT==
   *  [[ResidualCut.digest]] used to hash `Space.show`, truncated to FOUR BYTES.  Four separate
   *  defects, and the width is the least of them:
   *
   *   1. `Space.show` HAS NO `Fold` ARM.  It is a non-exhaustive match (the compiler says so), so a
   *      cut whose argument contains a `Fold` did not get a weak identity — it threw `MatchError`.
   *   2. `GroundedPS`/`GroundedSS`/`GroundedPP`/`GroundedSP` render as `f.hashCode()`, a 32-bit JVM
   *      IDENTITY hash.  So the "stable digest" was neither stable across runs — the same term
   *      digests differently in a fresh JVM, and these symbols are written into COMMITTED artifacts
   *      — nor injective, since two distinct functions collide whenever their identity hashes do.
   *   3. `show` is not injective even on the pure algebra: `Wrap(src, p)` renders `(p x src)` and
   *      `Composition(x, y)` renders `(x x y)` — the same surface syntax.
   *   4. AND THEN the width: 32 bits is a collision at roughly 2^16 cuts by the birthday bound.
   *      `cutSymbol`'s guard DETECTS a collision and throws, which is right but is not the same
   *      thing as not having them, and it only sees the cuts made in ONE JVM.
   *
   *  ==WHAT THIS IS INSTEAD==
   *  A tagged, length-prefixed structural encoding, TOTAL over every constructor of `Space` and
   *  `Path`.  Injective by construction: each constructor has a distinct tag, every string is
   *  written as `<byte length>:<bytes>` so no concatenation is ambiguous, and every operand list
   *  carries its arity.  The digest is then the FULL SHA-256 of that encoding.
   *
   *  ==AND IT REFUSES RATHER THAN GUESSES==
   *  A grounded node carries an arbitrary Scala function, for which no stable identity exists —
   *  which is the fact `docs/TRUSTED.md` T6 records, from the other side.  This encoder returns
   *  `None` there instead of inventing one, and [[ResidualCut.digest]] then FAILS LOUDLY.  Emitting
   *  an artifact whose symbol silently changes between runs is worse than not emitting it: the
   *  artifact is committed, and a reviewer diffing two runs would see a spurious difference. */
  object CanonicalId:
    /** the ONE separator, and it is safe for exactly one reason: every component written by the
     *  encoders below is either a tag character or a length-prefixed string, so no component can
     *  contain a run that parses as a boundary.  It is not a delimiter the encoding relies on. */
    private val Sep = "~"
    private def str(s: String, b: StringBuilder): Unit =
      b.append(s.getBytes("UTF-8").length).append(':').append(s)

    /** A PATH'S ITEMS, EACH LENGTH-PREFIXED, WITH THE COUNT.  Joining them on a separator first --
     *  which this encoder did, as `items.mkString(" ")` -- makes the encoding NON-INJECTIVE the
     *  moment an item contains that separator: `PathValue(List("a b"))` and
     *  `PathValue(List("a", "b"))` both become the single string `"a b"`, so two distinct terms get
     *  one key.  The claim on this object was "injective by construction", and joining on a
     *  separator is exactly the construction that breaks it.
     *
     *  No current fixture exercises it, because every test alphabet here is single letters -- which
     *  is why the injectivity tests could not see it and why `RangeCardCheck`-style exhaustion over
     *  hand-built constructors is not a substitute for encoding the structure faithfully. */
    private def items(xs: List[String], b: StringBuilder): Unit =
      b.append(xs.length).append('<')
      xs.foreach(str(_, b))
      b.append('>')

    /** the structural key of a term, or `None` if it contains a grounded node */
    def of(s: Space): Option[String] =
      val b = StringBuilder(); if go(s, b) then Some(b.result()) else None
    def ofPath(p: Path): Option[String] =
      val b = StringBuilder(); if goP(p, b) then Some(b.result()) else None
    /** the key of a whole cut descriptor */
    def ofCut(routine: String, depth: Int, refs: Vector[Path], mentions: Vector[Space]): Option[String] =
      val parts = refs.map(ofPath) ++ mentions.map(of)
      if parts.exists(_.isEmpty) then None
      else
        val b = StringBuilder()
        str(routine, b); b.append(depth).append(',').append(refs.length).append(',')
          .append(mentions.length).append(Sep)
        Some(b.result() + parts.flatten.mkString(Sep))

    private def go(s: Space, b: StringBuilder): Boolean = s match
      case Space.Empty              => b.append("E"); true
      case Space.Mention(m)         => b.append("M"); str(m.s, b); true
      case Space.Singleton(p)       => b.append("S"); goP(p, b)
      case Space.Literal(v)         =>
        // the PATH SET itself, sorted and each path length-prefixed: injective on the value, and
        // stable, where `SpaceValue.show` is a `Set` rendering
        b.append("L").append(v.paths.size).append('[')
        // sorted by the ITEM LIST, so the order is a function of the value and not of the Set's
        // iteration order, and each path encoded item-wise
        v.paths.toSeq.map(_.items).sortBy(x => (x.length, x.mkString("\u0000")))
          .foreach(items(_, b))
        b.append(']'); true
      case Space.Union(x, y)        => b.append("u"); go(x, b) && go(y, b)
      case Space.Intersection(x, y) => b.append("i"); go(x, b) && go(y, b)
      case Space.Subtraction(x, y)  => b.append("d"); go(x, b) && go(y, b)
      case Space.Restriction(x, y)  => b.append("r"); go(x, b) && go(y, b)
      case Space.Raffination(x, y)  => b.append("f"); go(x, b) && go(y, b)
      case Space.Composition(x, y)  => b.append("c"); go(x, b) && go(y, b)
      case Space.Wrap(src, p)       => b.append("w"); go(src, b) && goP(p, b)
      case Space.Unwrap(src, p)     => b.append("W"); go(src, b) && goP(p, b)
      case Space.TailsUnion(src)    => b.append("t"); go(src, b)
      case Space.TailsIntersection(src) => b.append("T"); go(src, b)
      case Space.Range(z, lo, hi)   => b.append("R").append(lo).append(',').append(hi).append(';'); go(z, b)
      case Space.Iteration(src, sym, rest, body) =>
        b.append("I"); str(sym.s, b); str(rest.s, b); go(src, b) && go(body, b)
      case Space.Fixpoint(init, rec, body) =>
        b.append("X"); str(rec.s, b); go(init, b) && go(body, b)
      case Space.Fold(src, initial, acc, sym, rest, body, upd) =>
        // THE ARM `show` DOES NOT HAVE.  All seven fields, both binders included.
        b.append("F"); str(acc.s, b); str(sym.s, b); str(rest.s, b)
        go(src, b) && goP(initial, b) && go(body, b) && goP(upd, b)
      case Space.Call(r, refs, mentions) =>
        b.append("C"); str(r.s, b); b.append(refs.length).append(',').append(mentions.length).append(';')
        refs.forall(goP(_, b)) && mentions.forall(go(_, b))
      // NO STABLE IDENTITY EXISTS for an arbitrary Scala function; refuse rather than invent one.
      case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => false

    private def goP(p: Path, b: StringBuilder): Boolean = p match
      case Path.Deref(pr)     => b.append("p"); str(pr.s, b); true
      case Path.Constant(pi)  => b.append("k"); items(pi.items, b); true
      case Path.Concat(l, r)  => b.append("."); goP(l, b) && goP(r, b)
      case Path.GroundedPP(_, _) | Path.GroundedSP(_, _) => false

  final case class ResidualCut(routine: String, depth: Int, refs: Vector[Path], mentions: Vector[Space]):
    /** the alpha-invariant rendering the digest is taken over — also what the emitters print */
    def canonical: String =
      s"$routine@$depth(" + refs.map(_.show).mkString(", ") + "; " +
        mentions.map(m => SmtDiff.alphaNorm(m).show).mkString(", ") + ")"
    /** THE STRUCTURAL IDENTITY the digest is taken over — see [[CanonicalId]] for why this is not
     *  [[canonical]], which is for humans and is neither injective nor total nor stable.  The
     *  mentions are alpha-normalised first, so two cuts that differ only in binder names key alike. */
    def identity: Option[String] =
      CanonicalId.ofCut(routine, depth, refs, mentions.map(SmtDiff.alphaNorm))

    /** THE FULL SHA-256 of [[identity]] — 256 bits, not the 32 this used to keep.
     *
     *  A truncated digest was a claim about how many cuts a run makes; the full one needs no such
     *  claim.  [[CanonicalId]] carries the reason the INPUT to the hash had to change as well, which
     *  matters more than the width: a digest is only as injective as the thing it digests. */
    def digest: String =
      val id = identity.getOrElse(throw IllegalStateException(
        s"cannot key a residual cut on $canonical: an argument contains a GROUNDED node, for which " +
        "no stable identity exists (docs/TRUSTED.md T6).  A residual symbol is written into a " +
        "COMMITTED artifact, so a per-JVM identity hash would make that artifact differ between " +
        "runs for no semantic reason, and refusing is the sound direction.  Either the caller must " +
        "not cut a call whose arguments are grounded, or the grounded node needs a declared id."))
      val md = java.security.MessageDigest.getInstance("SHA-256")
      md.digest(id.getBytes("UTF-8")).map(b => f"${b & 0xff}%02x").mkString
    /** the free-input name the cut is replaced by */
    def symbol: String = s"residual_${routine}_${depth}_$digest"

  /** symbol → descriptor, for every cut this JVM has made.  A residual symbol is meaningless
   *  without its arguments, and the emitters/gates need them; the map is append-only and keyed by
   *  a digest of the descriptor, so a symbol never denotes two different cuts. */
  val residualCuts: scala.collection.concurrent.Map[String, ResidualCut] =
    scala.collection.concurrent.TrieMap.empty[String, ResidualCut]

  private def cutSymbol(c: ResidualCut): String =
    val s = c.symbol
    residualCuts.putIfAbsent(s, c) match
      case Some(prev) if prev.canonical != c.canonical =>
        throw IllegalStateException(
          s"residual digest collision: $s already denotes ${prev.canonical}, now asked for ${c.canonical}")
      case _ => s

  /** The residual free inputs of a term, WITH their descriptors. */
  def residualsOf(s: Space): Map[String, ResidualCut] =
    val out = scala.collection.mutable.Map.empty[String, ResidualCut]
    def go(x: Space): Unit = x match
      case Mention(m) if m.s.startsWith("residual_") => residualCuts.get(m.s).foreach(out(m.s) = _)
      case Union(a, b) => go(a); go(b)
      case Intersection(a, b) => go(a); go(b)
      case Subtraction(a, b) => go(a); go(b)
      case Restriction(a, b) => go(a); go(b)
      case Raffination(a, b) => go(a); go(b)
      case Composition(a, b) => go(a); go(b)
      case Wrap(src, _) => go(src)
      case Unwrap(src, _) => go(src)
      case TailsUnion(src) => go(src)
      case TailsIntersection(src) => go(src)
      case Iteration(src, _, _, b) => go(src); go(b)
      case Fixpoint(i, _, b) => go(i); go(b)
      case Fold(src, _, _, _, _, b, _) => go(src); go(b)
      case Range(x, _, _) => go(x)
      case GroundedSS(src, _) => go(src)
      case Call(_, _, ms) => ms.foreach(go)
      case Empty | Literal(_) | Mention(_) | Singleton(_) | GroundedPS(_, _) => ()
    go(s); out.toMap

  /** THE CUT-ALIGNMENT VERDICT for one obligation.  Returns, for the two sides' residual sets:
   *    - `shared`     symbols both sides cut identically (same routine, depth AND arguments) —
   *                   these need nothing further: the ∀-quantified free input is genuinely shared;
   *    - `unmatched`  cuts that appear on one side only.  Each is a REAL gap: either the sides cut
   *                   at different depths/routines, or they cut the same routine with arguments
   *                   that are not alpha-equal.  For the second case the emitters state the
   *                   ARGUMENT EQUIVALENCE as its own obligation (`<name>-residual-args.smt2`);
   *                   only a discharged one licenses treating the two symbols as the same input.
   *  A name-set equality is deliberately NOT offered here: it is the check this replaces. */
  final case class CutAlignment(shared: Set[String], leftOnly: Map[String, ResidualCut],
                                rightOnly: Map[String, ResidualCut]):
    def aligned: Boolean = leftOnly.isEmpty && rightOnly.isEmpty
    /** the (left, right) pairs whose routine and depth agree but whose ARGUMENTS do not — the ones
     *  an argument-equivalence obligation could still align */
    def argumentPairs: List[(ResidualCut, ResidualCut)] =
      for l <- leftOnly.values.toList.sortBy(_.canonical);
          r <- rightOnly.values.toList.sortBy(_.canonical)
          if l.routine == r.routine && l.depth == r.depth
      yield (l, r)
    def report: String =
      if aligned then s"aligned (${shared.size} shared cut(s))"
      else s"MISALIGNED — left-only ${leftOnly.values.map(_.canonical).mkString("{", "; ", "}")}, " +
           s"right-only ${rightOnly.values.map(_.canonical).mkString("{", "; ", "}")}"

  def alignCuts(a: Space, b: Space): CutAlignment =
    val (ra, rb) = (residualsOf(a), residualsOf(b))
    CutAlignment(ra.keySet intersect rb.keySet, ra -- rb.keySet, rb -- ra.keySet)

  /** k-unroll recursive Calls; inline acyclic Calls; keep Fixpoint and everything else INTACT.
   *
   *  FIXPOINT IS NO LONGER UNROLLED (plan item 1).  It used to become
   *    `init ∪ F(init) ∪ F(F(init))` at k = 2, so the certificate stated "the 2-unrollings agree",
   *  never "the fixpoints agree"; the only reason for it was that neither downstream renderer could
   *  represent a `Fixpoint` at all.  Both can now — `renderZ` emits `(Fix init (BodyK …))` and
   *  `AgSmt.denRaw` emits an uninterpreted predicate with the two post-fixpoint axioms plus Park
   *  induction — so the binder survives to the provers.  Recursive `Call`s that no `asFixpoint`
   *  lowering turns into a `Fixpoint` are still k-unrolled and cut with a fresh shared free input;
   *  that residual is the honest remaining approximation, it is PARAMETERIZED BY ITS ARGUMENTS
   *  ([[ResidualCut]]) and it is named with its full descriptor in the emitted files. */
  def unrollControl(s: Space, k: Int)(using rc: PartialFunction[RoutinePtr, Routine]): Space = s match
    case Union(a, b) => Union(unrollControl(a, k), unrollControl(b, k))
    case Intersection(a, b) => Intersection(unrollControl(a, k), unrollControl(b, k))
    case Subtraction(a, b) => Subtraction(unrollControl(a, k), unrollControl(b, k))
    case Restriction(a, b) => Restriction(unrollControl(a, k), unrollControl(b, k))
    case Raffination(a, b) => Raffination(unrollControl(a, k), unrollControl(b, k))
    case Composition(a, b) => Composition(unrollControl(a, k), unrollControl(b, k))
    case Wrap(src, p) => Wrap(unrollControl(src, k), p)
    case Unwrap(src, p) => Unwrap(unrollControl(src, k), p)
    case TailsUnion(src) => TailsUnion(unrollControl(src, k))
    case TailsIntersection(src) => TailsIntersection(unrollControl(src, k))
    case Iteration(src, sym, rest, body) => Iteration(unrollControl(src, k), sym, rest, unrollControl(body, k))
    case Range(x, lo, hi) => Range(unrollControl(x, k), lo, hi)
    case Fixpoint(init, rec, body) => Fixpoint(unrollControl(init, k), rec, unrollControl(body, k))
    case Call(rp, refs, mentions) if rc.isDefinedAt(rp) && {
      // TRY TO LOWER BEFORE UNROLLING.  A self-recursion `asFixpointGeneral` recognises becomes a
      // real `Space.Fixpoint`, which now survives to both renderers with a first-class model; only
      // the shapes no lowering recognises are k-unrolled and cut with a fresh free input.
      // MEASURED (2026-08-31): the corpus' ONLY self-recursive cornerstone routine, datalog-sn's
      // `sn_tc`, is NOT lowerable — it changes TWO mentions at once (`all` and `delta`) and
      // `asFixpointGeneral` requires exactly one, the documented honest-residual case — so the
      // guard fires nowhere today and datalog-sn still gets the residual k-unrolling.  It is here
      // so that "we unroll" stops being the DEFAULT and becomes the fallback (non-recursive
      // routines take the same path as before: `asFixpointGeneral` returns None for them).
      val r = rc(rp); asFixpointGeneral(rp, r.refs, r.mentions, r.body).isEmpty
    } =>
      val Routine(_, refns, mentionns, body) = rc(rp)
      // substitute args; unroll self-recursion k levels, then cut with a fresh shared free input
      // ONE SIMULTANEOUS SUBSTITUTION, NOT A LOOP OF SINGLE ONES.
      //
      // This read
      //     for (pr, arg) <- refns zip refs      do b = substPathRef(b, pr, arg)
      //     for (mn, arg) <- mentionns zip args  do b = substMention(b, mn, arg)
      // which is SEQUENTIAL COMPOSITION.  It differs from simultaneous substitution exactly when an
      // ARGUMENT mentions a later FORMAL, and then it is WRONG: for `g(a, b)` called as `g(b, a)`,
      // `a := b` rewrites every `a` to `b`, and the following `b := a` rewrites BOTH to `a` — the two
      // arguments collapse into one variable.  The same hazard runs ACROSS the two sorts, which is
      // why both maps go into ONE call rather than two: a path argument naming a formal mention's
      // binder, or the reverse, would be resolved in whichever order the two loops happened to run.
      // `SubstCapture` pins the `g(y,x)` case; `Subst.scala`'s header works the example through.
      def inlineOnce(depth: Int, args: Vector[Space]): Space =
        val pm = (refns zip refs).toMap
        val sm = (mentionns zip args).toMap
        expandCalls(Subst(body, sm, pm), depth)
      def expandCalls(b: Space, depth: Int): Space = b match
        case Call(`rp`, rs, ms) =>
          // THE CUT.  The residual is keyed by (routine, depth, ARGUMENTS) — see [[ResidualCut]];
          // the arguments are recursed into first so a residual nested inside one is named too.
          if depth >= k then
            Mention(SpaceMention(cutSymbol(ResidualCut(rp.s, depth, rs, ms.map(expandCalls(_, depth))))))
          else inlineOnce(depth + 1, ms.map(expandCalls(_, depth)))
        case Union(a, c) => Union(expandCalls(a, depth), expandCalls(c, depth))
        case Intersection(a, c) => Intersection(expandCalls(a, depth), expandCalls(c, depth))
        case Subtraction(a, c) => Subtraction(expandCalls(a, depth), expandCalls(c, depth))
        case Restriction(a, c) => Restriction(expandCalls(a, depth), expandCalls(c, depth))
        case Raffination(a, c) => Raffination(expandCalls(a, depth), expandCalls(c, depth))
        case Composition(a, c) => Composition(expandCalls(a, depth), expandCalls(c, depth))
        case Wrap(src, p) => Wrap(expandCalls(src, depth), p)
        case Unwrap(src, p) => Unwrap(expandCalls(src, depth), p)
        case TailsUnion(src) => TailsUnion(expandCalls(src, depth))
        case TailsIntersection(src) => TailsIntersection(expandCalls(src, depth))
        case Iteration(src, sym, rest, bd) => Iteration(expandCalls(src, depth), sym, rest, expandCalls(bd, depth))
        case Range(x, lo, hi) => Range(expandCalls(x, depth), lo, hi)
        case Call(orp, rs, ms) if rc.isDefinedAt(orp) => unrollControl(Call(orp, rs, ms.map(expandCalls(_, depth))), k)
        case other => other
      inlineOnce(0, mentions.map(unrollControl(_, k)))
    case Call(rp, refs, mentions) if rc.isDefinedAt(rp) =>
      // the lowerable case: substitute the actual arguments into the Fixpoint form and keep going
      val r = rc(rp)
      val fixBody = asFixpointGeneral(rp, r.refs, r.mentions, r.body).get
      // Simultaneous, for the same reason as `inlineOnce` above — and it matters more here, because
      // the term being substituted into is a `Space.Fixpoint` whose `rec` binder is exactly the kind
      // of name a sequential pass can capture.
      val pm = (r.refs zip refs).toMap
      val sm = (r.mentions zip mentions.map(unrollControl(_, k))).toMap
      unrollControl(Subst(fixBody, sm, pm), k)
    case other => other

  /** PATH-REF SUBSTITUTION — delegated to [[Subst.pathRef]].
   *
   *  Its own walker had TWO defects, and the second is the one no equivalence test could see.  It was
   *  shadow-aware but not capture-avoiding, exactly as [[substMention]] was; and its inner path
   *  walker `sp` ended in `case other => other`, so `Path.GroundedPP` and `Path.GroundedSP` were
   *  never descended — a path ref inside a grounded closure's ARGUMENT was never substituted at all,
   *  and the closure then ran against an unbound ref.  `Subst`'s path walker is total over all five
   *  `Path` constructors, and `Path.GroundedSP` goes through the SPACE walker because it carries a
   *  `Space` that can contain binders. */
  def substPathRef(s: Space, pr: PathRef, arg: Path): Space = Subst.pathRef(s, pr, arg)

  /** ground = no free mentions, no bound-variable references. */
  def isGround(s: Space, boundP: Set[String], boundM: Set[String]): Boolean =
    def gp(p: Path): Boolean = p match
      case Path.Constant(_) => true
      case Path.Deref(pr) => boundP.contains(pr.s)   // bound refs are closed by their binder
      case Path.Concat(l, r) => gp(l) && gp(r)
      case _ => false
    s match
      case Empty | Literal(_) => true
      case Mention(m) => boundM.contains(m.s)   // a rest-mention bound by an enclosing iteration is closed
      case Singleton(p) => gp(p)
      case Union(a, b) => isGround(a, boundP, boundM) && isGround(b, boundP, boundM)
      case Intersection(a, b) => isGround(a, boundP, boundM) && isGround(b, boundP, boundM)
      case Subtraction(a, b) => isGround(a, boundP, boundM) && isGround(b, boundP, boundM)
      case Restriction(a, b) => isGround(a, boundP, boundM) && isGround(b, boundP, boundM)
      case Raffination(a, b) => isGround(a, boundP, boundM) && isGround(b, boundP, boundM)
      case Composition(a, b) => isGround(a, boundP, boundM) && isGround(b, boundP, boundM)
      case Wrap(src, p) => isGround(src, boundP, boundM) && gp(p)
      case Unwrap(src, p) => isGround(src, boundP, boundM) && gp(p)
      case TailsUnion(src) => isGround(src, boundP, boundM)
      case TailsIntersection(src) => isGround(src, boundP, boundM)
      case Iteration(src, sym, rest, body) => isGround(src, boundP, boundM) && isGround(body, boundP + sym.s, boundM + rest.s)
      case Range(x, _, _) => isGround(x, boundP, boundM)
      case _ => false

  /** Constant-fold maximal ground subtrees (the folded per-op semantics are certified in proofs/).
   *
   *  NEVER APPLY THIS TO A SIDE OF AN OBLIGATION.  It runs the executor, so after
   *  [[EquivPipeline.expand]] — which has already turned a cornerstone into ground local algebra —
   *  `isGround` holds AT THE ROOT and the whole program collapses to ONE `Literal`.  Both sides of
   *  an instance obligation then fold to the same literal and the goal becomes `(= B B)`: all 18
   *  every `proofs/pipeline` INSTANCE `.smt2` file was vacuous this way (plan item 12; z3 answered
   *  `unsat` in 0.00-0.01 s and stayed `unsat` with the ENTIRE prelude deleted).  It is only ever
   *  legitimate on an ANALYSIS INPUT — [[symbolic]], where free mentions keep the skeleton alive. */
  def fold(s: Space): Space =
    if isGround(s, Set.empty, Set.empty) then Literal(evalI(s)(using PathContextMap(Map.empty), Map.empty, PartialFunction.empty).toSpaceValue)
    else s match
      case Union(a, b) => Union(fold(a), fold(b))
      case Intersection(a, b) => Intersection(fold(a), fold(b))
      case Subtraction(a, b) => Subtraction(fold(a), fold(b))
      case Restriction(a, b) => Restriction(fold(a), fold(b))
      case Raffination(a, b) => Raffination(fold(a), fold(b))
      case Composition(a, b) => Composition(fold(a), fold(b))
      case Wrap(src, p) => Wrap(fold(src), p)
      case Unwrap(src, p) => Unwrap(fold(src), p)
      case TailsUnion(src) => TailsUnion(fold(src))
      case TailsIntersection(src) => TailsIntersection(fold(src))
      case Iteration(src, sym, rest, body) => Iteration(fold(src), sym, rest, fold(body))
      case Fixpoint(init, rec, body) => Fixpoint(fold(init), rec, fold(body))
      case Range(x, lo, hi) => Range(fold(x), lo, hi)
      case other => other

  def symbolic(s: Space, k: Int = 2)(using rc: PartialFunction[RoutinePtr, Routine]): Space =
    fold(unrollControl(s, k))

  // ==============================================================================================
  // egg renderer: Space (with free mentions + Iteration binders) → movement vocabulary
  // ==============================================================================================
  final class RenderCtx:
    val appRules = scala.collection.mutable.LinkedHashMap.empty[String, (Int, String)]  // bodyKey -> (id, rule)
    var nextId = 0
    // large ground literals interned ONCE as globals: without this every BodyK App rule inlines
    // the full relation per occurrence (~8x for a join body) and the Keys/KFilt/IsEmpty searches
    // congruence-close over enormous repeated ground terms.
    val litDefs = scala.collection.mutable.LinkedHashMap.empty[String, String]          // rendered -> name
    def internLit(rendered: String): String =
      if rendered.length < 120 then rendered
      else litDefs.getOrElseUpdate(rendered, s"$$glit${litDefs.size}")
    def text: String =
      (litDefs.map((r, n) => s"(let $n $r)") ++ appRules.values.map(_._2)).mkString("\n")

  def mentionId(m: SpaceMention): Int = Interner.intern(("$mention$" + m.s))

  private def pathTokens(p: Path, penv: Map[String, String]): List[String] = p match
    case Path.Constant(v) => Interner.internPath(v.items).map(_.toString)
    case Path.Deref(pr) => List(penv.getOrElse(pr.s, throw IllegalStateException(s"unbound path ref ${pr.s}")))
    case Path.Concat(l, r) => pathTokens(l, penv) ++ pathTokens(r, penv)
    case other => throw IllegalStateException(s"unsupported path: $other")

  def renderZ(s: Space, penv: Map[String, String], senv: Map[String, String], ctx: RenderCtx,
              zipperStyle: Boolean): String =
    def rz(s: Space): String = renderZ(s, penv, senv, ctx, zipperStyle)
    def bin(op: String, a: Space, b: Space): String =
      val (ra, rb) = (rz(a), rz(b))
      if zipperStyle && ra == rb && (op == "Union" || op == "Intersection") then ra          // smart ctor: x∪x=x, x∩x=x
      else if zipperStyle && ra == rb && op == "Subtraction" then "(Empty)"                  // x\x=∅
      else s"($op $ra $rb)"
    s match
      case Empty => "(Empty)"
      case Literal(v) => ctx.internLit(ZipperEgg.eggOfTrie(ITrie.fromSpaceValue(v)))
      case Mention(m) => senv.getOrElse(m.s, s"(Src (N ${mentionId(m)}))")
      case Singleton(p) => pathTokens(p, penv).foldRight("(Eps)")((t, acc) => s"(Wrap1 $t $acc)")
      case Union(a, b) => bin("Union", a, b)
      case Intersection(a, b) => bin("Intersection", a, b)
      case Subtraction(a, b) => bin("Subtraction", a, b)
      case Restriction(a, b) => s"(${if zipperStyle then "Restr" else "Restriction"} ${rz(a)} ${rz(b)})"
      case Raffination(a, b) => s"(Raffination ${rz(a)} ${rz(b)})"
      case Composition(a, b) => s"(Composition ${rz(a)} ${rz(b)})"
      case Wrap(src, p) => pathTokens(p, penv).foldRight(rz(src))((t, acc) => s"(Wrap1 $t $acc)")
      case Unwrap(src, p) => pathTokens(p, penv).foldLeft(rz(src))((acc, t) => s"(Sub $t $acc)")
      case TailsUnion(src) => s"(TailsUnion ${rz(src)})"
      case TailsIntersection(src) => s"(TailsIntersection ${rz(src)})"
      case Range(x, lo, hi) =>
        // Range is the POSITIONAL ordered-slice op — outside the certified path-set algebra
        // (the design note); over free inputs it is treated as an opaque shared input, keyed by its
        // operand's rendering + bounds so both sides align iff their Range subtrees align.
        val key = s"range|$lo|$hi|" + renderZ(x, penv, senv, ctx, false)
        s"(Src (N ${Interner.intern(("$range$" + key.hashCode))}))"
      case Iteration(src, sym, rest, body) =>
        // defunctionalize: captured items = bound path vars used in body (other than sym);
        // captured spaces = bound/free space refs used in body (other than rest)
        val pUsed = penv.keys.toList.sorted.filter(n => usesPathRef(body, n) && n != sym.s)
        val sUsed = senv.keys.toList.sorted.filter(n => usesMention(body, n) && n != rest.s)
        val hVar = s"h${penv.size}"
        // canonical key: the rule text with capture slots abstracted (ONE render per body — a second
        // per-instance render here would be exponential in iteration-nesting depth)
        val patP = pUsed.zipWithIndex.map((n, i) => s"ci$i"); val patS = sUsed.zipWithIndex.map((n, i) => s"cz$i")
        val bodyPat = renderZ(body,
          penv ++ (pUsed zip patP).toMap + (sym.s -> hVar),
          senv ++ (sUsed zip patS).toMap + (rest.s -> "t"), ctx, false)   // bodies always PLAIN:
          // both styles' bodies are law-equal; a style-split here would fork BodyK ids and leave
          // (Iter src (BodyK i …)) vs (BodyK j …) unprovably distinct over free sources
        val key = bodyPat + "|" + pUsed.size + "|" + sUsed.size
        val id = ctx.appRules.getOrElseUpdate(key, {
          val i = ctx.nextId; ctx.nextId += 1
          val il = patP.foldRight("(INil)")((v, acc) => s"(ICons $v $acc)")
          val zl = patS.foldRight("(ZNil)")((v, acc) => s"(ZCons $v $acc)")
          (i, s"(rewrite (App (BodyK $i $il $zl) $hVar t) $bodyPat)")
        })._1
        val il = pUsed.map(penv).foldRight("(INil)")((v, acc) => s"(ICons $v $acc)")
        val zl = sUsed.map(senv).foldRight("(ZNil)")((v, acc) => s"(ZCons $v $acc)")
        s"(Iter ${rz(src)} (BodyK $id $il $zl))"
      case Fixpoint(init, rec, body) =>
        // FIRST-CLASS (plan item 1): `(Fix init (BodyK i …))` with the step defunctionalized
        // exactly like an Iteration body, and an `FApp` rule instead of an `App` rule.  The three
        // Fix rules in the egg preludes only MERGE e-classes (no unrolling rewrite), so
        // the run still saturates; leastness has to be ASKED for with `(FixCand f c)`.
        // MONOTONICITY IS THE WHOLE SIDE CONDITION *because the executor is inflationary*: every
        // executor iterates `cur := cur ∪ F(cur)`, so the second premise of
        // terminating/fixpoint_is_lfp.smt2 (`init ⊆ F(init)`) holds by construction and
        // monotonicity is what remains — it is exactly what buys LEASTNESS (part iii).  Were the
        // executor to iterate `F` alone, monotonicity would NOT be enough: fixpoint_is_lfp.smt2:47-50
        // is the machine-checked monotone-but-non-inflationary counterexample.
        if !monotoneInMention(body, rec) then
          throw IllegalStateException(
            s"agnostic renderer: Fixpoint body is NOT monotone in ${rec.s} — the recursion variable " +
            "sits under a complement (Subtraction/Raffination right operand, or TailsIntersection), " +
            "so the least-post-fixpoint model would not denote the executor's limit")
        val pUsed = penv.keys.toList.sorted.filter(n => usesPathRef(body, n))
        val sUsed = senv.keys.toList.sorted.filter(n => usesMention(body, n) && n != rec.s)
        val patP = pUsed.indices.map(i => s"ci$i").toList; val patS = sUsed.indices.map(i => s"cz$i").toList
        val bodyPat = renderZ(body, penv ++ (pUsed zip patP).toMap,
                              senv ++ (sUsed zip patS).toMap + (rec.s -> "x"), ctx, false)
        val key = "fix|" + bodyPat + "|" + pUsed.size + "|" + sUsed.size
        val id = ctx.appRules.getOrElseUpdate(key, {
          val i = ctx.nextId; ctx.nextId += 1
          val il = patP.foldRight("(INil)")((v, acc) => s"(ICons $v $acc)")
          val zl = patS.foldRight("(ZNil)")((v, acc) => s"(ZCons $v $acc)")
          (i, s"(rewrite (FApp (BodyK $i $il $zl) x) $bodyPat)")
        })._1
        val il = pUsed.map(penv).foldRight("(INil)")((v, acc) => s"(ICons $v $acc)")
        val zl = sUsed.map(senv).foldRight("(ZNil)")((v, acc) => s"(ZCons $v $acc)")
        s"(Fix ${rz(init)} (BodyK $id $il $zl))"
      case other => throw IllegalStateException(s"agnostic renderer: unsupported $other")

  /** IS THE PATH REF `name` FREE IN `s`?  THE MATCH IS TOTAL, AND IT HAS TO BE.
   *
   *  `Fold`, `Call`, `GroundedPS` and `GroundedSS` used to fall through a `case _ => false`, so a
   *  `Fold` whose body reads a variable, or a `Call` passing it as an argument, was reported as NOT
   *  USING IT.  That is not a cosmetic gap: [[monotoneInMention]] decides variance with
   *  `case other => !free(other)`, so a `Fold`/`Call`/grounded node over the recursion variable came
   *  out MONOTONE — the opposite of the intended conservative answer — and monotonicity is the side
   *  condition under which an emitter may write a first-class least-post-fixpoint `Fix`
   *  (terminating/fixpoint_is_lfp.smt2, O1).  `src/test/scala/FreeVarsCheck.scala` is the
   *  regression, and it also pins the BINDER rules below rather than leaving them to inspection.
   *
   *  The binders, once: `Iteration` binds `symbol` (a path ref) over `templates` only; `Fold` binds
   *  `acc` AND `symbol` over `templates` and `update`, while `initial` is outside them; `Fixpoint`
   *  binds only a space mention, so it shadows no path ref at all. */
  def usesPathRef(s: Space, name: String): Boolean =
    def up(p: Path): Boolean = p match
      case Path.Deref(pr) => pr.s == name
      case Path.Concat(l, r) => up(l) || up(r)
      case _ => false
    s match
      case Empty | Literal(_) | Mention(_) => false
      case Singleton(p) => up(p)
      case Wrap(src, p) => up(p) || usesPathRef(src, name)
      case Unwrap(src, p) => up(p) || usesPathRef(src, name)
      case Union(a, b) => usesPathRef(a, name) || usesPathRef(b, name)
      case Intersection(a, b) => usesPathRef(a, name) || usesPathRef(b, name)
      case Subtraction(a, b) => usesPathRef(a, name) || usesPathRef(b, name)
      case Restriction(a, b) => usesPathRef(a, name) || usesPathRef(b, name)
      case Raffination(a, b) => usesPathRef(a, name) || usesPathRef(b, name)
      case Composition(a, b) => usesPathRef(a, name) || usesPathRef(b, name)
      case TailsUnion(src) => usesPathRef(src, name)
      case TailsIntersection(src) => usesPathRef(src, name)
      case Iteration(src, sym, _, body) => usesPathRef(src, name) || (sym.s != name && usesPathRef(body, name))
      case Fixpoint(init, _, body) => usesPathRef(init, name) || usesPathRef(body, name)
      case Fold(src, initial, acc, sym, _, body, upd) =>
        val bound = acc.s == name || sym.s == name
        usesPathRef(src, name) || up(initial) || (!bound && (usesPathRef(body, name) || up(upd)))
      case Call(_, refs, ms) => refs.exists(up) || ms.exists(usesPathRef(_, name))
      case GroundedPS(p, _) => up(p)
      case GroundedSS(src, _) => usesPathRef(src, name)
      case Range(x, _, _) => usesPathRef(x, name)

  /** IS THE SPACE MENTION `name` FREE IN `s`?  Total, for the reason [[usesPathRef]] gives — this is
   *  the function [[monotoneInMention]]'s `free` is, so a missing arm here weakened the
   *  monotonicity gate rather than merely under-reporting. */
  def usesMention(s: Space, name: String): Boolean = s match
    case Empty | Literal(_) | Singleton(_) | GroundedPS(_, _) => false
    case Mention(m) => m.s == name
    case Union(a, b) => usesMention(a, name) || usesMention(b, name)
    case Intersection(a, b) => usesMention(a, name) || usesMention(b, name)
    case Subtraction(a, b) => usesMention(a, name) || usesMention(b, name)
    case Restriction(a, b) => usesMention(a, name) || usesMention(b, name)
    case Raffination(a, b) => usesMention(a, name) || usesMention(b, name)
    case Composition(a, b) => usesMention(a, name) || usesMention(b, name)
    case Wrap(src, _) => usesMention(src, name)
    case Unwrap(src, _) => usesMention(src, name)
    case TailsUnion(src) => usesMention(src, name)
    case TailsIntersection(src) => usesMention(src, name)
    case Iteration(src, _, rest, body) => usesMention(src, name) || (rest.s != name && usesMention(body, name))
    case Fixpoint(init, rec, body) => usesMention(init, name) || (rec.s != name && usesMention(body, name))
    case Fold(src, _, _, _, rest, body, _) =>
      usesMention(src, name) || (rest.s != name && usesMention(body, name))
    case Call(_, _, ms) => ms.exists(usesMention(_, name))
    case GroundedSS(src, _) => usesMention(src, name)
    case Range(x, _, _) => usesMention(x, name)

  // ==============================================================================================
  // SMT compiler with free inputs and binder parameters
  // ==============================================================================================
  final class AgSmt:
    val defs = new StringBuilder
    val decls = scala.collection.mutable.LinkedHashSet.empty[String]
    private var n = 0
    def fresh(p: String): String = { n += 1; s"${p}_$n" }
    private val shared = scala.collection.mutable.HashMap.empty[Space, String]
    /** compile to a formula string over path term `pt`, with binder env (path var → SMT Int term). */
    def den(s: Space, pt: String, penv: Map[String, String], senv: Map[String, String]): String =
      // SHARE binder-free subterms as named define-funs: the k-unrolled programs duplicate large
      // subtrees (e.g. datalog's all/delta), and inlining them per occurrence is exponential.
      // LITERALS AND MENTIONS ARE NOT SHARED, AND SHARING THEM WAS TRIED AND MEASURED WORSE.
      //
      // A `Mention` is already one applied symbol, so a macro adds only a name.  A `Literal` is a
      // ground disjunction `(or (= p …) …)`, and the reasonable-looking idea — the instance legs'
      // inputs ARE literals, so sharing them should shrink the formula — makes the obligations
      // HARDER rather than bigger: MEASURED on `aunt-zipper`, sharing every literal of more than two
      // paths produced 69 tiny macros in a 9.5 KB file and BOTH provers then failed at 240 s where
      // z3 had discharged it in seconds.  A ground disjunction is directly usable by E-matching; the
      // same disjunction behind a `define-fun` application is an indirection to unfold first, and 69
      // of them obscure the goal.  Size was never the problem for literals — the size win came from
      // sharing the NON-literal subterms structurally, which `shared` does.
      if penv.isEmpty && senv.isEmpty && !s.isInstanceOf[Space.Literal] && !s.isInstanceOf[Space.Mention] then
        // SHARED STRUCTURALLY, NOT BY IDENTITY.  The key was `System.identityHashCode(s)`, so two
        // EQUAL subterms reached by different routes got two macros and the formula carried both.
        // That is most of an obligation's size, because the two sides of a pipeline obligation share
        // almost all of their subtrees while being built independently: MEASURED when this compiler
        // took over the instance legs from the deleted structural-sharing `Smt`, three cells that
        // had been discharged (`aunt-zipper`, `nqueens-zipper`, `puzzle3-full-space`) went to
        // PROVER-BUDGET-EXCEEDED and `gol-graph` lost its vampire verdict — purely from formula
        // size, since the goals were unchanged.  `Space` is a case-class tree, so `==`/`hashCode`
        // are structural and this is the same key the old `Smt` memo used.
        val key = s
        val name = shared.getOrElseUpdate(key, {
          val n = fresh("s")
          val body = denRaw(s, "p", Map.empty, Map.empty)
          emitDef(s"(define-fun $n ((p Path)) Bool $body)")
          n
        })
        return s"($name $pt)"
      denRaw(s, pt, penv, senv)
    private val defOrder = scala.collection.mutable.ArrayBuffer.empty[String]
    def emitDef(d: String): Unit = defOrder += d
    def defsText: String = defOrder.mkString("\n")
    def denRaw(s: Space, pt: String, penv: Map[String, String], senv: Map[String, String]): String =
      def pathOnto(p: Path, tail: String): String =
        def toks(p: Path): List[String] = p match
          case Path.Constant(v) => Interner.internPath(v.items).map(_.toString)
          case Path.Deref(pr) => List(penv.getOrElse(pr.s, throw IllegalStateException(s"unbound ${pr.s}")))
          case Path.Concat(l, r) => toks(l) ++ toks(r)
          case other => throw IllegalStateException(s"path: $other")
        toks(p).foldRight(tail)((t, acc) => s"(cons $t $acc)")
      s match
        case Empty => "false"
        case Literal(v) =>
          val ps = v.paths.toList.map(p => Interner.internPath(p.items)).sortBy(_.mkString(","))
          if ps.isEmpty then "false"
          else ps.map(ids => s"(= $pt ${ids.foldRight("nil")((k, a) => s"(cons $k $a)")})").mkString("(or ", " ", ")")
        case Mention(m) => senv.get(m.s) match
          case Some(f) => s"($f $pt)"
          case None =>
            val nm = s"in_${m.s.replaceAll("[^A-Za-z0-9]", "_")}"
            decls += s"(declare-fun $nm (Path) Bool)"; s"($nm $pt)"
        case Singleton(p) => s"(= $pt ${pathOnto(p, "nil")})"
        case Union(a, b) => s"(or ${den(a, pt, penv, senv)} ${den(b, pt, penv, senv)})"
        case Intersection(a, b) => s"(and ${den(a, pt, penv, senv)} ${den(b, pt, penv, senv)})"
        case Subtraction(a, b) => s"(and ${den(a, pt, penv, senv)} (not ${den(b, pt, penv, senv)}))"
        case Composition(a, b) =>
          s"(exists ((q Path) (r Path)) (and (= $pt (append q r)) ${den(a, "q", penv, senv)} ${den(b, "r", penv, senv)}))"
        case Restriction(x, y) =>
          s"(and ${den(x, pt, penv, senv)} (exists ((r Path)) (and ${den(y, "r", penv, senv)} (isPrefix r $pt))))"
        case Raffination(x, y) => den(Subtraction(x, Restriction(x, y)), pt, penv, senv)
        case Wrap(src, p) =>
          val q = fresh("q")
          s"(exists (($q Path)) (and (= $pt ${pathOnto(p, q)}) ${den(src, q, penv, senv)}))"
        case Unwrap(src, p) => den(src, pathOnto(p, pt), penv, senv)
        case TailsUnion(src) =>
          val h = fresh("h")
          s"(exists (($h Int)) ${den(src, s"(cons $h $pt)", penv, senv)})"
        case TailsIntersection(src) =>
          val h = fresh("h"); val h2 = fresh("g"); val q = fresh("q"); val q2 = fresh("w")
          s"(and (exists (($h Int) ($q Path)) ${den(src, s"(cons $h $q)", penv, senv)}) " +
            s"(forall (($h2 Int)) (=> (exists (($q2 Path)) ${den(src, s"(cons $h2 $q2)", penv, senv)}) ${den(src, s"(cons $h2 $pt)", penv, senv)})))"
        case Range(x, lo, hi) =>
          val key = "rng_" + (s"$lo|$hi|" + x.toString).hashCode.toHexString
          decls += s"(declare-fun $key (Path) Bool)"   // opaque positional op, shared across sides
          s"($key $pt)"
        case fx @ Fixpoint(init, rec, body) => s"(${fixSym(fx, init, rec, body, penv, senv)} $pt)"
        case Iteration(src, sym, rest, body) =>
          val h = fresh("h"); val q = fresh("q")
          val tails = fresh("tails")
          // tails-of-h as a derived predicate closure: T(q) := src(h·q)
          val bodyD = den(body, pt, penv + (sym.s -> h), senv + (rest.s -> tails))
          // inline the tails predicate by textual lambda: define as a let-free macro via a define-fun
          // with h as a parameter is cleaner, but the body may capture outer binders — inline instead:
          val inlined = bodyD.replace(s"($tails ", s"(TAILS$h ")
          // replace occurrences (TAILS$h x) textually with src(cons h x): handled by a helper pass
          val expanded = expandTails(inlined, s"TAILS$h", src, h, penv, senv)
          s"(exists (($h Int)) (and (exists (($q Path)) ${den(src, s"(cons $h $q)", penv, senv)}) $expanded))"
        case other => throw IllegalStateException(s"agnostic smt: unsupported $other")
    // ------------------------------------------------------------------------------------------
    // FIXPOINT — FIRST-CLASS IN PLAIN FOL (plan item 1).  Before this, `denRaw` threw on Fixpoint
    // and `unrollControl` k-unrolled it away, so the agnostic certificates only ever said "the
    // 2-unrollings agree".  A Fixpoint now becomes an UNINTERPRETED PREDICATE `fix_i : Path → Bool`
    // constrained by the two POST-FIXPOINT axioms
    //     ∀q. init(q) → fix(q)            ∀q. body[rec↦fix](q) → fix(q)
    // and, per ordered pair of fixpoints appearing in one obligation, a PARK INDUCTION instance
    //     (∀r. init_f(r) → g(r)) ∧ (∀r. body_f[rec↦g](r) → g(r))  →  ∀q. fix_f(q) → g(q)
    // which is a THEOREM of the intended semantics, not an assumption: its two premises are
    // obligations the prover still has to discharge, so it cannot make a goal vacuous.  Mutual
    // containment then yields equality in plain FOL with no new quantifier alternation.
    //
    // SOUNDNESS SIDE CONDITION, STATED EXACTLY.  The two axioms above say `fix` is a post-fixpoint
    // of the operator `X ↦ init ∪ F(X)`, and Park says it is the LEAST one.  The executors compute
    // the limit of `cur := cur ∪ F(cur)` — the Kleene chain of that same inflationary operator —
    // so `init ⊆ (init ∪ F(init))` is automatic and the only remaining premise of
    // terminating/fixpoint_is_lfp.smt2 (O1) is MONOTONICITY of F, which is what makes the limit the
    // LEAST post-fixpoint rather than merely one of them.  It is decided syntactically by
    // [[AgnosticPipeline.monotoneInMention]] and this method REFUSES to emit rather than assert
    // something unsound.  NOTE what would break if an executor went back to iterating `F` alone:
    // monotonicity would stop being sufficient (fixpoint_is_lfp.smt2:47-50 is the counterexample)
    // and these axioms would be false of the executor's output.  Regression:
    // src/test/scala/FixpointSemantics.scala.
    /** the Lean theorem every first-class `Fix` clause is derived from (see [[fixSym]]) */
    val FixpointTheorem = "proofs/lean/Zippy/Positive.lean#Zippy.Space.fixpoint_is_lfp"
    private val fixMemo = scala.collection.mutable.HashMap.empty[(Space, Map[String, String], Map[String, String]), String]
    private val fixes = scala.collection.mutable.ArrayBuffer.empty[(String, Space, Space, SpaceMention, Map[String, String], Map[String, String])]
    def fixSym(fx: Space, init: Space, rec: SpaceMention, body: Space,
               penv: Map[String, String], senv: Map[String, String]): String =
      fixMemo.getOrElseUpdate((fx, penv, senv), {
        if !AgnosticPipeline.monotoneInMention(body, rec) then
          throw IllegalStateException(
            s"agnostic smt: Fixpoint body is NOT monotone in ${rec.s} — the recursion variable sits " +
            "under a complement (Subtraction/Raffination right operand, or TailsIntersection).  The " +
            "least-post-fixpoint axioms would then be false of the executor's limit, so no " +
            "first-class denotation is emitted (the caller must record an honest marker)")
        val f = fresh("fix")
        decls += s"(declare-fun $f (Path) Bool)"
        emitDef(s"; FIXPOINT $f — first-class: the LEAST post-fixpoint above init (never unrolled)")
        // THE MARKER `scripts/check_asserts.py` READS (plan.md 2E.4).  These two clauses and the
        // Park instance below say the executor's fixpoint is the least post-fixpoint of
        // `X ↦ init ∪ body[rec := X]`; that it IS one is `Zippy.Space.fixpoint_is_lfp`
        // (proofs/lean/Zippy/Positive.lean), whose hypothesis — the body positive in `rec` — is the
        // `monotoneInMention` check this method just made.  So the clauses are DERIVED from a
        // Lean theorem, not assumed, and the marker says which.
        emitDef(s"; DERIVED-FROM: $FixpointTheorem")
        emitDef(s"(assert (forall ((zq Path)) (=> ${den(init, "zq", penv, senv)} ($f zq))))")
        emitDef(s"; DERIVED-FROM: $FixpointTheorem")
        emitDef(s"(assert (forall ((zq Path)) (=> ${den(body, "zq", penv, senv + (rec.s -> f))} ($f zq))))")
        fixes += ((f, init, body, rec, penv, senv))
        f
      })

    /** One PARK INDUCTION instance per ORDERED pair of (compiled fixpoint, candidate predicate),
     *  where the candidates are the other fixpoints PLUS whatever `extra` names the caller passes —
     *  normally the two sides' own root macros.  The `extra` list is not decoration: MEASURED on
     *  puzzle3-full, `SC.reduce` collapses the fixpoint side to a ground 12-path literal while the
     *  original side keeps the binder, so the obligation has exactly ONE `fix` symbol and
     *  fixpoint-to-fixpoint pairing emits NOTHING — leastness against the literal is the only form
     *  of the argument that exists.  Call once, AFTER both sides are compiled and after the root
     *  macros are emitted: `fixes` must be complete and the instances must follow the defining
     *  axioms in the file. */
    def emitParkInstances(extra: List[String] = Nil): Unit =
      val snapshot = fixes.toList
      val candidates = snapshot.map(_._1) ++ extra
      for (f, initF, bodyF, recF, pe, se) <- snapshot; g <- candidates if f != g do
        val premInit = s"(forall ((zr Path)) (=> ${den(initF, "zr", pe, se)} ($g zr)))"
        val premStep = s"(forall ((zr Path)) (=> ${den(bodyF, "zr", pe, se + (recF.s -> g))} ($g zr)))"
        emitDef(s"; PARK INDUCTION $f ⊑ $g — leastness of $f; BOTH premises are obligations")
        emitDef(s"; DERIVED-FROM: $FixpointTheorem")
        emitDef(s"(assert (=> (and $premInit $premStep) (forall ((zq Path)) (=> ($f zq) ($g zq)))))")

    /** replace (MARK t) applications with den(src, (cons h t)). */
    private def expandTails(f: String, mark: String, src: Space, h: String, penv: Map[String, String], senv: Map[String, String]): String =
      var out = f
      while out.contains(s"($mark ") do
        val i = out.indexOf(s"($mark ")
        var d = 0; var j = i
        while { val c = out(j); if c == '(' then d += 1 else if c == ')' then d -= 1; d != 0 || j == i } do j += 1
        val arg = out.substring(i + mark.length + 2, j)
        out = out.substring(0, i) + den(src, s"(cons $h $arg)", penv, senv) + out.substring(j + 1)
      out

  def smtAgnostic(title: String, a: Space, b: Space): String =
    val smt = new AgSmt
    val fa0 = smt.den(a, "p", Map.empty, Map.empty)
    val fb0 = smt.den(b, "p", Map.empty, Map.empty)
    // name both roots so a fixpoint on ONE side can take the OTHER side as its Park candidate
    smt.emitDef(s"(define-fun sideA ((p Path)) Bool $fa0)")
    smt.emitDef(s"(define-fun sideB ((p Path)) Bool $fb0)")
    smt.emitParkInstances(List("sideA", "sideB"))   // after BOTH sides and both root macros
    val (fa, fb) = ("(sideA p)", "(sideB p)")
    s"""; AUTO-GENERATED — $title
; DATA-AGNOSTIC: inputs are uninterpreted path-set predicates; the goal (negated) states the two
; programs produce the same output at EVERY path for ALL inputs.
${EquivPipeline.foPrelude}
${smt.decls.mkString("\n")}
${smt.defsText}
(assert (not (forall ((p Path)) (= $fa $fb))))
(check-sat)
"""

/** structural-diff decomposition for agnostic SMT: the two sides are usually identical except at
 *  finitely many optimiser-rewritten subterms; whole-program ∀-equivalence under nested binders is
 *  FO-hard, but each differing SUBTERM pair — with its surrounding binders freed to fresh symbols —
 *  is a small obligation, and whole-program equivalence follows by congruence (as in the e-graph). */
object SmtDiff:
  import Space.*
  type Mismatch = (Space, Space, List[String], List[String])   // (lhs, rhs, bound path vars, bound mentions)

  def diff(a: Space, b: Space, penv: List[String], senv: List[String]): List[Mismatch] =
    if a == b then Nil
    else (a, b) match
      case (Union(_, _), Union(_, _)) =>
        // AC-AWARE: flatten both union towers and cancel common operands (multiset) — sound
        // because common ∪ restA = common ∪ restB follows from restA = restB.  Unrolling the
        // original vs the optimised program enumerates branches in different orders; positional
        // pairing would mismatch them and fabricate unprovable obligations.
        def ops(s: Space): List[Space] = s match { case Union(x, y) => ops(x) ++ ops(y); case o => List(o) }
        val (la, lb) = (ops(a), ops(b))
        val cb = scala.collection.mutable.Map.empty[Space, Int].withDefaultValue(0)
        lb.foreach(x => cb(x) += 1)
        val restA = la.filter(x => if cb(x) > 0 then { cb(x) -= 1; false } else true)
        val ca = scala.collection.mutable.Map.empty[Space, Int].withDefaultValue(0)
        la.foreach(x => ca(x) += 1)
        val restB = lb.filter(x => if ca(x) > 0 then { ca(x) -= 1; false } else true)
        (restA, restB) match
          case (Nil, Nil) => Nil                                       // AC-equal
          case (x :: Nil, y :: Nil) => diff(x, y, penv, senv)
          case (xs, ys) =>
            def u(l: List[Space]): Space = if l.isEmpty then Empty else l.reduceLeft(Union.apply)
            List((u(xs), u(ys), penv, senv))
      case (Intersection(a1, a2), Intersection(b1, b2)) => diff(a1, b1, penv, senv) ++ diff(a2, b2, penv, senv)
      case (Subtraction(a1, a2), Subtraction(b1, b2)) => diff(a1, b1, penv, senv) ++ diff(a2, b2, penv, senv)
      case (Restriction(a1, a2), Restriction(b1, b2)) => diff(a1, b1, penv, senv) ++ diff(a2, b2, penv, senv)
      case (Raffination(a1, a2), Raffination(b1, b2)) => diff(a1, b1, penv, senv) ++ diff(a2, b2, penv, senv)
      case (Composition(a1, a2), Composition(b1, b2)) => diff(a1, b1, penv, senv) ++ diff(a2, b2, penv, senv)
      case (Wrap(s1, p1), Wrap(s2, p2)) if p1 == p2 => diff(s1, s2, penv, senv)
      case (Unwrap(s1, p1), Unwrap(s2, p2)) if p1 == p2 => diff(s1, s2, penv, senv)
      case (TailsUnion(s1), TailsUnion(s2)) => diff(s1, s2, penv, senv)
      case (TailsIntersection(s1), TailsIntersection(s2)) => diff(s1, s2, penv, senv)
      case (Range(s1, l1, h1), Range(s2, l2, h2)) if l1 == l2 && h1 == h2 => diff(s1, s2, penv, senv)
      case (Iteration(s1, y1, r1, b1), Iteration(s2, y2, r2, b2)) if y1.s == y2.s && r1.s == r2.s =>
        diff(s1, s2, penv, senv) ++ diff(b1, b2, y1.s :: penv, r1.s :: senv)
      case (Fixpoint(i1, r1, b1), Fixpoint(i2, r2, b2)) if r1.s == r2.s =>
        // CONGRUENCE for the least fixpoint: lfp is monotone in BOTH init and step, so
        // init₁ = init₂ and step₁ = step₂ (pointwise, with `rec` freed) give lfp₁ = lfp₂ — Park
        // induction in each direction with the identity as the mediating predicate.  `alphaNorm`
        // has already canonicalised the binder, so the `r1.s == r2.s` guard is not a restriction.
        diff(i1, i2, penv, senv) ++ diff(b1, b2, penv, r1.s :: senv)
      case _ => List((a, b, penv, senv))

  /** diff pairs partitioned into LAW-JUSTIFIED (proof-carrying: instances of the ∀-certified
   *  optimiser laws, verified by syntactic replay — no per-program prover run needed) and RESIDUAL
   *  (genuinely needing a prover obligation). */
  def partition(a0: Space, b0: Space): (List[(Mismatch, String)], List[Mismatch]) =
    val ms = diff(alphaNorm(a0), alphaNorm(b0), Nil, Nil)
    val refined = ms.flatMap(refine(_, 3))
    (refined.collect { case Left(j) => j }, refined.collect { case Right(m) => m })

  def obligationsFile(title: String, a0: Space, b0: Space): String =
    val (justified, residual) = partition(a0, b0)
    val jHeader = justified.zipWithIndex.map { case ((_, law), i) =>
      s"; LAW-JUSTIFIED pair $i: $law\n;   certificate(s): ${certificateOf(law)}"
    }.mkString("\n")
    val smt = new AgnosticPipeline.AgSmt
    var reflexive = 0
    val parkCands = scala.collection.mutable.ArrayBuffer.empty[String]
    val obs = residual.zipWithIndex.flatMap { case ((l, r, ps, ss), i) =>
      val penv = ps.map(n => n -> s"bv_${i}_$n").toMap
      val senv = ss.map(n => n -> s"bm_${i}_${n.replaceAll("[^A-Za-z0-9]", "_")}").toMap
      val fl = smt.den(l, "p", penv, senv); val fr = smt.den(r, "p", penv, senv)
      if fl == fr then { reflexive += 1; None }          // freed-binder collapse ⇒ no real obligation
      else
        penv.values.foreach(v => smt.decls += s"(declare-const $v Int)")
        senv.values.foreach(v => smt.decls += s"(declare-fun $v (Path) Bool)")
        val (nl, nr) = (s"pairL$i", s"pairR$i")
        smt.emitDef(s"(define-fun $nl ((p Path)) Bool $fl)")
        smt.emitDef(s"(define-fun $nr ((p Path)) Bool $fr)")
        parkCands ++= List(nl, nr)
        Some(s"(forall ((p Path)) (= ($nl p) ($nr p)))")
    }
    smt.emitParkInstances(parkCands.toList)   // after EVERY pair: each side is the other's candidate
    val nPairs = justified.size + residual.size
    if obs.isEmpty && justified.isEmpty then
      return s"""; AUTO-GENERATED — $title
; TRIVIAL-NO-OBLIGATION: the two sides are syntactically identical after alpha-normalisation
; ($nPairs candidate pair(s), $reflexive reflexive after freeing binders).  Recorded as a
; no-obligation marker; the runner counts these and invokes no prover on them.
"""
    if obs.isEmpty then
      return s"""; AUTO-GENERATED — $title
; LAW-JUSTIFIED-NO-RESIDUAL: all ${justified.size} differing pair(s) (of $nPairs candidates,
; $reflexive reflexive-after-freeing) are verified instances of the optimiser's ∀-certified law
; set — each right side is reproduced EXACTLY by replaying the named laws on the left side
; (proof-carrying transformation).  No per-program prover obligation remains; the universal
; certificates are the proofs/ files named per pair below.
$jHeader
"""
    s"""; AUTO-GENERATED — $title
; STRUCTURAL-DIFF decomposition: ${obs.size} REAL obligation(s) of $nPairs candidate pair(s)
; ($reflexive reflexive-after-freeing skipped, ${justified.size} law-justified — see below);
; each proved ∀ inputs ∀ paths with its surrounding binders freed to fresh symbols;
; whole-program equivalence follows by congruence (identical context around equal subterms).
${if justified.isEmpty then "" else jHeader + "\n"}${EquivPipeline.foPrelude}
${smt.decls.mkString("\n")}
${smt.defsText}
(assert (not ${obs.mkString(if obs.size == 1 then "" else "(and ", " ", if obs.size == 1 then "" else ")")}))
(check-sat)
"""

  /** ============================================================================================
   *  CANONICAL ALPHA-NORMALISATION OF BINDER NAMES (traversal order), so optimiser-induced binder
   *  renamings do not masquerade as structural differences (they previously produced REFLEXIVE
   *  diff obligations: both sides' differing name mapped to the same freed symbol).
   *
   *  ==IT IS TOTAL OVER EVERY CONSTRUCTOR, AND THAT IS A CORRECTNESS PROPERTY, NOT TIDINESS==
   *  An earlier revision ended both matches in `case other => other`, which swallowed `Call`,
   *  `Fold`, `GroundedPS`, `GroundedSS` on the space side and `Path.GroundedPP`, `Path.GroundedSP`
   *  on the path side.  For a CLOSED constructor (`Empty`, `Literal`, `Path.Constant`) that identity
   *  is right.  For the other six it is WRONG IN BOTH DIRECTIONS:
   *
   *    * INCOMPLETE -- `Fold` binds three names (`acc`, `symbol`, `rest`) and they were left as the
   *      optimiser wrote them, so two alpha-equivalent folds compared UNEQUAL and the pair became a
   *      residual prover obligation instead of being recognised as the same term;
   *    * UNSOUND -- worse, and this is the real defect.  A `Mention` or `Deref` inside an
   *      un-descended `Call`/`Fold`/grounded subterm kept the name the ENCLOSING binder had already
   *      renamed, so the result could carry ONE variable under TWO names.  Two terms could then
   *      compare EQUAL after normalisation (both mis-normalised the same way) and a cell be
   *      classified `IDENTICAL-STRUCTURE-NO-EQUIVALENCE-OBLIGATION` -- i.e. no obligation emitted at
   *      all -- on the strength of a renaming that was never applied.  `alphaNorm` is the decision
   *      procedure behind that classification (`SmtDiff.alphaNorm(a) == SmtDiff.alphaNorm(b)`), and
   *      behind `CanonicalId.ofCut`'s residual-cut identity, so its totality is load-bearing.
   *
   *  So BOTH matches are now EXHAUSTIVE, with no catch-all: a new `Space` or `Path` constructor is a
   *  COMPILE ERROR here rather than a silent identity.  Every closed case is listed by name with
   *  the reason it needs no descent.
   *
   *  ==IT DELEGATES TO `Subst` (plan.md 0.6/1A.1), AND THE SHAPE CHANGED WITH IT==
   *  This used to thread two rename maps (`pm`, `mm`) down the traversal and apply them at `Deref`
   *  and `Mention`.  It now renames EACH BINDER'S OWN OCCURRENCES with one `Subst` call at that
   *  binder and then descends into the result, so the maps are gone: by the time `go` reaches a
   *  subterm, every enclosing binder has already been renamed in it.  That is `Matching.canon`'s
   *  structure, and it is the right one — there is one substitution in the tree and this is not a
   *  second implementation of half of it.
   *
   *  The MINTING ORDER is unchanged, so the canonical names are unchanged: the counter is still one
   *  monotone sequence over the traversal, and two alpha-equivalent terms still get identical names,
   *  which is what makes `alphaNorm(a) == alphaNorm(b)` a decision procedure.
   *
   *  ==WHAT THE DELEGATION BUYS, GIVEN THE FRESHNESS ARGUMENT ALREADY HELD==
   *  Every name introduced here is minted from a monotone counter with a prefix (`av`/`ar`/`af`/
   *  `fa`/`fv`/`fr`) that no source program uses, so no introduced name could capture a free
   *  occurrence — the old map-threading was capture-free for that reason.  But it was capture-free
   *  by an argument about the FRESHNESS SUPPLY, written in this comment, and correct SHADOWING was a
   *  second property of the map updates (`pm + (sym.s -> ns)` overriding an outer entry).  Both are
   *  now `Subst`'s, checked by `SubstCapture` and proved in `proofs/lean/Zippy/Subst.lean`, and this
   *  file no longer carries an argument of its own that a future edit could invalidate.
   *  ============================================================================================ */
  def alphaNorm(s: Space): Space =
    var n = 0
    def fresh(): Int = { n += 1; n }
    /** one canonical name per binder occurrence, from the shared counter */
    def bind(prefix: String): String = s"$prefix${fresh()}"
    def go(s: Space): Space = s match
      // ---- closed: nothing to rename, and each is named so the match stays exhaustive ----------
      case Empty => Empty
      case Literal(v) => Literal(v)                 // a SpaceValue is ground; it holds no binders
      // ---- variable occurrences: FREE by the time `go` sees them.  Every enclosing binder has
      //      already renamed its own occurrences through `Subst`, so a name still standing here is
      //      free in the whole term and must be PRESERVED.
      case Mention(m) => Mention(m)
      // ---- pointwise, non-binding -------------------------------------------------------------
      case Union(a, b) => Union(go(a), go(b))
      case Intersection(a, b) => Intersection(go(a), go(b))
      case Subtraction(a, b) => Subtraction(go(a), go(b))
      case Restriction(a, b) => Restriction(go(a), go(b))
      case Raffination(a, b) => Raffination(go(a), go(b))
      case Composition(a, b) => Composition(go(a), go(b))
      case Wrap(src, p) => Wrap(go(src), rp(p))
      case Unwrap(src, p) => Unwrap(go(src), rp(p))
      case TailsUnion(src) => TailsUnion(go(src))
      case TailsIntersection(src) => TailsIntersection(go(src))
      case Range(x, lo, hi) => Range(go(x), lo, hi)
      case Singleton(p) => Singleton(rp(p))
      // ---- calls: `r` is a GLOBAL routine name, not a binder, so it is preserved verbatim.
      //      Its arguments are ordinary subterms and are descended.  Leaving them un-descended was
      //      the unsoundness the old `case other => other` had.
      case Call(r, refs, mentions) => Call(r, refs.map(rp), mentions.map(go))
      // ---- binding forms.  ONE `Subst` per binder, then descend into the result.  `src`/`init`/
      //      `initial` are OUTSIDE the binder and are descended without it.
      case Iteration(src, sym, rest, body) =>
        val (ns, nr) = (bind("av"), bind("ar"))
        val ref = PathRef(ns).known(1)
        val men = SpaceMention(nr)
        Iteration(go(src), ref, men,
                  go(Subst(body, Map(rest -> Mention(men)), Map(sym -> Path.Deref(ref)))))
      case Fixpoint(init, rec, body) =>
        val men = SpaceMention(bind("af"))
        Fixpoint(go(init), men, go(Subst.mention(body, rec, Mention(men))))
      // `Fold` BINDS THREE NAMES, and this is the case the old catch-all lost entirely.  `src` and
      // `initial` are evaluated OUTSIDE the binder (the accumulator's seed cannot mention the
      // accumulator), so they are normalised in the outer scope; `templates` and `update` are the
      // body and see all three.  Order of minting follows the field order so the canonical names are
      // a function of the term, which is what makes two alpha-equivalent folds compare equal.
      case Fold(src, initial, acc, symbol, rest, templates, update) =>
        val (na, nv, nr) = (bind("fa"), bind("fv"), bind("fr"))
        val (ra, rv, mr) = (PathRef(na).known(1), PathRef(nv).known(1), SpaceMention(nr))
        val ren = (x: Space) => Subst(x, Map(rest -> Mention(mr)),
                                      Map(acc -> Path.Deref(ra), symbol -> Path.Deref(rv)))
        Fold(go(src), rp(initial), ra, rv, mr,
             go(ren(templates)),
             rp(Subst.path(update, Map(rest -> Mention(mr)),
                           Map(acc -> Path.Deref(ra), symbol -> Path.Deref(rv)))))
      // ---- grounded: the CLOSURE is opaque (docs/TRUSTED.md T6 assumes only determinism) but its
      //      ARGUMENT is an ordinary subterm and must be descended.
      case GroundedPS(p, f) => GroundedPS(rp(p), f)
      case GroundedSS(p, f) => GroundedSS(go(p), f)

    def rp(p: Path): Path = p match
      case Path.Deref(pr) => Path.Deref(pr)         // free by the time `rp` sees it; see `go`
      case Path.Concat(l, r) => Path.Concat(rp(l), rp(r))
      case Path.Constant(pi) => Path.Constant(pi)   // a PathValue is ground
      case Path.GroundedPP(q, f) => Path.GroundedPP(rp(q), f)
      case Path.GroundedSP(q, f) => Path.GroundedSP(go(q), f)

    go(s)

  /** PROOF-CARRYING JUSTIFICATION: try to match a differing pair as an instance of one of the
   *  optimiser's laws (or a short composition).  A justified pair needs NO per-program prover run —
   *  it is an instance of a ∀-certified law.  The AUTHORITATIVE law table is
   *  proofs/laws/REGISTRY.tsv (kind FILE/SCHEMATIC/GROUND/DEFINITIONAL; per-file prover verdicts
   *  in proofs/STATUS.tsv; kept in sync with SC.sourceLaws by scripts/check_laws.py) — this map
   *  mirrors it for the pair annotations the emitters write. */
  val lawCertificates: Map[String, String] = Map(
    "constant-ops" -> "GROUND — per-op threeway_*/impl_* characterizations, eval-gated (registry: constant-ops)",
    "algebraic-identities" -> "proofs/laws/law_{union_unit,inter_empty,sub_empty,union_idem,inter_idem,sub_self}.smt2",
    "iterate-singleton-deref" -> "proofs/keyfold_iter.smt2 (SCHEMATIC: singleton key list)",
    "literal-space-ops" -> "GROUND — per-op threeway_*/impl_* characterizations, eval-gated (registry: literal-space-ops)",
    "singleton-const-literal" -> "DEFINITIONAL (representation change)",
    "concat-singleton-iter" -> "proofs/keyfold_iter.smt2 (SCHEMATIC)",
    "iter-union-indep" -> "proofs/laws/law_guard_hoist.smt2 (+ the bare-hoist fail-check in formal.egg)",
    "unwrap-merge" -> "proofs/laws/law_unwrap_merge.smt2",
    "wrap-iter" -> "proofs/laws/law_guard_hoist.smt2",
    "iter-ident" -> "proofs/keyfold_iter.smt2 (SCHEMATIC)",
    "concat-path" -> "proofs/laws/law_append_assoc.smt2 (path constant folding)",
    "iterate-literal-union" -> "proofs/keyfold_iter.smt2 (SCHEMATIC: exact ground keys)",
    "unwrap-concat-unwraps" -> "proofs/laws/law_unwrap_merge.smt2",
    "singleton-composition-wrap" -> "proofs/laws/law_wrap_as_comp.smt2",
    "singleton-space-op-path-op" -> "proofs/laws/law_wrap_set.smt2 + proofs/laws/law_unwrap_set.smt2",
    "restriction-singleton-unwrap" -> "proofs/laws/law_restrict_set.smt2",
    "iter-tails" -> "proofs/laws/law_tailsu_set.smt2 + proofs/keyfolds.smt2",
    "tailsunion-singleton" -> "proofs/laws/law_tailsu_set.smt2",
    "range-singleton" -> "GROUND — trusted positional boundary (the design note); executor-evaluated",
    "unwrap-wrap" -> "proofs/laws/law_unwrap_set.smt2",
    "iter-transpose-semijoin" -> "proofs/laws/law_iter_transpose_semijoin.smt2 + laws/law_transpose_spec.smt2",
    "iter-witness-head-narrow" -> "proofs/laws/law_iter_head_narrow.smt2",
    "unwrap-push" -> "proofs/laws/law_unwrap_push.smt2",
    "wrap-merge" -> "proofs/laws/law_wrap_merge.smt2 + laws/law_wrap_disjoint.smt2",
    "restriction-push" -> "proofs/laws/law_restrict_push.smt2",
    "comp-wrap-assoc" -> "proofs/laws/law_comp_wrap_assoc.smt2",
    "comp-assoc-right" -> "proofs/laws/law_comp_assoc.smt2",
    "comp-lit-to-wraps" -> "proofs/laws/law_comp_lit_wraps.smt2",
    "unwrap-fuse-const" -> "proofs/laws/law_unwrap_merge.smt2",
    "singleton-constprefix-wrap" -> "proofs/laws/law_wrap_set.smt2",
    "iter-comp-right-hoist" -> "proofs/laws/law_iter_comp_right_hoist.smt2",
    "raffination-push" -> "proofs/laws/law_raff_push.smt2",
    "raff-restrict-algebra" -> "proofs/laws/law_raff_restrict_algebra.smt2",
    "restrict-raff-wrap-both" -> "proofs/laws/law_restrict_wrap_both.smt2 + laws/law_raff_wrap_both.smt2",
    "iter-setop-merge" -> "proofs/laws/law_iter_merge.smt2",
    "union-chain-tailsu" -> "proofs/laws/law_union_chain_tailsu.smt2")

  def justify(l: Space, r: Space): Option[String] =
    // EVERY comparison is modulo alpha-renaming: the two sides of a pair were alpha-normalised as
    // parts of two different whole programs, so their binder names differ even when the terms are
    // the same — measured on puzzle15's graph residual (2A.5), whose one-law-each-side join was
    // missed for exactly that reason and cost 240 s of prover time per prover.
    def same(a: Space, b: Space): Boolean = a == b || alphaNorm(a) == alphaNorm(b)
    def onceMatches(from: Space, to: Space): Option[String] =
      SC.sourceLaws.collectFirst { case (nm, fn) if same(fn(from), to) => nm }
    onceMatches(l, r).orElse(onceMatches(r, l)).orElse {
      // two-step composition (reduce applies laws to fixpoint; a pair may combine two laws)
      SC.sourceLaws.iterator.flatMap { (n1, f1) =>
        val mid = f1(l)
        if mid == l then Iterator.empty
        else SC.sourceLaws.iterator.collect { case (n2, f2) if same(f2(mid), r) => s"$n1 + $n2" }
      }.nextOption()
    }.orElse {
      // MEET IN THE MIDDLE: one law on each side reaching the same term.  A law is an EQUATION, so a
      // rewrite the optimiser applied right-to-left (the graph optimiser pushes a composition INTO an
      // iteration; the source law `iter-comp-right-hoist` is written hoisting it OUT) is justified by
      // applying the law to the OTHER side.  This is the case `SC.reduce`-based replay cannot see,
      // because it only ever rewrites left-to-right.
      SC.sourceLaws.iterator.flatMap { (n1, f1) =>
        val ml = f1(l)
        if ml == l then Iterator.empty
        else SC.sourceLaws.iterator.collect { case (n2, f2) if f2(r) != r && same(ml, f2(r)) => s"join: $n1 + $n2" }
      }.nextOption()
    }.orElse {
      // REPLAY/JOIN: the laws are LOCAL bottom-up traversals, so SC.reduce restricted to the
      // differing subtree replays the optimiser's own derivation.  Either exact reproduction of
      // the right side (replay) or both sides reducing to the SAME normal form (confluent join —
      // two certified-law derivations meeting) is proof-carrying: every step preserves semantics
      // universally, so l ≈ nf ≈ r.
      def nf(s: Space, names: scala.collection.mutable.LinkedHashSet[String]): Space =
        var cur = s; var steps = 0; var progress = true
        while progress && steps < 64 do
          progress = false; steps += 1
          for (nm, fn) <- SC.sourceLaws do
            val nxt = fn(cur)
            if nxt != cur then { names += nm; cur = nxt; progress = true }
        cur
      val names = scala.collection.mutable.LinkedHashSet.empty[String]
      val (nl, nr) = (nf(l, names), nf(r, names))
      if alphaNorm(nl) == alphaNorm(r) then Some(s"replay: ${names.mkString(" + ")}")
      else if alphaNorm(nl) == alphaNorm(nr) then Some(s"reduce-join: ${names.mkString(" + ")}")
      else None
    }

  def certificateOf(law: String): String =
    val parts = law.stripPrefix("replay: ").stripPrefix("reduce-join: ").stripPrefix("join: ").split(" \\+ ").toList
    parts.map(p => s"$p ⟶ ${lawCertificates.getOrElse(p, "certified law set")}").mkString("; ")

  /** Recursive pair refinement: an unjustified pair is NORMALISED on both sides by the certified
   *  law set (semantics-preserving ∀), re-diffed (AC-aware), and its sub-pairs refined again —
   *  the residual obligations shrink to the branches the derivations genuinely disagree on. */
  private def refine(m: Mismatch, depth: Int): List[Either[(Mismatch, String), Mismatch]] =
    val (l, r, ps, ss) = m
    justify(l, r) match
      case Some(law) => List(Left((m, law)))
      case None if depth > 0 =>
        val (nl, nr) = (alphaNorm(SC.reduce(l)), alphaNorm(SC.reduce(r)))
        val sub = diff(nl, nr, ps, ss)
        if sub.isEmpty then List(Left((m, "reduce-join")))
        else if (nl == l && nr == r) || sub == List((nl, nr, ps, ss)) then List(Right(m))
        else sub.flatMap(refine(_, depth - 1))
      case None => List(Right(m))
