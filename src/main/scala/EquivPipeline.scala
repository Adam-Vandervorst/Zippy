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

  // ==============================================================================================
  // Renderers into the three certified egg vocabularies
  // ==============================================================================================
  private def itemsOf(p: Path): List[Int] = p match
    case Path.Constant(v) => Interner.internPath(v.items)
    case other => throw IllegalStateException(s"expand should have made paths constant: $other")

  /** formal.egg vocabulary (set-of-paths reference). */
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
  final class Smt:
    private val defs = new StringBuilder
    private var n = 0
    def fresh(prefix: String): String = { n += 1; s"${prefix}_$n" }
    def emit(s: String): Unit = defs.append(s).append('\n')
    def text: String = defs.toString
    /** STRUCTURAL SHARING: one macro per DISTINCT subterm, across BOTH sides of an obligation.
     *  Two effects, both measured on the instance legs (the un-folded sides, 2026-08-31):
     *    (a) size — puzzle15-zipper 339 895 → 41 172 chars, aunt-zipper 38 775 → 7 115,
     *        puzzle3-full-graph 711 906 → 56 KB: the two sides of a pipeline obligation share
     *        almost all of their literal leaves, and the un-shared encoder emitted each copy;
     *    (b) VACUITY BECOMES DECIDABLE AT THE ENCODER — if the two sides are the same term they
     *        now get the SAME macro name, so `smtEquivalence` can refuse to emit `(= (m p) (m p))`
     *        and write an honest marker instead (this is the plan-item-12 failure mode).
     *  Sharing is a naming change only: a define-fun is a definition, the goal is unchanged, and
     *  the prover still has to prove it (measured: aunt-space z3 0.02 s shared vs 0.02 s unshared,
     *  aunt-zipper times out at 120 s in BOTH forms — sharing buys size, not provability). */
    private val memo = scala.collection.mutable.HashMap.empty[Space, String]
    /** compile `s`; returns the name of a (define-fun <name> ((p Path)) Bool ...). */
    def den(s: Space): String = memo.getOrElseUpdate(s, denRaw(s))
    private def denRaw(s: Space): String =
      def pathTerm(ids: List[Int]): String = ids.foldRight("nil")((k, acc) => s"(cons $k $acc)")
      val name = fresh("m")
      val body = s match
        case Empty => "false"
        case Literal(v) =>
          val ps = v.paths.toList.map(p => Interner.internPath(p.items)).sortBy(_.mkString(","))
          if ps.isEmpty then "false" else ps.map(ids => s"(= p ${pathTerm(ids)})").mkString("(or ", " ", ")")
        case Singleton(pt) => s"(= p ${pathTerm(itemsOf(pt))})"
        case Union(a, b) => s"(or (${den(a)} p) (${den(b)} p))"
        case Intersection(a, b) => s"(and (${den(a)} p) (${den(b)} p))"
        case Subtraction(a, b) => s"(and (${den(a)} p) (not (${den(b)} p)))"
        case Composition(a, b) =>
          s"(exists ((q Path) (r Path)) (and (= p (append q r)) (${den(a)} q) (${den(b)} r)))"
        case Restriction(x, y) =>
          s"(and (${den(x)} p) (exists ((r Path)) (and (${den(y)} r) (isPrefix r p))))"
        case Raffination(x, y) => return den(Subtraction(x, Restriction(x, y)))
        case Wrap(src, pt) =>
          val inner = den(src); val ids = itemsOf(pt)
          // p = ids ++ q ∧ inner q — tester-free (vampire-friendly) existential form
          s"(exists ((q Path)) (and (= p ${ids.foldRight("q")((k, acc) => s"(cons $k $acc)")}) ($inner q)))"
        case Unwrap(src, pt) => s"(${den(src)} ${itemsOf(pt).foldRight("p")((k, acc) => s"(cons $k $acc)")})"
        case TailsUnion(src) => s"(exists ((h Int)) (${den(src)} (cons h p)))"
        case TailsIntersection(src) =>
          val inner = den(src)
          s"(and (exists ((h Int) (q Path)) ($inner (cons h q))) " +
            s"(forall ((h Int)) (=> (exists ((q Path)) ($inner (cons h q))) ($inner (cons h p)))))"
        case other => throw IllegalStateException(s"not local algebra: $other")
      emit(s"(define-fun $name ((p Path)) Bool $body)")
      name

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
    val smt = new Smt
    val na = smt.den(a); val nb = smt.den(b)
    if na == nb then
      return s"""; AUTO-GENERATED — $title
; IDENTICAL-STRUCTURE-NO-EQUIVALENCE-OBLIGATION: the two sides compile to the SAME shared
; membership macro — they are the same local-algebra term, so `(= ($na p) ($nb p))` expands to
; `true` and no prover would do any work on it.  The structural identity IS the equivalence
; result for this cell (it is checked in Scala, not asserted here); the optimiser/transpiler
; comparison that is NOT definitional for this stone is carried by the -agnostic twin.
"""
    val goal =
      if obs.isEmpty then s"(assert (not (forall ((p Path)) (= ($na p) ($nb p)))))"
      else obs.map(ids => ids.foldRight("nil")((k, acc) => s"(cons $k $acc)"))
              .map(pt => s"(= ($na $pt) ($nb $pt))").mkString("(assert (not (and ", " ", ")))")
    val body = s"${smt.text}\n$goal"
    s"""; AUTO-GENERATED — $title
; Both sides compiled to their denotational membership formulas over the same inputs;
; the goal (negated): the programs produce the SAME OUTPUT — ${if obs.isEmpty then "equal membership at EVERY path"
                                                              else s"equal membership at the ${obs.size} observation path(s)"}.
${prunedPrelude(body)}
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

  def substMention(s: Space, m: SpaceMention, r: Space): Space = s match
    case Mention(`m`) => r
    case Union(a, b) => Union(substMention(a, m, r), substMention(b, m, r))
    case Intersection(a, b) => Intersection(substMention(a, m, r), substMention(b, m, r))
    case Subtraction(a, b) => Subtraction(substMention(a, m, r), substMention(b, m, r))
    case Restriction(a, b) => Restriction(substMention(a, m, r), substMention(b, m, r))
    case Raffination(a, b) => Raffination(substMention(a, m, r), substMention(b, m, r))
    case Composition(a, b) => Composition(substMention(a, m, r), substMention(b, m, r))
    case Wrap(src, p) => Wrap(substMention(src, m, r), p)
    case Unwrap(src, p) => Unwrap(substMention(src, m, r), p)
    case TailsUnion(src) => TailsUnion(substMention(src, m, r))
    case TailsIntersection(src) => TailsIntersection(substMention(src, m, r))
    case Iteration(src, sym, rest, body) =>
      Iteration(substMention(src, m, r), sym, rest, if rest == m then body else substMention(body, m, r))
    case Fixpoint(init, rec, body) =>
      Fixpoint(substMention(init, m, r), rec, if rec == m then body else substMention(body, m, r))
    case Call(rp, refs, ms) => Call(rp, refs, ms.map(substMention(_, m, r)))
    case Range(x, lo, hi) => Range(substMention(x, m, r), lo, hi)
    case other => other

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
      case Fixpoint(init, rec, body) => go(init) && (rec.s == m.s || go(body))
      case other => !free(other)                            // Range / Call / grounded: unknown variance
    go(s)

  /** k-unroll recursive Calls; inline acyclic Calls; keep Fixpoint and everything else INTACT.
   *
   *  FIXPOINT IS NO LONGER UNROLLED (plan item 1).  It used to become
   *    `init ∪ F(init) ∪ F(F(init))` at k = 2, so the certificate stated "the 2-unrollings agree",
   *  never "the fixpoints agree"; the only reason for it was that neither downstream renderer could
   *  represent a `Fixpoint` at all.  Both can now — `renderZ` emits `(Fix init (BodyK …))` and
   *  `AgSmt.denRaw` emits an uninterpreted predicate with the two post-fixpoint axioms plus Park
   *  induction — so the binder survives to the provers.  Recursive `Call`s that no `asFixpoint`
   *  lowering turns into a `Fixpoint` are still k-unrolled and cut with a fresh shared free input;
   *  that residual is the honest remaining approximation and it is named in the emitted files. */
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
      def inlineOnce(depth: Int, args: Vector[Space]): Space =
        var b = body
        for (pr, arg) <- refns zip refs do b = substPathRef(b, pr, arg)
        for (mn, arg) <- mentionns zip args do b = substMention(b, mn, arg)
        expandCalls(b, depth)
      def expandCalls(b: Space, depth: Int): Space = b match
        case Call(`rp`, rs, ms) =>
          if depth >= k then Mention(SpaceMention(s"residual_${rp.s}_$depth"))
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
      var b = fixBody
      for (pr, arg) <- r.refs zip refs do b = substPathRef(b, pr, arg)
      for (mn, arg) <- r.mentions zip mentions do b = substMention(b, mn, unrollControl(arg, k))
      unrollControl(b, k)
    case other => other

  def substPathRef(s: Space, pr: PathRef, arg: Path): Space =
    def sp(p: Path): Path = p match
      case Path.Deref(`pr`) => arg
      case Path.Concat(l, r) => Path.Concat(sp(l), sp(r))
      case other => other
    s match
      case Singleton(p) => Singleton(sp(p))
      case Wrap(src, p) => Wrap(substPathRef(src, pr, arg), sp(p))
      case Unwrap(src, p) => Unwrap(substPathRef(src, pr, arg), sp(p))
      case Union(a, b) => Union(substPathRef(a, pr, arg), substPathRef(b, pr, arg))
      case Intersection(a, b) => Intersection(substPathRef(a, pr, arg), substPathRef(b, pr, arg))
      case Subtraction(a, b) => Subtraction(substPathRef(a, pr, arg), substPathRef(b, pr, arg))
      case Restriction(a, b) => Restriction(substPathRef(a, pr, arg), substPathRef(b, pr, arg))
      case Raffination(a, b) => Raffination(substPathRef(a, pr, arg), substPathRef(b, pr, arg))
      case Composition(a, b) => Composition(substPathRef(a, pr, arg), substPathRef(b, pr, arg))
      case TailsUnion(src) => TailsUnion(substPathRef(src, pr, arg))
      case TailsIntersection(src) => TailsIntersection(substPathRef(src, pr, arg))
      case Iteration(src, sym, rest, body) =>
        Iteration(substPathRef(src, pr, arg), sym, rest, if sym.s == pr.s then body else substPathRef(body, pr, arg))
      case Call(rp, refs, ms) => Call(rp, refs.map(sp), ms.map(substPathRef(_, pr, arg)))
      case Range(x, lo, hi) => Range(substPathRef(x, pr, arg), lo, hi)
      case other => other

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
        if !monotoneInMention(body, rec) then
          throw IllegalStateException(
            s"agnostic renderer: Fixpoint body is NOT monotone in ${rec.s} — the recursion variable " +
            "sits under a complement (Subtraction/Raffination right operand, or TailsIntersection), " +
            "so the least-post-fixpoint model would not denote the executor's iterate union")
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

  def usesPathRef(s: Space, name: String): Boolean =
    def up(p: Path): Boolean = p match
      case Path.Deref(pr) => pr.s == name
      case Path.Concat(l, r) => up(l) || up(r)
      case _ => false
    s match
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
      case Range(x, _, _) => usesPathRef(x, name)
      case _ => false

  def usesMention(s: Space, name: String): Boolean = s match
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
    case Range(x, _, _) => usesMention(x, name)
    case _ => false

  // ==============================================================================================
  // SMT compiler with free inputs and binder parameters
  // ==============================================================================================
  final class AgSmt:
    val defs = new StringBuilder
    val decls = scala.collection.mutable.LinkedHashSet.empty[String]
    private var n = 0
    def fresh(p: String): String = { n += 1; s"${p}_$n" }
    private val shared = scala.collection.mutable.HashMap.empty[Int, String]
    /** compile to a formula string over path term `pt`, with binder env (path var → SMT Int term). */
    def den(s: Space, pt: String, penv: Map[String, String], senv: Map[String, String]): String =
      // SHARE binder-free subterms as named define-funs: the k-unrolled programs duplicate large
      // subtrees (e.g. datalog's all/delta), and inlining them per occurrence is exponential.
      if penv.isEmpty && senv.isEmpty && !s.isInstanceOf[Space.Literal] && !s.isInstanceOf[Space.Mention] then
        val key = System.identityHashCode(s)
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
    // SOUNDNESS SIDE CONDITION: the axioms hold of ⋃ₙ Fⁿ(init) only when F is MONOTONE in `rec`;
    // [[AgnosticPipeline.monotoneInMention]] decides that syntactically and this method REFUSES to
    // emit rather than assert something unsound.
    private val fixMemo = scala.collection.mutable.HashMap.empty[(Space, Map[String, String], Map[String, String]), String]
    private val fixes = scala.collection.mutable.ArrayBuffer.empty[(String, Space, Space, SpaceMention, Map[String, String], Map[String, String])]
    def fixSym(fx: Space, init: Space, rec: SpaceMention, body: Space,
               penv: Map[String, String], senv: Map[String, String]): String =
      fixMemo.getOrElseUpdate((fx, penv, senv), {
        if !AgnosticPipeline.monotoneInMention(body, rec) then
          throw IllegalStateException(
            s"agnostic smt: Fixpoint body is NOT monotone in ${rec.s} — the recursion variable sits " +
            "under a complement (Subtraction/Raffination right operand, or TailsIntersection).  The " +
            "least-post-fixpoint axioms would then be false of the executor's iterate union, so no " +
            "first-class denotation is emitted (the caller must record an honest marker)")
        val f = fresh("fix")
        decls += s"(declare-fun $f (Path) Bool)"
        emitDef(s"; FIXPOINT $f — first-class: the LEAST post-fixpoint above init (never unrolled)")
        emitDef(s"(assert (forall ((zq Path)) (=> ${den(init, "zq", penv, senv)} ($f zq))))")
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

  /** Canonical alpha-normalisation of binder names (traversal order), so optimiser-induced binder
   *  renamings do not masquerade as structural differences (they previously produced REFLEXIVE
   *  diff obligations: both sides' differing name mapped to the same freed symbol). */
  def alphaNorm(s: Space): Space =
    var n = 0
    def fresh(): Int = { n += 1; n }
    def go(s: Space, pm: Map[String, String], mm: Map[String, String]): Space = s match
      case Union(a, b) => Union(go(a, pm, mm), go(b, pm, mm))
      case Intersection(a, b) => Intersection(go(a, pm, mm), go(b, pm, mm))
      case Subtraction(a, b) => Subtraction(go(a, pm, mm), go(b, pm, mm))
      case Restriction(a, b) => Restriction(go(a, pm, mm), go(b, pm, mm))
      case Raffination(a, b) => Raffination(go(a, pm, mm), go(b, pm, mm))
      case Composition(a, b) => Composition(go(a, pm, mm), go(b, pm, mm))
      case Wrap(src, p) => Wrap(go(src, pm, mm), rp(p, pm))
      case Unwrap(src, p) => Unwrap(go(src, pm, mm), rp(p, pm))
      case TailsUnion(src) => TailsUnion(go(src, pm, mm))
      case TailsIntersection(src) => TailsIntersection(go(src, pm, mm))
      case Range(x, lo, hi) => Range(go(x, pm, mm), lo, hi)
      case Singleton(p) => Singleton(rp(p, pm))
      case Mention(m) => Mention(SpaceMention(mm.getOrElse(m.s, m.s)))
      case Iteration(src, sym, rest, body) =>
        val i = fresh()
        val (ns, nr) = (s"av$i", s"ar$i")
        Iteration(go(src, pm, mm), PathRef(ns).known(1), SpaceMention(nr),
                  go(body, pm + (sym.s -> ns), mm + (rest.s -> nr)))
      case Fixpoint(init, rec, body) =>
        val i = fresh()
        val nr = s"af$i"
        Fixpoint(go(init, pm, mm), SpaceMention(nr), go(body, pm, mm + (rec.s -> nr)))
      case other => other
    def rp(p: Path, pm: Map[String, String]): Path = p match
      case Path.Deref(pr) => Path.Deref(PathRef(pm.getOrElse(pr.s, pr.s)).known(1))
      case Path.Concat(l, r) => Path.Concat(rp(l, pm), rp(r, pm))
      case other => other
    go(s, Map.empty, Map.empty)

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
    def onceMatches(from: Space, to: Space): Option[String] =
      SC.sourceLaws.collectFirst { case (nm, fn) if fn(from) == to => nm }
    onceMatches(l, r).orElse(onceMatches(r, l)).orElse {
      // two-step composition (reduce applies laws to fixpoint; a pair may combine two laws)
      SC.sourceLaws.iterator.flatMap { (n1, f1) =>
        val mid = f1(l)
        if mid == l then Iterator.empty
        else SC.sourceLaws.iterator.collect { case (n2, f2) if f2(mid) == r => s"$n1 + $n2" }
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
    val parts = law.stripPrefix("replay: ").stripPrefix("reduce-join: ").split(" \\+ ").toList
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
