package morkl

/** Transpiler from the Scala [[SpaceZipper]] abstraction into the egglog `Z` term language modelled in
 *  `zipper.egg` / `zipper-egg-tests/prelude.egg`.  Every constructor maps one-to-one:
 *
 *    SpaceZipper.Lit(t)          ->  the trie `t` spelled out in the DENOTATIONAL vocabulary
 *                                    (Empty / Eps / Wrap1 k · / Union ·) — a concrete cursor
 *    Union/Intersection/         ->  (Union ·)/(Intersection ·)/(Subtraction ·)/(Composition ·)
 *      Subtraction/Composition
 *    Prefix(rem, src)            ->  nested (Wrap1 k ·) over the source           (the Wrap cursor)
 *    RestrictionNode(x, p)       ->  (Restr · ·)  (the restriction smart constructor)
 *    TailsUnion / TailsIntersection -> (TailsUnion ·) / (TailsIntersection ·)
 *
 *  Child keys are the SAME interned ints the trie uses, so the emitted program and the expected result
 *  (also emitted by [[eggOfTrie]]) share one vocabulary and are directly comparable under egglog. */
object ZipperEgg:
  import scala.collection.immutable.IntMap

  /** A concrete [[ITrie]] as an egg `Z` term in canonical (per-node, sorted-key) form:
   *  a node is `(Eps)` if terminal, `(Wrap1 k child)` per child, all combined by `(Union ..)`. */
  def eggOfTrie(t: ITrie): String =
    if t.isEmpty then "(Empty)"
    else
      val kids = t.children.toList.sortBy(_._1).map((k, c) => s"(Wrap1 $k ${eggOfTrie(c)})")
      val parts = (if t.terminal then List("(Eps)") else Nil) ++ kids
      parts.reduceLeft((a, b) => s"(Union $a $b)")

  /** A (possibly virtual) [[SpaceZipper]] as an egg `Z` term — the structural transpilation. */
  def eggOf(z: SpaceZipper): String = z match
    case SpaceZipper.Lit(t)               => eggOfTrie(t)
    case SpaceZipper.Union(a, b)          => s"(Union ${eggOf(a)} ${eggOf(b)})"
    case SpaceZipper.Intersection(a, b)   => s"(Intersection ${eggOf(a)} ${eggOf(b)})"
    case SpaceZipper.Subtraction(a, b)    => s"(Subtraction ${eggOf(a)} ${eggOf(b)})"
    case SpaceZipper.Composition(a, b)    => s"(Composition ${eggOf(a)} ${eggOf(b)})"
    case SpaceZipper.Prefix(rem, src)     => rem.foldRight(eggOf(src))((k, acc) => s"(Wrap1 $k $acc)")
    case SpaceZipper.RestrictionNode(x, p) => s"(Restr ${eggOf(x)} ${eggOf(p)})"
    case SpaceZipper.TailsUnion(s)        => s"(TailsUnion ${eggOf(s)})"
    case SpaceZipper.TailsIntersection(s) => s"(TailsIntersection ${eggOf(s)})"

  // ============================================================================================
  // Transpilation into the IMPLEMENTATION model (zipper-impl.egg): a trie is `(Node terminal
  // sorted-child-list)` and each operator transpiles to the matching recursive trie-op constructor,
  // so egglog RUNS the same set-operation recursion the Scala `ITrie`/`SpaceZipper.materialize` run.
  // ============================================================================================

  /** A concrete [[ITrie]] as an implementation-model `Tr`: `(Node T/F (CC k subtrie … (CNil)))`, the
   *  key-ascending child list the Patricia merges walk. */
  def trOfITrie(t: ITrie): String =
    val term = if t.terminal then "(T)" else "(F)"
    val kids = t.children.toList.sortBy(_._1).foldRight("(CNil)")((kc, acc) => s"(CC ${kc._1} ${trOfITrie(kc._2)} $acc)")
    s"(Node $term $kids)"

  /** A (virtual) [[SpaceZipper]] as an implementation-model `Tr` EXPRESSION — `TrU`/`TrI`/`TrS`/`TrC`/
   *  `TrR`/`TrW`/`TrTU`/`TrTI` — which egglog reduces by the modelled recursion to a canonical `Node`. */
  def implOf(z: SpaceZipper): String = z match
    case SpaceZipper.Lit(t)               => trOfITrie(t)
    case SpaceZipper.Union(a, b)          => s"(TrU ${implOf(a)} ${implOf(b)})"
    case SpaceZipper.Intersection(a, b)   => s"(TrI ${implOf(a)} ${implOf(b)})"
    case SpaceZipper.Subtraction(a, b)    => s"(TrS ${implOf(a)} ${implOf(b)})"
    case SpaceZipper.Composition(a, b)    => s"(TrC ${implOf(a)} ${implOf(b)})"
    case SpaceZipper.Prefix(rem, src)     => rem.foldRight(implOf(src))((k, acc) => s"(TrW $k $acc)")
    case SpaceZipper.RestrictionNode(x, p) => s"(TrR ${implOf(x)} ${implOf(p)})"
    case SpaceZipper.TailsUnion(s)        => s"(TrTU ${implOf(s)})"
    case SpaceZipper.TailsIntersection(s) => s"(TrTI ${implOf(s)})"

  /** A program asserting egglog's RECURSIVE IMPLEMENTATION, run on the transpiled zipper, computes the
   *  exact trie the Scala implementation (`execZ`) produced — i.e. the two implementations coincide. */
  def implCoincidenceProgram(prelude: String, title: String, z: SpaceZipper, result: ITrie): String =
    val sb = new StringBuilder
    sb.append(s"; AUTO-GENERATED — $title\n")
    sb.append("; egglog RUNS the modelled recursive set-operation implementation on the transpiled zipper\n")
    sb.append("; ($impl) and checks it reduces to exactly the trie the Scala implementation computed ($want).\n\n")
    sb.append(prelude).append('\n')
    sb.append(s"(let $$impl ${implOf(z)})\n")
    sb.append(s"(let $$want ${trOfITrie(result)})\n")
    sb.append("\n(run 400)\n\n")
    sb.append("(check (= $impl $want))\n")
    sb.toString

  /** Every interned item key occurring anywhere in a zipper — the program's vocabulary. */
  def keysOf(z: SpaceZipper): Set[Int] = z match
    case SpaceZipper.Lit(t)               => trieKeys(t)
    case SpaceZipper.Union(a, b)          => keysOf(a) ++ keysOf(b)
    case SpaceZipper.Intersection(a, b)   => keysOf(a) ++ keysOf(b)
    case SpaceZipper.Subtraction(a, b)    => keysOf(a) ++ keysOf(b)
    case SpaceZipper.Composition(a, b)    => keysOf(a) ++ keysOf(b)
    case SpaceZipper.Prefix(rem, src)     => rem.toSet ++ keysOf(src)
    case SpaceZipper.RestrictionNode(x, p) => keysOf(x) ++ keysOf(p)
    case SpaceZipper.TailsUnion(s)        => keysOf(s)
    case SpaceZipper.TailsIntersection(s) => keysOf(s)
  private def trieKeys(t: ITrie): Set[Int] =
    t.children.iterator.flatMap((k, c) => Iterator.single(k) ++ trieKeys(c)).toSet

  /** Build a self-contained egglog program that checks the transpiled zipper `z` denotes EXACTLY the set
   *  `execZ` computes — purely by DESCENT, the way a zipper is meant to be used, WITHOUT ever materialising
   *  the result.  For every member path you can descend to it (the focus is `Term`-true); for every
   *  non-member you cannot (`Term`-false / the descent dead-ends at ∅).  Non-members are the BOUNDARY: at
   *  every reachable node, each program-vocabulary key that is NOT a child there (these are exactly the
   *  branches a flat materialisation would have to consider and the zipper prunes locally).  No
   *  `materialize`, no result-trie equality — only `Term` and `Descend` moving the cursor. */
  def coincidenceProgram(prelude: String, title: String, z: SpaceZipper, result: ITrie): String =
    coincidenceProgramRaw(prelude, title, eggOf(z), keysOf(z), result)

  /** Same, but over an ALREADY-RENDERED egg space term (used by the virtual-workload emitters,
   *  e.g. the unrolled semi-naive TC where the egg expression is built directly). */
  def coincidenceProgramRaw(prelude: String, title: String, progTerm: String, progKeys: Set[Int], result: ITrie): String =
    val members: List[List[Int]] = ITrie.toPaths(result).iterator.map(p => Interner.internPath(p.items)).filter(_.nonEmpty).toList.sortBy(_.mkString(","))
    val vocab: List[Int] = (progKeys ++ trieKeys(result)).toList.sorted
    val nonMembers = scala.collection.mutable.ArrayBuffer.empty[List[Int]]
    def walk(node: ITrie, prefix: List[Int]): Unit =
      val present = node.children.keySet
      for k <- vocab if !present.contains(k) do nonMembers += (prefix :+ k)   // a vocab key absent here ⇒ a non-member
      node.children.foreach((k, c) => walk(c, prefix :+ k))
    walk(result, Nil)

    val sb = new StringBuilder
    sb.append(s"; AUTO-GENERATED — $title\n")
    sb.append("; Coincidence is checked PURELY BY MOVEMENT — the result trie is NEVER materialised here.\n")
    sb.append("; A CURSOR (Root $prog) is moved by Descend: for every member the focus is a member\n")
    sb.append("; (TermAt = T); for every boundary non-member it is not (TermAt = F); an absent key's focus\n")
    sb.append("; is the empty subspace.  Ascend inverts Descend (the zipper contract), checked per file.\n")
    sb.append("; For virtual cursors the Sub rules move LOCALLY through the operators — no operand is built.\n")
    sb.append("\n").append(prelude).append('\n')
    sb.append(s"(let $$prog $progTerm)\n")
    def cursorAlong(ids: List[Int]): String = ids.foldLeft("(Root $prog)")((acc, k) => s"(Descend $k $acc)")
    // observations must be let-bound BEFORE the run (a (check ..) does not trigger rewrites)
    sb.append("(let $root (TermAt (Root $prog)))\n")
    for (ids, i) <- members.zipWithIndex do sb.append(s"(let $$mem$i (TermAt ${cursorAlong(ids)}))\n")
    for (ids, i) <- nonMembers.zipWithIndex do sb.append(s"(let $$non$i (TermAt ${cursorAlong(ids)}))\n")
    sb.append("(let $absent (IsEmpty (FocusOf (Descend 999998 (Root $prog)))))\n")  // 999998: never interned
    val k0 = members.headOption.flatMap(_.headOption).getOrElse(0)
    sb.append(s"(let $$zipup (FocusOf (Ascend (Descend $k0 (Root $$prog)))))\n")     // Ascend ∘ Descend = id
    sb.append("\n(run 300)\n\n")
    sb.append(s"; ε ${if result.terminal then "IS" else "is NOT"} a member\n")
    sb.append(s"(check (= $$root ${if result.terminal then "(T)" else "(F)"}))\n")
    sb.append(s"; ${members.size} member path(s): each reachable by movement (focus TermAt = T)\n")
    for i <- members.indices do sb.append(s"(check (= $$mem$i (T)))\n")
    sb.append(s"; ${nonMembers.size} boundary non-member(s): each UNreachable (focus TermAt = F)\n")
    for i <- nonMembers.indices do sb.append(s"(check (= $$non$i (F)))\n")
    sb.append("(check (= $absent (T)))\n")
    sb.append("(check (= $zipup $prog))\n")
    sb.toString
