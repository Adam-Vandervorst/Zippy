package morkl

import scala.collection.mutable.Stack

/** Trie-native executor for the RecursiveOpGraph — the `exec` analog that operates directly on
 *  interned [[ITrie]]s and interned int-paths, with NO intermediate `eval` calls and NO old
 *  `PathValue` allocations (the current `exec` rebuilds `Space.Literal`s and calls `eval` per
 *  node).  Stack slots hold either an `ITrie` (space) or a `List[Int]` (an interned path). */
def execT(rog: RecursiveOpGraph, stack: Stack[Array[Any | Null]],
          index: PartialFunction[String, RecursiveOpGraph] = PartialFunction.empty): Unit =
  val l = rog.level
  var c = 0
  val s = stack.top
  inline def pos = (l, c)
  extension (p: (Int, Int)) inline def sget: ITrie = stack(stack.length - 1 - p._1)(p._2).asInstanceOf[ITrie]
  extension (p: (Int, Int)) inline def pget: List[Int] = stack(stack.length - 1 - p._1)(p._2).asInstanceOf[List[Int]]
  while c < rog.nodes.length do
    rog.nodes(c) match
      case Left(Node(op, constant, kind, inputs)) => kind match
        case "path" => s(c) = (op match
          case "ExtractPathRef" => pos.pget
          case "Constant" => internConstStr(constant)
          case "Concat" => inputs(0).pget ++ inputs(1).pget)
        case "space" => s(c) = (op match
          case "Empty" => ITrie.empty
          case "Call" =>
            val code = index(constant)
            val cstack = Stack(new Array[Any | Null](code.nodes.length))
            for (arg, i) <- inputs.zipWithIndex do cstack.top(i) = stack(stack.length - 1 - arg._1)(arg._2)
            execT(code, cstack, index)
            cstack.top.last.asInstanceOf[ITrie]
          case "ExtractSpaceMention" => pos.sget
          case "Singleton" => ITrie.singleton(inputs(0).pget)
          case "Literal" => iLiteralStr(constant)
          case "Union" => ITrie.union(inputs(0).sget, inputs(1).sget)
          case "Intersection" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else ITrie.intersection(a, inputs(1).sget)
          case "Subtraction" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else ITrie.subtraction(a, inputs(1).sget)
          case "Restriction" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else ITrie.restriction(a, inputs(1).sget)
          case "Raffination" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else ITrie.raffination(a, inputs(1).sget)
          case "Composition" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else ITrie.composition(a, inputs(1).sget)
          case "Wrap" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else ITrie.wrap(inputs(1).pget, a)
          case "Unwrap" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else ITrie.unwrap(a, inputs(1).pget)
          case "TailsUnion" => ITrie.tailsUnion(inputs(0).sget)
          case "TailsIntersection" => ITrie.tailsIntersection(inputs(0).sget)
          case "Range" => val Array(lo, hi) = constant.split(",", 2).map(_.toInt); ITrie.range(inputs(0).sget, lo, hi)  // native ordered trie-slice
          case "Iteration" => throw IllegalStateException("Iteration should be a recursive subgraph")
          case other => throw IllegalStateException(s"execT: unsupported flat op $other"))
      case Right(sg: RecursiveOpGraph) =>
        sg.root.operation match
          case "Iteration" =>
            // each child of the source trie IS a (head, tail-trie) group — no regrouping.  Reuse ONE
            // body frame across children: execT overwrites every slot it reads, so no per-child
            // Array allocation / Stack churn is needed (hot in deep nested iterations, e.g. n-queens).
            val src = sg.root.inputs(0).sget
            val frame = new Array[Any | Null](sg.nodes.length)
            val last = sg.nodes.length - 1
            stack.push(frame)
            var acc = ITrie.empty
            src.children.foreach { case (k, sub) =>
              frame(0) = k :: Nil; frame(1) = sub
              execT(sg, stack, index)
              acc = ITrie.union(acc, frame(last).asInstanceOf[ITrie])
            }
            stack.pop()
            s(c) = acc
          case "Fixpoint" =>
            // lowered union-saturating recursion `r(m) = m ∪ r(next(m))`: faithfully match eval,
            // which unions `m` over every iterate m_0, next(m_0), next²(m_0), … and stops when the
            // argument stabilises (next(m)==m).  Accumulating the union (rather than returning the
            // final iterate) is correct for ANY `next`, not only extensive (monotone-growing) ones.
            val frame = new Array[Any | Null](sg.nodes.length)
            val last = sg.nodes.length - 1
            stack.push(frame)
            var cur = sg.root.inputs(0).sget
            var acc = cur
            var done = false
            while !done do
              frame(0) = cur
              execT(sg, stack, index)
              val nxt = frame(last).asInstanceOf[ITrie]
              if nxt == cur then done = true else { cur = nxt; acc = ITrie.union(acc, nxt) }
            stack.pop()
            s(c) = acc
          case other => throw IllegalStateException(s"execT: unsupported subgraph root $other")
    c += 1
  end while

/** Run a transpiled routine graph through [[execT]], binding inputs by NAME (robust to the
 *  optimizer reordering nodes): each top-level ExtractPathRef/ExtractSpaceMention slot is filled
 *  from `refs`/`mentions`.  `index` resolves any Call'd routines.  Returns the result [[ITrie]]. */
def runGraphT(g: RecursiveOpGraph, refs: Map[String, List[Int]] = Map.empty, mentions: Map[String, ITrie] = Map.empty,
              index: PartialFunction[String, RecursiveOpGraph] = PartialFunction.empty): ITrie =
  val frame = new Array[Any | Null](g.nodes.length)
  for (nl, i) <- g.nodes.iterator.zipWithIndex do nl match
    case Left(Node("ExtractPathRef", name, _, _)) => refs.get(name).foreach(frame(i) = _)
    case Left(Node("ExtractSpaceMention", name, _, _)) => mentions.get(name).foreach(frame(i) = _)
    case _ => ()
  val stack = Stack(frame)
  execT(g, stack, index)
  stack.top.last.asInstanceOf[ITrie]

/** Same, but through the original eval-based [[exec]] (SpaceValue stack), for comparison. */
def runGraph(g: RecursiveOpGraph, refs: Map[String, PathValue] = Map.empty, mentions: Map[String, SpaceValue] = Map.empty,
             index: PartialFunction[String, RecursiveOpGraph] = PartialFunction.empty): SpaceValue =
  val frame = new Array[PathValue | SpaceValue | Null](g.nodes.length)
  for (nl, i) <- g.nodes.iterator.zipWithIndex do nl match
    case Left(Node("ExtractPathRef", name, _, _)) => refs.get(name).foreach(frame(i) = _)
    case Left(Node("ExtractSpaceMention", name, _, _)) => mentions.get(name).foreach(frame(i) = _)
    case _ => ()
  val stack = Stack(frame)
  exec(g, stack, index)
  stack.top.last.asInstanceOf[SpaceValue]
