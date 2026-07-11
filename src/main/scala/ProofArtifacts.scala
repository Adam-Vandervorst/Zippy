import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path as JPath, Paths}

object ProofArtifacts:
  type PathTuple = Vector[String]

  case class Ctx(alphabet: Vector[String], maxLen: Int, explicitPaths: Option[Vector[PathTuple]] = None):
    val paths: Vector[PathTuple] = explicitPaths match
      case Some(paths0) =>
        paths0.distinct.sortWith(ProofArtifacts.comparePaths(_, _) < 0)
      case None =>
        ProofArtifacts.atoms(maxLen, alphabet)
    val index: Map[PathTuple, Int] = paths.zipWithIndex.toMap
    val width: Int = paths.length
    val zero: String = bv(BigInt(0))
    val epsilon: String = mask(Vector(Vector.empty))

    def bv(value: BigInt): String = s"(_ bv$value $width)"

    def mask(paths0: Iterable[PathTuple]): String =
      val value = paths0.foldLeft(BigInt(0)) { (acc, path) =>
        index.get(path).fold(acc)(i => acc | (BigInt(1) << i))
      }
      bv(value)

    def bit(space: String, path: PathTuple): String =
      val i = index(path)
      s"(not (= (bvand $space ${bv(BigInt(1) << i)}) $zero))"

  def atoms(maxLen: Int, alphabet: Vector[String]): Vector[PathTuple] =
    def product(n: Int): Vector[PathTuple] =
      if n == 0 then Vector(Vector.empty)
      else
        for
          prefix <- product(n - 1)
          item <- alphabet
        yield prefix :+ item
    (Vector(Vector.empty[String]) ++ (1 to maxLen).toVector.flatMap(product))
      .sortWith(comparePaths(_, _) < 0)

  private def comparePaths(left: PathTuple, right: PathTuple): Int =
    val n = math.min(left.length, right.length)
    var i = 0
    while i < n do
      val c = left(i).compareTo(right(i))
      if c != 0 then return c
      i += 1
    left.length.compareTo(right.length)

  private def bor(parts0: Iterable[String], ctx: Ctx): String =
    val parts = parts0.filter(_ != ctx.zero).toVector
    if parts.isEmpty then ctx.zero
    else parts.tail.foldLeft(parts.head)((acc, part) => s"(bvor $acc $part)")

  private def bandBool(parts0: Iterable[String]): String =
    val parts = parts0.toVector
    if parts.isEmpty then "true"
    else if parts.length == 1 then parts.head
    else s"(and ${parts.mkString(" ")})"

  private def borBool(parts0: Iterable[String]): String =
    val parts = parts0.toVector
    if parts.isEmpty then "false"
    else if parts.length == 1 then parts.head
    else s"(or ${parts.mkString(" ")})"

  private def intSum(parts0: Iterable[String]): String =
    val parts = parts0.toVector
    if parts.isEmpty then "0"
    else if parts.length == 1 then parts.head
    else s"(+ ${parts.mkString(" ")})"

  private def clampInt(value: String, lo: String, hi: String): String =
    s"(ite (< $value $lo) $lo (ite (> $value $hi) $hi $value))"

  sealed trait SpaceExpr:
    def smt(ctx: Ctx): String
    def vars: Set[String] = Set.empty

  sealed trait BoolExpr:
    def smt(ctx: Ctx): String
    def vars: Set[String] = Set.empty

  case class Var(name: String) extends SpaceExpr:
    override def smt(ctx: Ctx): String = name
    override def vars: Set[String] = Set(name)

  case class Const(paths: Vector[PathTuple]) extends SpaceExpr:
    override def smt(ctx: Ctx): String = ctx.mask(paths)

  case class Raw(term: String, names: Set[String] = Set.empty) extends SpaceExpr:
    override def smt(ctx: Ctx): String = term
    override def vars: Set[String] = names

  val Empty: Const = Const(Vector.empty)
  val Eps: Const = Const(Vector(Vector.empty))

  def singleton(items: String*): Const = Const(Vector(items.toVector))

  case class Union(left: SpaceExpr, right: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String = s"(bvor ${left.smt(ctx)} ${right.smt(ctx)})"
    override def vars: Set[String] = left.vars ++ right.vars

  case class Intersection(left: SpaceExpr, right: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String = s"(bvand ${left.smt(ctx)} ${right.smt(ctx)})"
    override def vars: Set[String] = left.vars ++ right.vars

  case class Diff(left: SpaceExpr, right: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String = s"(bvand ${left.smt(ctx)} (bvnot ${right.smt(ctx)}))"
    override def vars: Set[String] = left.vars ++ right.vars

  case class Product(left: SpaceExpr, right: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val leftSmt = left.smt(ctx)
      val rightSmt = right.smt(ctx)
      val terms =
        for
          p <- ctx.paths
          q <- ctx.paths
          r = p ++ q
          if ctx.index.contains(r)
        yield
          val cond = bandBool(Vector(ctx.bit(leftSmt, p), ctx.bit(rightSmt, q)))
          s"(ite $cond ${ctx.mask(Vector(r))} ${ctx.zero})"
      bor(terms, ctx)
    override def vars: Set[String] = left.vars ++ right.vars

  case class Wrap(prefix: PathTuple, src: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      val terms =
        for
          q <- ctx.paths
          r = prefix ++ q
          if ctx.index.contains(r)
        yield s"(ite ${ctx.bit(srcSmt, q)} ${ctx.mask(Vector(r))} ${ctx.zero})"
      bor(terms, ctx)
    override def vars: Set[String] = src.vars

  case class Unwrap(src: SpaceExpr, prefix: PathTuple) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      val terms =
        for
          q <- ctx.paths
          r = prefix ++ q
          if ctx.index.contains(r)
        yield s"(ite ${ctx.bit(srcSmt, r)} ${ctx.mask(Vector(q))} ${ctx.zero})"
      bor(terms, ctx)
    override def vars: Set[String] = src.vars

  case class UnwrapBy(src: SpaceExpr, prefixes: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      val prefixesSmt = prefixes.smt(ctx)
      val terms =
        for
          prefix <- ctx.paths
          q <- ctx.paths
          r = prefix ++ q
          if ctx.index.contains(r)
        yield
          val cond = bandBool(Vector(ctx.bit(prefixesSmt, prefix), ctx.bit(srcSmt, r)))
          s"(ite $cond ${ctx.mask(Vector(q))} ${ctx.zero})"
      bor(terms, ctx)
    override def vars: Set[String] = src.vars ++ prefixes.vars

  case class Child(item: String, src: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String = Unwrap(src, Vector(item)).smt(ctx)
    override def vars: Set[String] = src.vars

  case class Iter(src: SpaceExpr,
                  body: (SpaceExpr, SpaceExpr) => SpaceExpr,
                  bodyVars: Set[String] = Set.empty,
                  label: String = "iter") extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcVars = src.vars
      val terms = ctx.alphabet.map { head =>
        val tail = Child(head, src)
        val tailSmt = tail.smt(ctx)
        val bodySmt = body(singleton(head), Raw(tailSmt, srcVars)).smt(ctx)
        s"(ite (not (= $tailSmt ${ctx.zero})) $bodySmt ${ctx.zero})"
      }
      bor(terms, ctx)
    override def vars: Set[String] =
      src.vars ++ bodyVars ++ body(Var(s"__${label}_head"), Var(s"__${label}_tail")).vars

  case class Restriction(src: SpaceExpr, prefixes: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      val prefixesSmt = prefixes.smt(ctx)
      val byPrefix = ctx.paths.map { prefix =>
        val kept = ctx.paths.filter(r => r.length >= prefix.length && r.take(prefix.length) == prefix)
        val selectSrc = bor(kept.map(r => s"(ite ${ctx.bit(srcSmt, r)} ${ctx.mask(Vector(r))} ${ctx.zero})"), ctx)
        s"(ite ${ctx.bit(prefixesSmt, prefix)} $selectSrc ${ctx.zero})"
      }
      bor(byPrefix, ctx)
    override def vars: Set[String] = src.vars ++ prefixes.vars

  case class Raffination(src: SpaceExpr, prefixes: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String = Diff(src, Restriction(src, prefixes)).smt(ctx)
    override def vars: Set[String] = src.vars ++ prefixes.vars

  case class NonEmpty(src: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String = s"(bvand ${src.smt(ctx)} (bvnot ${ctx.epsilon}))"
    override def vars: Set[String] = src.vars

  case class TailsUnion(src: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      val terms = ctx.paths.collect {
        case path if path.nonEmpty =>
          s"(ite ${ctx.bit(srcSmt, path)} ${ctx.mask(Vector(path.tail))} ${ctx.zero})"
      }
      bor(terms, ctx)
    override def vars: Set[String] = src.vars

  case class FrontierUnion(src: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String = TailsUnion(src).smt(ctx)
    override def vars: Set[String] = src.vars

  case class FrontierTailUnion(src: SpaceExpr, item: String) extends SpaceExpr:
    override def smt(ctx: Ctx): String = Child(item, src).smt(ctx)
    override def vars: Set[String] = src.vars

  case class FrontierChildUnion(src: SpaceExpr, item: String) extends SpaceExpr:
    override def smt(ctx: Ctx): String = Child(item, FrontierState(src)).smt(ctx)
    override def vars: Set[String] = src.vars

  case class FrontierState(active: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String = active.smt(ctx)
    override def vars: Set[String] = active.vars

  case class TailsIntersection(src: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      val childPresent = ctx.alphabet.map { head =>
        head -> borBool(ctx.paths.filter(path => path.nonEmpty && path.head == head).map(path => ctx.bit(srcSmt, path)))
      }.toMap
      val anyChild = borBool(childPresent.values)
      val terms = ctx.paths.map { tail =>
        val clauses = Vector(anyChild) ++ ctx.alphabet.map { head =>
          val full = head +: tail
          val hasFull = if ctx.index.contains(full) then ctx.bit(srcSmt, full) else "false"
          s"(or (not ${childPresent(head)}) $hasFull)"
        }
        s"(ite ${bandBool(clauses)} ${ctx.mask(Vector(tail))} ${ctx.zero})"
      }
      bor(terms, ctx)
    override def vars: Set[String] = src.vars

  case class Head(src: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      val terms = ctx.alphabet.map { head =>
        val present = borBool(ctx.paths.filter(path => path.nonEmpty && path.head == head).map(path => ctx.bit(srcSmt, path)))
        s"(ite $present ${ctx.mask(Vector(Vector(head)))} ${ctx.zero})"
      }
      bor(terms, ctx)
    override def vars: Set[String] = src.vars

  case class PatchChild(parent: SpaceExpr, item: String, replacement: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      Union(
        Diff(parent, Restriction(parent, singleton(item))),
        Wrap(Vector(item), replacement)
      ).smt(ctx)
    override def vars: Set[String] = parent.vars ++ replacement.vars

  case class PrefixClosure(src: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      val terms =
        for
          path <- ctx.paths
          if path.nonEmpty
          i <- 1 to path.length
        yield s"(ite ${ctx.bit(srcSmt, path)} ${ctx.mask(Vector(path.take(i)))} ${ctx.zero})"
      bor(terms, ctx)
    override def vars: Set[String] = src.vars

  case class SuffixClosure(src: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      val terms =
        for
          path <- ctx.paths
          if path.nonEmpty
          i <- 0 until path.length
        yield s"(ite ${ctx.bit(srcSmt, path)} ${ctx.mask(Vector(path.drop(i)))} ${ctx.zero})"
      bor(terms, ctx)
    override def vars: Set[String] = src.vars

  case class TailsClosure(src: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      s"(ite (= $srcSmt ${ctx.zero}) ${ctx.zero} (bvor ${ctx.epsilon} ${SuffixClosure(src).smt(ctx)}))"
    override def vars: Set[String] = src.vars

  case class Range(src: SpaceExpr, start: Int, end: Int) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      val count = intSum(ctx.paths.map(path => s"(ite ${ctx.bit(srcSmt, path)} 1 0)"))
      val lower =
        if start == 0 then "0"
        else if start > 0 then (start - 1).toString
        else s"(+ $count $start)"
      val upper =
        if end == 0 then count
        else if start == 0 && end > 0 then end.toString
        else if end > 0 then (end - 1).toString
        else s"(+ $count $end)"
      val lo = clampInt(lower, "0", count)
      val hi = clampInt(upper, "0", count)
      val nonEmptySlice = s"(> $hi $lo)"
      val terms = ctx.paths.zipWithIndex.map { (path, i) =>
        val rankBefore = intSum(ctx.paths.take(i).map(q => s"(ite ${ctx.bit(srcSmt, q)} 1 0)"))
        val cond = bandBool(Vector(
          nonEmptySlice,
          ctx.bit(srcSmt, path),
          s"(>= $rankBefore $lo)",
          s"(< $rankBefore $hi)",
        ))
        s"(ite $cond ${ctx.mask(Vector(path))} ${ctx.zero})"
      }
      bor(terms, ctx)
    override def vars: Set[String] = src.vars

  case class FixpointExpr(initial: SpaceExpr,
                          body: SpaceExpr => SpaceExpr,
                          bodyVars: Set[String] = Set.empty,
                          label: String = "fix") extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val names = (0 to ctx.width).map(i => s"__${label}_fp_$i").toVector
      val bindings = Vector.newBuilder[(String, String)]
      bindings += names.head -> initial.smt(ctx)
      var i = 0
      while i < ctx.width do
        val state = Raw(names(i), vars)
        bindings += names(i + 1) -> s"(bvor ${names(i)} ${body(state).smt(ctx)})"
        i += 1
      bindings.result().foldRight(names.last) { case ((name, value), inner) =>
        s"(let (($name $value)) $inner)"
      }
    override def vars: Set[String] =
      initial.vars ++ bodyVars ++ body(Var(s"__${label}_state")).vars

  case class IfNullable(src: SpaceExpr, yes: SpaceExpr, no: SpaceExpr = Empty) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      s"(ite ${ctx.bit(srcSmt, Vector.empty)} ${yes.smt(ctx)} ${no.smt(ctx)})"
    override def vars: Set[String] = src.vars ++ yes.vars ++ no.vars

  case class IfEmpty(src: SpaceExpr, yes: SpaceExpr, no: SpaceExpr) extends SpaceExpr:
    override def smt(ctx: Ctx): String =
      val srcSmt = src.smt(ctx)
      s"(ite (= $srcSmt ${ctx.zero}) ${yes.smt(ctx)} ${no.smt(ctx)})"
    override def vars: Set[String] = src.vars ++ yes.vars ++ no.vars

  case class NonEmptyAssumption(src: SpaceExpr) extends BoolExpr:
    override def smt(ctx: Ctx): String = s"(not (= ${src.smt(ctx)} ${ctx.zero}))"
    override def vars: Set[String] = src.vars

  case class WithinLength(src: SpaceExpr, maxLength: Int) extends BoolExpr:
    override def smt(ctx: Ctx): String =
      val allowed = ctx.mask(ctx.paths.filter(_.length <= maxLength))
      val srcSmt = src.smt(ctx)
      s"(= (bvand $srcSmt (bvnot $allowed)) ${ctx.zero})"
    override def vars: Set[String] = src.vars

  case class ProductClosed(left: SpaceExpr, right: SpaceExpr) extends BoolExpr:
    override def smt(ctx: Ctx): String =
      val leftSmt = left.smt(ctx)
      val rightSmt = right.smt(ctx)
      val clauses =
        for
          p <- ctx.paths
          q <- ctx.paths
          if !ctx.index.contains(p ++ q)
        yield s"(not ${bandBool(Vector(ctx.bit(leftSmt, p), ctx.bit(rightSmt, q)))})"
      bandBool(clauses)
    override def vars: Set[String] = left.vars ++ right.vars

  private final class SharedSmtEmitter(ctx: Ctx):
    private val bindings = scala.collection.mutable.ArrayBuffer.empty[(String, String)]
    private val cache = scala.collection.mutable.LinkedHashMap.empty[String, String]
    private val identityIds = java.util.IdentityHashMap[AnyRef, String]()
    private var nextBinding = 0
    private var nextIdentity = 0

    def renderSpace(expr: SpaceExpr): String = wrap(emitSpace(expr))

    def renderBool(expr: BoolExpr): String = wrap(emitBool(expr))

    def renderDisequality(lhs: SpaceExpr, rhs: SpaceExpr): String =
      val left = emitSpace(lhs)
      val right = emitSpace(rhs)
      wrap(s"(not (= $left $right))")

    private def fresh(): String =
      val out = s"__pa_$nextBinding"
      nextBinding += 1
      out

    private def wrap(root: String): String =
      bindings.foldRight(root) { case ((name, term), inner) =>
        s"(let (($name $term)) $inner)"
      }

    private def identityKey(x: AnyRef): String =
      val cached = identityIds.get(x)
      if cached != null then cached
      else
        val out = s"id${nextIdentity}"
        nextIdentity += 1
        identityIds.put(x, out)
        out

    private def bind(kind: String, key: String, term: => String): String =
      val fullKey = s"$kind:$key"
      cache.getOrElseUpdate(fullKey, {
        val name = fresh()
        bindings += name -> term
        name
      })

    private def emitSpace(expr: SpaceExpr): String = expr match
      case Var(name) => name
      case Const(paths) => ctx.mask(paths)
      case Raw(term, _) => term
      case Union(left, right) =>
        bind("space", spaceKey(expr), s"(bvor ${emitSpace(left)} ${emitSpace(right)})")
      case Intersection(left, right) =>
        bind("space", spaceKey(expr), s"(bvand ${emitSpace(left)} ${emitSpace(right)})")
      case Diff(left, right) =>
        bind("space", spaceKey(expr), s"(bvand ${emitSpace(left)} (bvnot ${emitSpace(right)}))")
      case Product(left, right) =>
        bind("space", spaceKey(expr), {
          val leftSmt = emitSpace(left)
          val rightSmt = emitSpace(right)
          val terms =
            for
              p <- ctx.paths
              q <- ctx.paths
              r = p ++ q
              if ctx.index.contains(r)
            yield
              val cond = bandBool(Vector(ctx.bit(leftSmt, p), ctx.bit(rightSmt, q)))
              s"(ite $cond ${ctx.mask(Vector(r))} ${ctx.zero})"
          bor(terms, ctx)
        })
      case Wrap(prefix, src) =>
        bind("space", spaceKey(expr), {
          val srcSmt = emitSpace(src)
          val terms =
            for
              q <- ctx.paths
              r = prefix ++ q
              if ctx.index.contains(r)
            yield s"(ite ${ctx.bit(srcSmt, q)} ${ctx.mask(Vector(r))} ${ctx.zero})"
          bor(terms, ctx)
        })
      case Unwrap(src, prefix) =>
        bind("space", spaceKey(expr), {
          val srcSmt = emitSpace(src)
          val terms =
            for
              q <- ctx.paths
              r = prefix ++ q
              if ctx.index.contains(r)
            yield s"(ite ${ctx.bit(srcSmt, r)} ${ctx.mask(Vector(q))} ${ctx.zero})"
          bor(terms, ctx)
        })
      case UnwrapBy(src, prefixes) =>
        bind("space", spaceKey(expr), {
          val srcSmt = emitSpace(src)
          val prefixesSmt = emitSpace(prefixes)
          val terms =
            for
              prefix <- ctx.paths
              q <- ctx.paths
              r = prefix ++ q
              if ctx.index.contains(r)
            yield
              val cond = bandBool(Vector(ctx.bit(prefixesSmt, prefix), ctx.bit(srcSmt, r)))
              s"(ite $cond ${ctx.mask(Vector(q))} ${ctx.zero})"
          bor(terms, ctx)
        })
      case Child(item, src) =>
        bind("space", spaceKey(expr), emitSpace(Unwrap(src, Vector(item))))
      case iter @ Iter(src, body, _, label) =>
        bind("space", spaceKey(iter), {
          val srcSmt = emitSpace(src)
          val srcVars = src.vars
          val terms = ctx.alphabet.map { head =>
            val tailSmt = emitSpace(Child(head, Raw(srcSmt, srcVars)))
            val bodySmt = emitSpace(body(singleton(head), Raw(tailSmt, srcVars)))
            s"(ite (not (= $tailSmt ${ctx.zero})) $bodySmt ${ctx.zero})"
          }
          bor(terms, ctx)
        })
      case Restriction(src, prefixes) =>
        bind("space", spaceKey(expr), {
          val srcSmt = emitSpace(src)
          val prefixesSmt = emitSpace(prefixes)
          val byPrefix = ctx.paths.map { prefix =>
            val kept = ctx.paths.filter(r => r.length >= prefix.length && r.take(prefix.length) == prefix)
            val selectSrc = bor(kept.map(r => s"(ite ${ctx.bit(srcSmt, r)} ${ctx.mask(Vector(r))} ${ctx.zero})"), ctx)
            s"(ite ${ctx.bit(prefixesSmt, prefix)} $selectSrc ${ctx.zero})"
          }
          bor(byPrefix, ctx)
        })
      case Raffination(src, prefixes) =>
        bind("space", spaceKey(expr), emitSpace(Diff(src, Restriction(src, prefixes))))
      case NonEmpty(src) =>
        bind("space", spaceKey(expr), s"(bvand ${emitSpace(src)} (bvnot ${ctx.epsilon}))")
      case TailsUnion(src) =>
        bind("space", spaceKey(expr), {
          val srcSmt = emitSpace(src)
          val terms = ctx.paths.collect {
            case path if path.nonEmpty =>
              s"(ite ${ctx.bit(srcSmt, path)} ${ctx.mask(Vector(path.tail))} ${ctx.zero})"
          }
          bor(terms, ctx)
        })
      case FrontierUnion(src) =>
        bind("space", spaceKey(expr), emitSpace(TailsUnion(src)))
      case FrontierTailUnion(src, item) =>
        bind("space", spaceKey(expr), emitSpace(Child(item, src)))
      case FrontierChildUnion(src, item) =>
        bind("space", spaceKey(expr), emitSpace(Child(item, FrontierState(src))))
      case FrontierState(active) =>
        bind("space", spaceKey(expr), emitSpace(active))
      case TailsIntersection(src) =>
        bind("space", spaceKey(expr), {
          val srcSmt = emitSpace(src)
          val childPresent = ctx.alphabet.map { head =>
            head -> bind("bool", s"tails-inter-child:${spaceKey(src)}:$head",
              borBool(ctx.paths.filter(path => path.nonEmpty && path.head == head).map(path => ctx.bit(srcSmt, path))))
          }.toMap
          val anyChild = bind("bool", s"tails-inter-any:${spaceKey(src)}", borBool(childPresent.values))
          val terms = ctx.paths.map { tail =>
            val clauses = Vector(anyChild) ++ ctx.alphabet.map { head =>
              val full = head +: tail
              val hasFull = if ctx.index.contains(full) then ctx.bit(srcSmt, full) else "false"
              s"(or (not ${childPresent(head)}) $hasFull)"
            }
            s"(ite ${bandBool(clauses)} ${ctx.mask(Vector(tail))} ${ctx.zero})"
          }
          bor(terms, ctx)
        })
      case Head(src) =>
        bind("space", spaceKey(expr), {
          val srcSmt = emitSpace(src)
          val terms = ctx.alphabet.map { head =>
            val present = borBool(ctx.paths.filter(path => path.nonEmpty && path.head == head).map(path => ctx.bit(srcSmt, path)))
            s"(ite $present ${ctx.mask(Vector(Vector(head)))} ${ctx.zero})"
          }
          bor(terms, ctx)
        })
      case PatchChild(parent, item, replacement) =>
        bind("space", spaceKey(expr),
          emitSpace(Union(
            Diff(parent, Restriction(parent, singleton(item))),
            Wrap(Vector(item), replacement)
          ))
        )
      case PrefixClosure(src) =>
        bind("space", spaceKey(expr), {
          val srcSmt = emitSpace(src)
          val terms =
            for
              path <- ctx.paths
              if path.nonEmpty
              i <- 1 to path.length
            yield s"(ite ${ctx.bit(srcSmt, path)} ${ctx.mask(Vector(path.take(i)))} ${ctx.zero})"
          bor(terms, ctx)
        })
      case SuffixClosure(src) =>
        bind("space", spaceKey(expr), {
          val srcSmt = emitSpace(src)
          val terms =
            for
              path <- ctx.paths
              if path.nonEmpty
              i <- 0 until path.length
            yield s"(ite ${ctx.bit(srcSmt, path)} ${ctx.mask(Vector(path.drop(i)))} ${ctx.zero})"
          bor(terms, ctx)
        })
      case TailsClosure(src) =>
        bind("space", spaceKey(expr), {
          val srcSmt = emitSpace(src)
          s"(ite (= $srcSmt ${ctx.zero}) ${ctx.zero} (bvor ${ctx.epsilon} ${emitSpace(SuffixClosure(src))}))"
        })
      case Range(src, start, end) =>
        bind("space", spaceKey(expr), {
          val srcSmt = emitSpace(src)
          val srcKey = spaceKey(src)
          val count = bind("int", s"range-count:$srcKey", intSum(ctx.paths.map(path => s"(ite ${ctx.bit(srcSmt, path)} 1 0)")))
          val lower =
            if start == 0 then "0"
            else if start > 0 then (start - 1).toString
            else s"(+ $count $start)"
          val upper =
            if end == 0 then count
            else if start == 0 && end > 0 then end.toString
            else if end > 0 then (end - 1).toString
            else s"(+ $count $end)"
          val lo = bind("int", s"range-lo:$srcKey:$start:$end", clampInt(lower, "0", count))
          val hi = bind("int", s"range-hi:$srcKey:$start:$end", clampInt(upper, "0", count))
          val nonEmptySlice = bind("bool", s"range-nonempty:$srcKey:$start:$end", s"(> $hi $lo)")
          val terms = ctx.paths.zipWithIndex.map { (path, i) =>
            val rankBefore = bind("int", s"range-rank:$srcKey:$i", intSum(ctx.paths.take(i).map(q => s"(ite ${ctx.bit(srcSmt, q)} 1 0)")))
            val cond = bandBool(Vector(
              nonEmptySlice,
              ctx.bit(srcSmt, path),
              s"(>= $rankBefore $lo)",
              s"(< $rankBefore $hi)",
            ))
            s"(ite $cond ${ctx.mask(Vector(path))} ${ctx.zero})"
          }
          bor(terms, ctx)
        })
      case fix @ FixpointExpr(initial, body, _, label) =>
        bind("space", spaceKey(fix), {
          var current = emitSpace(initial)
          var i = 0
          while i < ctx.width do
            val bodySmt = emitSpace(body(Raw(current)))
            current = bind("space", s"fix-step:${identityKey(fix)}:$i", s"(bvor $current $bodySmt)")
            i += 1
          current
        })
      case IfNullable(src, yes, no) =>
        bind("space", spaceKey(expr), s"(ite ${ctx.bit(emitSpace(src), Vector.empty)} ${emitSpace(yes)} ${emitSpace(no)})")
      case IfEmpty(src, yes, no) =>
        bind("space", spaceKey(expr), {
          val srcSmt = emitSpace(src)
          s"(ite (= $srcSmt ${ctx.zero}) ${emitSpace(yes)} ${emitSpace(no)})"
        })

    private def emitBool(expr: BoolExpr): String = expr match
      case NonEmptyAssumption(src) =>
        bind("bool", s"nonempty:${spaceKey(src)}", s"(not (= ${emitSpace(src)} ${ctx.zero}))")
      case WithinLength(src, maxLength) =>
        bind("bool", s"within:${spaceKey(src)}:$maxLength", {
          val allowed = ctx.mask(ctx.paths.filter(_.length <= maxLength))
          val srcSmt = emitSpace(src)
          s"(= (bvand $srcSmt (bvnot $allowed)) ${ctx.zero})"
        })
      case ProductClosed(left, right) =>
        bind("bool", s"product-closed:${spaceKey(left)}:${spaceKey(right)}", {
          val leftSmt = emitSpace(left)
          val rightSmt = emitSpace(right)
          val clauses =
            for
              p <- ctx.paths
              q <- ctx.paths
              if !ctx.index.contains(p ++ q)
            yield s"(not ${bandBool(Vector(ctx.bit(leftSmt, p), ctx.bit(rightSmt, q)))})"
          bandBool(clauses)
        })

    private def spaceKey(expr: SpaceExpr): String = expr match
      case Var(name) => s"var:$name"
      case Const(paths) => s"const:${paths.map(_.mkString(".")).mkString(";")}"
      case Raw(term, _) => s"raw:$term"
      case Union(left, right) => s"union(${spaceKey(left)},${spaceKey(right)})"
      case Intersection(left, right) => s"inter(${spaceKey(left)},${spaceKey(right)})"
      case Diff(left, right) => s"diff(${spaceKey(left)},${spaceKey(right)})"
      case Product(left, right) => s"product(${spaceKey(left)},${spaceKey(right)})"
      case Wrap(prefix, src) => s"wrap(${prefix.mkString(".")},${spaceKey(src)})"
      case Unwrap(src, prefix) => s"unwrap(${spaceKey(src)},${prefix.mkString(".")})"
      case UnwrapBy(src, prefixes) => s"unwrap-by(${spaceKey(src)},${spaceKey(prefixes)})"
      case Child(item, src) => s"child($item,${spaceKey(src)})"
      case x: Iter => s"iter:${identityKey(x)}"
      case Restriction(src, prefixes) => s"restriction(${spaceKey(src)},${spaceKey(prefixes)})"
      case Raffination(src, prefixes) => s"raffination(${spaceKey(src)},${spaceKey(prefixes)})"
      case NonEmpty(src) => s"nonempty(${spaceKey(src)})"
      case TailsUnion(src) => s"tails-union(${spaceKey(src)})"
      case FrontierUnion(src) => s"frontier-union(${spaceKey(src)})"
      case FrontierTailUnion(src, item) => s"frontier-tail-union(${spaceKey(src)},$item)"
      case FrontierChildUnion(src, item) => s"frontier-child-union(${spaceKey(src)},$item)"
      case FrontierState(active) => s"frontier-state(${spaceKey(active)})"
      case TailsIntersection(src) => s"tails-intersection(${spaceKey(src)})"
      case Head(src) => s"head(${spaceKey(src)})"
      case PatchChild(parent, item, replacement) => s"patch-child(${spaceKey(parent)},$item,${spaceKey(replacement)})"
      case PrefixClosure(src) => s"prefix-closure(${spaceKey(src)})"
      case SuffixClosure(src) => s"suffix-closure(${spaceKey(src)})"
      case TailsClosure(src) => s"tails-closure(${spaceKey(src)})"
      case Range(src, start, end) => s"range(${spaceKey(src)},$start,$end)"
      case x: FixpointExpr => s"fix:${identityKey(x)}"
      case IfNullable(src, yes, no) => s"if-nullable(${spaceKey(src)},${spaceKey(yes)},${spaceKey(no)})"
      case IfEmpty(src, yes, no) => s"if-empty(${spaceKey(src)},${spaceKey(yes)},${spaceKey(no)})"

  case class Law(name: String,
                 lhs: SpaceExpr,
                 rhs: SpaceExpr,
                 expected: String = "unsat",
                 note: String = "",
                 assumptions: Vector[BoolExpr] = Vector.empty):
    def variables: Vector[String] =
      (lhs.vars ++ rhs.vars ++ assumptions.flatMap(_.vars)).toVector.sorted

    def smt2(ctx: Ctx): String =
      val decls = variables.map(v => s"(declare-const $v (_ BitVec ${ctx.width}))").mkString("\n")
      val emitter = SharedSmtEmitter(ctx)
      val assumptionText = assumptions.map { a =>
        (assumptionComments(a, ctx) :+ s"(assert ${emitter.renderBool(a)})").mkString("\n")
      }.mkString("\n")
      Vector(
        "; Generated by morkl.ProofArtifactGeneratorMain",
        s"; $name",
        s"; expected: $expected",
        s"; alphabet: ${ctx.alphabet.mkString(",")} max-len: ${ctx.maxLen} width: ${ctx.width}",
        "(set-option :produce-models true)",
        "(set-logic ALL)",
        decls,
        assumptionText,
        s"(assert ${emitter.renderDisequality(lhs, rhs)})",
        "(check-sat)",
        "(get-model)",
        "",
      ).filter(_.nonEmpty).mkString("\n")

    private def assumptionComments(assumption: BoolExpr, ctx: Ctx): Vector[String] = assumption match
      case ProductClosed(_, _) =>
        val escapingPairs =
          for
            p <- ctx.paths
            q <- ctx.paths
            if !ctx.index.contains(p ++ q)
          yield (p, q)
        Vector(
          "; assumption: ProductClosed(left,right)",
          "; principle: no concatenation escapes the bounded universe.",
          s"; generated guard: forbids exactly ${escapingPairs.length} left/right path pairs whose concatenation is outside the ${ctx.width}-path universe.",
          "; this is not a hand-picked mask: the pair list is derived from alphabet/max-len and the current bounded path index.",
        )
      case WithinLength(_, maxLength) =>
        Vector(
          s"; assumption: all paths in the source have length <= $maxLength.",
          "; generated guard: masks out every path above that bound in the current bounded universe.",
        )
      case NonEmptyAssumption(_) =>
        Vector(
          "; assumption: source is non-empty in the current bounded universe.",
        )

  def laws: Vector[Law] =
    val x = Var("X")
    val y = Var("Y")
    val z = Var("Z")
    val p = Var("P")
    val q = Var("Q")
    val a = "a"
    val b = "b"
    val sa = singleton(a)
    val sb = singleton(b)
    def iterTail(src: SpaceExpr): Iter = Iter(src, (_head, tail) => tail, label = "tail")
    def iterHead(src: SpaceExpr): Iter = Iter(src, (head, _tail) => head, label = "head")
    def iterReconstruct(src: SpaceExpr): Iter = Iter(src, (head, tail) => Product(head, tail), label = "reconstruct")
    def iterPrefixedReconstruct(src: SpaceExpr, prefix: PathTuple): Iter =
      Iter(src, (head, tail) => Product(Wrap(prefix, head), tail), label = "prefixed-reconstruct")
    def iterRangeTail(src: SpaceExpr, start: Int, end: Int): Iter =
      Iter(src, (_head, tail) => Range(tail, start, end), label = s"range-tail-$start-$end")
    def iterRangeReconstruct(src: SpaceExpr, start: Int, end: Int): Iter =
      Iter(src, (head, tail) => Product(head, Range(tail, start, end)), label = s"range-reconstruct-$start-$end")
    def iterPrefixedRangeReconstruct(src: SpaceExpr, prefix: PathTuple, start: Int, end: Int): Iter =
      Iter(src, (head, tail) => Product(Wrap(prefix, head), Range(tail, start, end)), label = s"prefixed-range-reconstruct-$start-$end")
    def fixpointTail(src: SpaceExpr): FixpointExpr =
      FixpointExpr(src, state => TailsUnion(state), label = "tail")
    def fixpointHead(src: SpaceExpr): FixpointExpr =
      FixpointExpr(src, state => Head(state), label = "head")
    def fixpointReconstruct(src: SpaceExpr): FixpointExpr =
      FixpointExpr(src, state => NonEmpty(state), label = "reconstruct")
    def fixpointPrefixedReconstruct(src: SpaceExpr, prefix: PathTuple): FixpointExpr =
      FixpointExpr(src, state => iterPrefixedReconstruct(state, prefix), label = s"prefixed-reconstruct-${prefix.mkString(".")}")
    def fixpointRangeTail(src: SpaceExpr, start: Int, end: Int): FixpointExpr =
      FixpointExpr(src, state => iterRangeTail(state, start, end), label = s"range-tail-$start-$end")
    def fixpointRangeReconstruct(src: SpaceExpr, start: Int, end: Int): FixpointExpr =
      FixpointExpr(src, state => iterRangeReconstruct(state, start, end), label = s"range-reconstruct-$start-$end")
    def fixpointPrefixedRangeReconstruct(src: SpaceExpr, prefix: PathTuple, start: Int, end: Int): FixpointExpr =
      FixpointExpr(src, state => iterPrefixedRangeReconstruct(state, prefix, start, end), label = s"prefixed-range-reconstruct-${prefix.mkString(".")}-$start-$end")
    def iterConst(src: SpaceExpr, body: SpaceExpr, bodyVars: String*): Iter =
      Iter(src, (_head, _tail) => body, bodyVars = bodyVars.toSet, label = "const")
    val iterConstY = Iter(x, (_head, _tail) => y, bodyVars = Set("Y"), label = "const-y")
    val puzzleEdges = Const(Vector(Vector(a, b), Vector(b, a)))
    val nqueensUpto2 = Const(Vector(Vector(a), Vector(b)))
    val nqueensTaken = sa
    val rangeBorderFixture = Const(Vector(Vector.empty[String], Vector(a, a), Vector(a, b), Vector(b, a)))
    val rangeNoEpsilonFixture = Const(Vector(Vector(a, b), Vector(b, a)))
    val sameHeadRangeFixture = Const(Vector(Vector(a, a), Vector(a, b)))
    val sameHeadRangeFixtureB = Const(Vector(Vector(b, a), Vector(b, b)))
    val rangeItemFixture = Const(Vector(Vector(a), Vector(b)))
    def generatedNegative(name: String,
                          lhs: SpaceExpr,
                          rhs: SpaceExpr,
                          assumptions: Vector[BoolExpr] = Vector.empty,
                          note: String = ""): Law =
      Law(
        s"bad_${name}_generated_negative_control",
        lhs,
        rhs,
        expected = "sat",
        note = note,
        assumptions = assumptions,
      )
    val generatedNegativeControls = Vector(
      generatedNegative("union_as_intersection", Union(x, y), Intersection(x, y)),
      generatedNegative("intersection_as_union", Intersection(x, y), Union(x, y)),
      generatedNegative("diff_as_intersection", Diff(x, y), Intersection(x, y)),
      generatedNegative("restriction_as_raffination", Restriction(x, p), Raffination(x, p)),
      generatedNegative("wrap_unwrap_wrong_prefix", Unwrap(Wrap(Vector(a), x), Vector(b)), x),
      generatedNegative("product_commutative", Product(x, y), Product(y, x)),
      generatedNegative(
        "child_union_as_child_intersection",
        Child(a, Union(x, y)),
        Intersection(Child(a, x), Child(a, y)),
      ),
      generatedNegative("tails_union_as_head", TailsUnion(x), Head(x)),
      generatedNegative("child_tails_union_a_drops_b_frontier", Child(a, TailsUnion(x)), Child(a, Child(a, x))),
      generatedNegative("child_tails_closure_a_is_child_source", Child(a, TailsClosure(x)), Child(a, x)),
      generatedNegative("antimirov_suffix_frontier_state_is_source_child", FrontierState(FrontierTailUnion(SuffixClosure(x), a)), Child(a, x)),
      generatedNegative("antimirov_tails_frontier_state_is_source_child", FrontierState(FrontierTailUnion(TailsClosure(x), a)), Child(a, x)),
      generatedNegative("tails_intersection_as_tails_union", TailsIntersection(x), TailsUnion(x)),
      generatedNegative("prefix_closure_identity", PrefixClosure(x), x),
      generatedNegative("suffix_closure_identity", SuffixClosure(x), x),
      generatedNegative("tails_closure_identity", TailsClosure(x), x),
      generatedNegative("tails_closure_without_base", TailsClosure(x), TailsUnion(TailsClosure(x))),
      generatedNegative("nonempty_identity", NonEmpty(x), x),
      generatedNegative("head_identity", Head(x), x),
      generatedNegative("patch_child_identity", PatchChild(x, a, y), x),
      generatedNegative("iteration_reconstruct_identity", iterReconstruct(x), x),
      generatedNegative("iteration_tail_union_as_intersection", iterTail(Union(x, y)), Intersection(iterTail(x), iterTail(y))),
      generatedNegative("iteration_range_tail_first_is_tail_union", iterRangeTail(x, 0, 1), TailsUnion(x)),
      generatedNegative("iteration_range_reconstruct_first_is_nonempty", iterRangeReconstruct(x, 0, 1), NonEmpty(x)),
      generatedNegative("iteration_range_tail_same_head_split_frontier", iterRangeTail(sameHeadRangeFixture, 0, 1), TailsUnion(sameHeadRangeFixture)),
      generatedNegative("child_same_head_union_a_drops_second", Child(a, sameHeadRangeFixture), singleton(a)),
      generatedNegative("child_same_head_union_b_drops_second", Child(b, sameHeadRangeFixtureB), singleton(a)),
      generatedNegative("fixpoint_tail_identity", fixpointTail(x), x),
      generatedNegative("fixpoint_tail_without_base", fixpointTail(x), iterTail(fixpointTail(x))),
      generatedNegative("fixpoint_head_identity", fixpointHead(x), x),
      generatedNegative("fixpoint_reconstruct_as_nonempty", fixpointReconstruct(x), NonEmpty(x)),
      generatedNegative("fixpoint_range_tail_first_as_tail_closure", fixpointRangeTail(x, 0, 1), TailsClosure(x)),
      generatedNegative("fixpoint_prefixed_reconstruct_nonempty_prefix_identity", fixpointPrefixedReconstruct(x, Vector(a)), x),
      generatedNegative("fixpoint_prefixed_range_reconstruct_nonempty_prefix_identity", fixpointPrefixedRangeReconstruct(x, Vector(a), 0, 1), x),
      generatedNegative("range_first_is_full", Range(x, 0, 1), x),
      generatedNegative("range_last_is_full", Range(x, -1, 0), x),
      generatedNegative("range_drop_last_is_full", Range(x, 0, -1), x),
      generatedNegative("range_first_distributes_over_union", Range(Union(x, y), 0, 1), Union(Range(x, 0, 1), Range(y, 0, 1))),
      generatedNegative("range_last_distributes_over_union", Range(Union(x, y), -1, 0), Union(Range(x, -1, 0), Range(y, -1, 0))),
      generatedNegative("range_wrap_first_uses_last", Range(Wrap(Vector(a), rangeNoEpsilonFixture), 0, 1), Wrap(Vector(a), Range(rangeNoEpsilonFixture, -1, 0))),
      generatedNegative("range_wrap_last_uses_first", Range(Wrap(Vector(a), rangeNoEpsilonFixture), -1, 0), Wrap(Vector(a), Range(rangeNoEpsilonFixture, 0, 1))),
      generatedNegative("range_wrap_drop_last_keeps_last", Range(Wrap(Vector(a), rangeNoEpsilonFixture), 0, -1), Wrap(Vector(a), rangeNoEpsilonFixture)),
    )
    Vector(
      Law("union_idempotent", Union(x, x), x),
      Law("union_empty_right", Union(x, Empty), x),
      Law("union_commutative", Union(x, y), Union(y, x)),
      Law("union_associative", Union(Union(x, y), z), Union(x, Union(y, z))),
      Law("intersection_idempotent", Intersection(x, x), x),
      Law("intersection_empty_left", Intersection(Empty, x), Empty),
      Law("intersection_commutative", Intersection(x, y), Intersection(y, x)),
      Law("intersection_associative", Intersection(Intersection(x, y), z), Intersection(x, Intersection(y, z))),
      Law("union_absorbs_intersection_subset", Union(x, Intersection(x, y)), x),
      Law("intersection_absorbs_union_superset", Intersection(x, Union(x, y)), x),
      Law("union_absorbs_diff_subset", Union(x, Diff(x, y)), x),
      Law("union_difference_rejoins_removed", Union(Diff(x, y), y), Union(x, y)),
      Law("union_difference_intersection_partition", Union(Diff(x, y), Intersection(x, y)), x),
      Law("intersection_absorbs_diff_subset", Intersection(x, Diff(x, y)), Diff(x, y)),
      Law("diff_empty_right", Diff(x, Empty), x),
      Law("diff_empty_left", Diff(Empty, x), Empty),
      Law("diff_self_empty", Diff(x, x), Empty),
      Law("diff_union_rhs", Diff(x, Union(y, z)), Diff(Diff(x, y), z)),
      Law("diff_intersection_left_subset_empty", Diff(Intersection(x, y), x), Empty),
      Law("diff_intersection_right_subset_empty", Diff(Intersection(x, y), y), Empty),
      Law("diff_union_left_cancel", Diff(Union(x, y), x), Diff(y, x)),
      Law("diff_union_right_cancel", Diff(Union(x, y), y), Diff(x, y)),
      Law("diff_union_minus_difference_left", Diff(Union(x, y), Diff(x, y)), y),
      Law("diff_union_minus_difference_right", Diff(Union(x, y), Diff(y, x)), x),
      Law("diff_nested_same_rhs", Diff(Diff(x, y), y), Diff(x, y)),
      Law("diff_intersection_complement_left", Diff(x, Intersection(x, y)), Diff(x, y)),
      Law("diff_intersection_complement_right", Diff(x, Intersection(y, x)), Diff(x, y)),
      Law("diff_difference_self_left", Diff(x, Diff(x, y)), Intersection(x, y)),
      Law("diff_difference_other_right", Diff(x, Diff(y, x)), x),
      Law("restriction_epsilon_identity", Restriction(x, Eps), x),
      Law("restriction_empty_prefixes", Restriction(x, Empty), Empty),
      Law("union_absorbs_restriction_subset", Union(x, Restriction(x, p)), x),
      Law("intersection_absorbs_restriction_subset", Intersection(x, Restriction(x, p)), Restriction(x, p)),
      Law("union_absorbs_raffination_subset", Union(x, Raffination(x, p)), x),
      Law("intersection_absorbs_raffination_subset", Intersection(x, Raffination(x, p)), Raffination(x, p)),
      Law("restriction_union_same_source", Union(Restriction(x, p), Restriction(x, q)), Restriction(x, Union(p, q))),
      Law("raffination_intersection_same_source", Intersection(Raffination(x, p), Raffination(x, q)), Raffination(x, Union(p, q))),
      Law("restriction_raffination_partition", Union(Restriction(x, p), Raffination(x, p)), x),
      Law("restriction_raffination_disjoint", Intersection(Restriction(x, p), Raffination(x, p)), Empty),
      Law("diff_restriction_subset_empty", Diff(Restriction(x, p), x), Empty),
      Law("diff_raffination_subset_empty", Diff(Raffination(x, p), x), Empty),
      Law("diff_restriction_complement", Diff(x, Restriction(x, p)), Raffination(x, p)),
      Law("diff_raffination_complement", Diff(x, Raffination(x, p)), Restriction(x, p)),
      Law("wrap_unwrap_left_inverse_a", Unwrap(Wrap(Vector(a), x), Vector(a)), x, assumptions = Vector(WithinLength(x, 2))),
      Law("wrap_unwrap_left_inverse_b", Unwrap(Wrap(Vector(b), x), Vector(b)), x, assumptions = Vector(WithinLength(x, 2))),
      Law("wrap_unwrap_left_inverse_ab", Unwrap(Wrap(Vector(a, b), x), Vector(a, b)), x, assumptions = Vector(WithinLength(x, 1))),
      Law("wrap_unwrap_restriction_a", Wrap(Vector(a), Unwrap(x, Vector(a))), Restriction(x, sa)),
      Law("wrap_unwrap_restriction_b", Wrap(Vector(b), Unwrap(x, Vector(b))), Restriction(x, sb)),
      Law("unwrap_union", Unwrap(Union(x, y), Vector(a)), Union(Unwrap(x, Vector(a)), Unwrap(y, Vector(a)))),
      Law("product_empty_left", Product(Empty, x), Empty),
      Law("product_empty_right", Product(x, Empty), Empty),
      Law("product_epsilon_left", Product(Eps, x), x),
      Law("product_epsilon_right", Product(x, Eps), x),
      Law("child_union_a", Child(a, Union(x, y)), Union(Child(a, x), Child(a, y))),
      Law("child_union_b", Child(b, Union(x, y)), Union(Child(b, x), Child(b, y))),
      Law("child_same_head_union_a", Child(a, sameHeadRangeFixture), Union(singleton(a), singleton(b))),
      Law("child_same_head_union_b", Child(b, sameHeadRangeFixtureB), Union(singleton(a), singleton(b))),
      Law("child_intersection_a", Child(a, Intersection(x, y)), Intersection(Child(a, x), Child(a, y))),
      Law("child_intersection_b", Child(b, Intersection(x, y)), Intersection(Child(b, x), Child(b, y))),
      Law("child_diff_a", Child(a, Diff(x, y)), Diff(Child(a, x), Child(a, y))),
      Law("child_diff_b", Child(b, Diff(x, y)), Diff(Child(b, x), Child(b, y))),
      Law("child_empty_a", Child(a, Empty), Empty),
      Law("child_empty_b", Child(b, Empty), Empty),
      Law("child_epsilon_a", Child(a, Eps), Empty),
      Law("child_epsilon_b", Child(b, Eps), Empty),
      Law("child_singleton_hit_a", Child(a, singleton(a)), Eps),
      Law("child_singleton_hit_b", Child(b, singleton(b)), Eps),
      Law("child_singleton_miss_a_b", Child(a, singleton(b)), Empty),
      Law("child_singleton_miss_b_a", Child(b, singleton(a)), Empty),
      Law("child_concat_hit_a", Child(a, singleton(a, b)), singleton(b)),
      Law("child_concat_hit_b", Child(b, singleton(b, a)), singleton(a)),
      Law("child_concat_miss_a_b", Child(a, singleton(b, a)), Empty),
      Law("child_concat_miss_b_a", Child(b, singleton(a, b)), Empty),
      Law(
        "child_product_a",
        Child(a, Product(x, y)),
        Union(Product(Child(a, x), y), IfNullable(x, Child(a, y))),
        note = "Guarded by ProductClosed(X,Y): every X/Y path pair whose concatenation would escape the bounded universe is forbidden, so RHS derivative products cannot fabricate tails for out-of-universe source concatenations.",
        assumptions = Vector(ProductClosed(x, y)),
      ),
      Law(
        "child_product_b",
        Child(b, Product(x, y)),
        Union(Product(Child(b, x), y), IfNullable(x, Child(b, y))),
        note = "Symmetric representative of the ProductClosed(X,Y)-guarded product derivative for the other alphabet symbol.",
        assumptions = Vector(ProductClosed(x, y)),
      ),
      Law(
        "child_restriction_a",
        Child(a, Restriction(x, p)),
        Union(IfNullable(p, Child(a, x)), Restriction(Child(a, x), Child(a, p))),
      ),
      Law(
        "child_restriction_b",
        Child(b, Restriction(x, p)),
        Union(IfNullable(p, Child(b, x)), Restriction(Child(b, x), Child(b, p))),
      ),
      Law("tails_union_children", TailsUnion(x), Union(Child(a, x), Child(b, x))),
      Law("frontier_union_is_tails_union", FrontierState(FrontierUnion(x)), TailsUnion(x)),
      Law("frontier_tail_union_a_is_child", FrontierState(FrontierTailUnion(x, a)), Child(a, x)),
      Law("frontier_tail_union_b_is_child", FrontierState(FrontierTailUnion(x, b)), Child(b, x)),
      Law("frontier_child_union_a_after_b", FrontierState(FrontierChildUnion(FrontierTailUnion(x, b), a)), Child(a, Child(b, x))),
      Law("child_tails_union_a", Child(a, TailsUnion(x)), Union(Child(a, Child(a, x)), Child(a, Child(b, x)))),
      Law("child_tails_union_b", Child(b, TailsUnion(x)), Union(Child(b, Child(a, x)), Child(b, Child(b, x)))),
      Law(
        "tails_intersection_two_known_heads",
        TailsIntersection(Union(Wrap(Vector(a), Union(Eps, x)), Wrap(Vector(b), Union(Eps, y)))),
        Intersection(Union(Eps, x), Union(Eps, y)),
        assumptions = Vector(WithinLength(x, 2), WithinLength(y, 2)),
      ),
      Law("head_idempotent", Head(Head(x)), Head(x)),
      Law(
        "head_product",
        Head(Product(x, y)),
        Union(Head(x), IfNullable(x, Head(y))),
        assumptions = Vector(WithinLength(x, 2), WithinLength(y, 1), NonEmptyAssumption(y)),
      ),
      Law("nonempty_empty", NonEmpty(Empty), Empty),
      Law("nonempty_epsilon_empty", NonEmpty(Eps), Empty),
      Law("nonempty_idempotent", NonEmpty(NonEmpty(x)), NonEmpty(x)),
      Law("nonempty_subset", Diff(NonEmpty(x), x), Empty),
      Law("nonempty_union", NonEmpty(Union(x, y)), Union(NonEmpty(x), NonEmpty(y))),
      Law("nonempty_child_a", Child(a, NonEmpty(x)), Child(a, x)),
      Law("nonempty_child_b", Child(b, NonEmpty(x)), Child(b, x)),
      Law("head_nonempty", Head(NonEmpty(x)), Head(x)),
      Law("patch_child_hit_a", Child(a, PatchChild(x, a, y)), y, assumptions = Vector(WithinLength(y, 2))),
      Law("patch_child_hit_b", Child(b, PatchChild(x, b, y)), y, assumptions = Vector(WithinLength(y, 2))),
      Law("patch_child_miss_b", Child(b, PatchChild(x, a, y)), Child(b, x)),
      Law("patch_child_miss_a", Child(a, PatchChild(x, b, y)), Child(a, x)),
      Law("patch_child_identity_a", PatchChild(x, a, Child(a, x)), x),
      Law("patch_child_identity_b", PatchChild(x, b, Child(b, x)), x),
      Law("patch_child_terminal_preserved", Intersection(PatchChild(x, a, y), Eps), Intersection(x, Eps)),
      Law(
        "patch_child_materialization_a",
        PatchChild(x, a, y),
        Union(Diff(x, Restriction(x, sa)), Wrap(Vector(a), y)),
        assumptions = Vector(WithinLength(y, 2)),
      ),
      Law("iteration_tail_identity", iterTail(x), TailsUnion(x)),
      Law("iteration_head_identity", iterHead(x), Head(x)),
      Law("iteration_reconstruct_nonempty_source", iterReconstruct(x), NonEmpty(x)),
      Law("iteration_prefixed_reconstruct_nonempty_source", iterPrefixedReconstruct(x, Vector(a)), Wrap(Vector(a), NonEmpty(x))),
      Law("iteration_prefixed_reconstruct_two_item_nonempty_source", iterPrefixedReconstruct(x, Vector(a, b)), Wrap(Vector(a, b), NonEmpty(x))),
      Law("iteration_range_tail_full_sentinel", iterRangeTail(x, 0, 0), TailsUnion(x)),
      Law("iteration_range_reconstruct_full_sentinel", iterRangeReconstruct(x, 0, 0), NonEmpty(x)),
      Law("iteration_prefixed_range_reconstruct_full_sentinel", iterPrefixedRangeReconstruct(x, Vector(a), 0, 0), Wrap(Vector(a), NonEmpty(x))),
      Law("iteration_range_tail_empty_slice", iterRangeTail(x, 1, 1), Empty),
      Law("iteration_range_reconstruct_empty_slice", iterRangeReconstruct(x, 1, 1), Empty),
      Law("iteration_prefixed_range_reconstruct_empty_slice", iterPrefixedRangeReconstruct(x, Vector(a), 1, 1), Empty),
      Law("iteration_range_tail_first_subset", Diff(iterRangeTail(x, 0, 1), TailsUnion(x)), Empty),
      Law("iteration_range_reconstruct_first_subset", Diff(iterRangeReconstruct(x, 0, 1), NonEmpty(x)), Empty),
      Law("iteration_prefixed_range_reconstruct_first_subset", Diff(iterPrefixedRangeReconstruct(x, Vector(a), 0, 1), Wrap(Vector(a), NonEmpty(x))), Empty),
      Law("iteration_range_tail_drop_last_subset", Diff(iterRangeTail(x, 0, -1), TailsUnion(x)), Empty),
      Law("iteration_range_reconstruct_drop_last_subset", Diff(iterRangeReconstruct(x, 0, -1), NonEmpty(x)), Empty),
      Law("iteration_prefixed_range_reconstruct_drop_last_subset", Diff(iterPrefixedRangeReconstruct(x, Vector(a), 0, -1), Wrap(Vector(a), NonEmpty(x))), Empty),
      Law("iteration_empty_source", iterConst(Empty, y, "Y"), Empty),
      Law("iteration_independent_body_head_guard", iterConstY, IfEmpty(Head(x), Empty, y)),
      Law("iteration_source_union_tail", iterTail(Union(x, y)), Union(iterTail(x), iterTail(y))),
      Law("iteration_source_union_head", iterHead(Union(x, y)), Union(iterHead(x), iterHead(y))),
      Law(
        "iteration_body_union_distribution",
        Iter(x, (head, tail) => Union(Product(head, tail), head), label = "body-union"),
        Union(iterReconstruct(x), iterHead(x)),
      ),
      Law(
        "iteration_source_union_reconstruct",
        iterReconstruct(Union(x, y)),
        Union(iterReconstruct(x), iterReconstruct(y)),
      ),
      Law(
        "iteration_general_wrap_hoist",
        Iter(x, (head, tail) => Wrap(Vector(a), Product(head, tail)), label = "wrap-hoist"),
        Wrap(Vector(a), iterReconstruct(x)),
      ),
      Law(
        "iteration_general_product_right_hoist",
        Iter(x, (_head, tail) => Product(tail, y), bodyVars = y.vars, label = "product-right-hoist"),
        Product(iterTail(x), y),
      ),
      Law(
        "iteration_general_intersection_right_hoist",
        Iter(x, (_head, tail) => Intersection(tail, y), bodyVars = y.vars, label = "intersection-right-hoist"),
        Intersection(iterTail(x), y),
      ),
      Law(
        "iteration_general_diff_right_hoist",
        Iter(x, (_head, tail) => Diff(tail, y), bodyVars = y.vars, label = "diff-right-hoist"),
        Diff(iterTail(x), y),
      ),
      Law(
        "iteration_general_restriction_right_hoist",
        Iter(x, (_head, tail) => Restriction(tail, y), bodyVars = y.vars, label = "restriction-right-hoist"),
        Restriction(iterTail(x), y),
      ),
      Law("example_puzzle_one_move_a_to_b", iterTail(Restriction(puzzleEdges, sa)), sb),
      Law("example_puzzle_one_move_b_to_a", iterTail(Restriction(puzzleEdges, sb)), sa),
      Law("iteration_range_tail_first_literal", iterRangeTail(rangeBorderFixture, 0, 1), singleton(a)),
      Law("iteration_range_reconstruct_first_literal", iterRangeReconstruct(rangeBorderFixture, 0, 1), Const(Vector(Vector(a, a), Vector(b, a)))),
      Law("iteration_prefixed_range_reconstruct_first_literal", iterPrefixedRangeReconstruct(rangeBorderFixture, Vector(a), 0, 1), Const(Vector(Vector(a, a, a), Vector(a, b, a)))),
      Law("iteration_range_tail_drop_last_literal", iterRangeTail(rangeBorderFixture, 0, -1), singleton(a)),
      Law("iteration_range_reconstruct_drop_last_literal", iterRangeReconstruct(rangeBorderFixture, 0, -1), singleton(a, a)),
      Law("iteration_prefixed_range_reconstruct_drop_last_literal", iterPrefixedRangeReconstruct(rangeBorderFixture, Vector(a), 0, -1), singleton(a, a, a)),
      Law("iteration_range_tail_same_head_first_literal", iterRangeTail(sameHeadRangeFixture, 0, 1), singleton(a)),
      Law("iteration_range_tail_same_head_drop_last_literal", iterRangeTail(sameHeadRangeFixture, 0, -1), singleton(a)),
      Law("iteration_range_reconstruct_same_head_first_literal", iterRangeReconstruct(sameHeadRangeFixture, 0, 1), singleton(a, a)),
      Law("iteration_range_reconstruct_same_head_drop_last_literal", iterRangeReconstruct(sameHeadRangeFixture, 0, -1), singleton(a, a)),
      Law("iteration_prefixed_range_reconstruct_same_head_drop_last_literal", iterPrefixedRangeReconstruct(sameHeadRangeFixture, Vector(a), 0, -1), singleton(a, a, a)),
      Law(
        "example_nqueens_attack_projection_2x2",
        Iter(nqueensUpto2, (i, _tail) => Union(Product(sa, i), Product(i, sb)), label = "nqueens-attack"),
        Const(Vector(Vector(a, a), Vector(a, b), Vector(b, b))),
      ),
      Law(
        "example_nqueens_available_choice_2x2",
        Iter(
          Diff(nqueensUpto2, nqueensTaken),
          (q, _tail) => Product(q, Union(Product(sa, q), nqueensTaken)),
          label = "nqueens-choice",
        ),
        Const(Vector(Vector(b, a), Vector(b, a, b))),
      ),
      Law("prefix_closure_idempotent", PrefixClosure(PrefixClosure(x)), PrefixClosure(x)),
      Law("suffix_closure_idempotent", SuffixClosure(SuffixClosure(x)), SuffixClosure(x)),
      Law("tails_closure_idempotent", TailsClosure(TailsClosure(x)), TailsClosure(x)),
      Law(
        "suffix_closure_child_derivative_a",
        Child(a, SuffixClosure(x)),
        Child(a, Union(NonEmpty(x), TailsUnion(SuffixClosure(x)))),
      ),
      Law(
        "suffix_closure_child_derivative_b",
        Child(b, SuffixClosure(x)),
        Child(b, Union(NonEmpty(x), TailsUnion(SuffixClosure(x)))),
      ),
      Law("tails_closure_definition", TailsClosure(x), IfEmpty(x, Empty, Union(Eps, SuffixClosure(x)))),
      Law("child_tails_closure_derivative_a", Child(a, TailsClosure(x)), Child(a, SuffixClosure(x))),
      Law("child_tails_closure_derivative_b", Child(b, TailsClosure(x)), Child(b, SuffixClosure(x))),
      Law("antimirov_suffix_frontier_state_child_a", FrontierState(FrontierTailUnion(SuffixClosure(x), a)), Child(a, SuffixClosure(x))),
      Law("antimirov_suffix_frontier_state_child_b", FrontierState(FrontierTailUnion(SuffixClosure(x), b)), Child(b, SuffixClosure(x))),
      Law("antimirov_tails_frontier_state_child_a", FrontierState(FrontierTailUnion(TailsClosure(x), a)), Child(a, TailsClosure(x))),
      Law("antimirov_tails_frontier_state_child_b", FrontierState(FrontierTailUnion(TailsClosure(x), b)), Child(b, TailsClosure(x))),
      Law("antimirov_suffix_frontier_nested_a_b", Child(b, FrontierState(FrontierTailUnion(SuffixClosure(x), a))), Child(b, Child(a, SuffixClosure(x)))),
      Law("antimirov_tails_frontier_nested_a_b", Child(b, FrontierState(FrontierTailUnion(TailsClosure(x), a))), Child(b, Child(a, TailsClosure(x)))),
      Law("tails_closure_unfold_base_or_step", TailsClosure(x), Union(x, TailsUnion(TailsClosure(x)))),
      Law("fixpoint_tail_closure", fixpointTail(x), TailsClosure(x)),
      Law("fixpoint_tail_unfold_base_or_step", fixpointTail(x), Union(x, TailsUnion(fixpointTail(x)))),
      Law("fixpoint_tail_unfold_via_iter_tail", fixpointTail(x), Union(x, iterTail(fixpointTail(x)))),
      Law("fixpoint_head_closure", fixpointHead(x), Union(x, Head(x))),
      Law("fixpoint_head_unfold_base_or_step", fixpointHead(x), Union(x, iterHead(fixpointHead(x)))),
      Law("fixpoint_reconstruct_identity", fixpointReconstruct(x), x),
      Law("fixpoint_reconstruct_unfold_base_or_step", fixpointReconstruct(x), Union(x, iterReconstruct(fixpointReconstruct(x)))),
      Law("fixpoint_prefixed_reconstruct_empty_prefix_identity", fixpointPrefixedReconstruct(x, Vector.empty), x),
      Law("fixpoint_range_tail_full_sentinel_closure", fixpointRangeTail(x, 0, 0), TailsClosure(x)),
      Law("fixpoint_range_tail_empty_slice_identity", fixpointRangeTail(x, 1, 1), x),
      Law("fixpoint_range_reconstruct_full_sentinel_identity", fixpointRangeReconstruct(x, 0, 0), x),
      Law("fixpoint_range_reconstruct_first_identity", fixpointRangeReconstruct(x, 0, 1), x),
      Law("fixpoint_range_reconstruct_drop_last_identity", fixpointRangeReconstruct(x, 0, -1), x),
      Law("fixpoint_prefixed_range_reconstruct_empty_prefix_first_identity", fixpointPrefixedRangeReconstruct(x, Vector.empty, 0, 1), x),
      Law("fixpoint_prefixed_range_reconstruct_empty_prefix_drop_last_identity", fixpointPrefixedRangeReconstruct(x, Vector.empty, 0, -1), x),
      Law("range_full_0_0", Range(x, 0, 0), x),
      Law("range_empty_1_1", Range(x, 1, 1), Empty),
      Law("range_empty_source_first", Range(Empty, 0, 1), Empty),
      Law("range_empty_source_last", Range(Empty, -1, 0), Empty),
      Law("range_empty_source_drop_last", Range(Empty, 0, -1), Empty),
      Law("range_first_wrap_a", Range(Wrap(Vector(a), x), 0, 1), Wrap(Vector(a), Range(x, 0, 1)), assumptions = Vector(WithinLength(x, 2))),
      Law("range_last_wrap_a", Range(Wrap(Vector(a), x), -1, 0), Wrap(Vector(a), Range(x, -1, 0)), assumptions = Vector(WithinLength(x, 2))),
      Law("range_drop_last_wrap_a", Range(Wrap(Vector(a), x), 0, -1), Wrap(Vector(a), Range(x, 0, -1)), assumptions = Vector(WithinLength(x, 2))),
      Law("range_first_wrap_b", Range(Wrap(Vector(b), x), 0, 1), Wrap(Vector(b), Range(x, 0, 1)), assumptions = Vector(WithinLength(x, 2))),
      Law("range_last_wrap_b", Range(Wrap(Vector(b), x), -1, 0), Wrap(Vector(b), Range(x, -1, 0)), assumptions = Vector(WithinLength(x, 2))),
      Law("range_drop_last_wrap_b", Range(Wrap(Vector(b), x), 0, -1), Wrap(Vector(b), Range(x, 0, -1)), assumptions = Vector(WithinLength(x, 2))),
      Law("range_first_wrap_ab", Range(Wrap(Vector(a, b), x), 0, 1), Wrap(Vector(a, b), Range(x, 0, 1)), assumptions = Vector(WithinLength(x, 1))),
      Law("range_last_wrap_ab", Range(Wrap(Vector(a, b), x), -1, 0), Wrap(Vector(a, b), Range(x, -1, 0)), assumptions = Vector(WithinLength(x, 1))),
      Law("range_drop_last_wrap_ab", Range(Wrap(Vector(a, b), x), 0, -1), Wrap(Vector(a, b), Range(x, 0, -1)), assumptions = Vector(WithinLength(x, 1))),
      Law("range_first_subset", Diff(Range(x, 0, 1), x), Empty),
      Law("range_union_absorb", Union(x, Range(x, 0, 1)), x),
      Law("range_intersection_absorb", Intersection(x, Range(x, 0, 1)), Range(x, 0, 1)),
      Law("range_first_idempotent", Range(Range(x, 0, 1), 0, 1), Range(x, 0, 1)),
      Law("range_last_idempotent", Range(Range(x, -1, 0), -1, 0), Range(x, -1, 0)),
      Law("range_first_of_last", Range(Range(x, -1, 0), 0, 1), Range(x, -1, 0)),
      Law("range_drop_last_of_first_empty", Range(Range(x, 0, 1), 0, -1), Empty),
      Law("range_nested_first", Range(Range(x, 0, 2), 0, 1), Range(x, 0, 1)),
      Law("range_nested_suffix_first", Range(Range(x, 2, 0), 0, 2), Range(x, 2, 4)),
      Law("range_nested_suffix_offset", Range(Range(x, 2, 0), 2, 0), Range(x, 3, 0)),
      Law("range_nested_last_last", Range(Range(x, -5, 0), -2, 0), Range(x, -2, 0)),
      Law("range_positive_same_empty", Range(x, 2, 2), Empty),
      Law("range_positive_decreasing_empty", Range(x, 3, 2), Empty),
      Law("range_negative_same_empty", Range(x, -2, -2), Empty),
      Law("range_negative_decreasing_empty", Range(x, -2, -3), Empty),
      Law("range_last_subset", Diff(Range(x, -1, 0), x), Empty),
      Law("range_drop_last_subset", Diff(Range(x, 0, -1), x), Empty),
      Law("range_negative_window_subset", Diff(Range(x, -3, -1), x), Empty),
      Law("range_singleton_last_literal", Range(singleton(a, b), -1, 0), singleton(a, b)),
      Law("range_singleton_drop_last_literal", Range(singleton(a, b), 0, -1), Empty),
      Law("range_singleton_negative_window_literal", Range(singleton(a, b), -2, -1), Empty),
      Law("range_nested_singleton_last_literal", Range(Range(singleton(a, b), -2, 0), -1, 0), singleton(a, b)),
      Law("range_item_union_first_literal", Range(rangeItemFixture, 0, 1), sa),
      Law("range_item_union_last_literal", Range(rangeItemFixture, -1, 0), sb),
      Law("range_item_union_drop_last_literal", Range(rangeItemFixture, 0, -1), sa),
      Law("range_drop_last_full_sentinel_literal", Range(Range(rangeBorderFixture, 0, -1), 0, 0), Range(rangeBorderFixture, 0, -1)),
      Law("range_first_epsilon_literal", Range(rangeBorderFixture, 0, 1), Eps),
      Law("range_first_child_border_literal", Child(a, Range(rangeBorderFixture, 0, 2)), singleton(a)),
      Law("range_first_child_full_literal", Child(a, Range(rangeBorderFixture, 0, 3)), Const(Vector(Vector(a), Vector(b)))),
      Law("range_prunes_after_upper_border_literal", Child(b, Range(rangeBorderFixture, 0, 3)), Empty),
      Law("range_suffix_child_border_literal", Child(b, Range(rangeBorderFixture, 4, 0)), singleton(a)),
      Law("range_last_border_literal", Range(rangeBorderFixture, -1, 0), singleton(b, a)),
      Law("range_last_child_border_literal", Child(b, Range(rangeBorderFixture, -1, 0)), singleton(a)),
      Law("range_last_prunes_earlier_head_literal", Child(a, Range(rangeBorderFixture, -1, 0)), Empty),
      Law("range_drop_last_border_literal", Range(rangeBorderFixture, 0, -1), Const(Vector(Vector.empty[String], Vector(a, a), Vector(a, b)))),
      Law("range_drop_last_child_border_literal", Child(a, Range(rangeBorderFixture, 0, -1)), Const(Vector(Vector(a), Vector(b)))),
      Law("range_drop_last_prunes_last_head_literal", Child(b, Range(rangeBorderFixture, 0, -1)), Empty),
      Law("range_negative_window_border_literal", Range(rangeBorderFixture, -2, -1), singleton(a, b)),
      Law("range_negative_window_child_border_literal", Child(a, Range(rangeBorderFixture, -2, -1)), singleton(b)),
      Law("range_negative_window_prunes_last_head_literal", Child(b, Range(rangeBorderFixture, -2, -1)), Empty),
      Law("range_first_without_epsilon_literal", Range(rangeNoEpsilonFixture, 0, 1), Const(Vector(Vector(a, b)))),
      Law("range_first_without_epsilon_child_literal", Child(a, Range(rangeNoEpsilonFixture, 0, 1)), singleton(b)),
      Law("range_first_without_epsilon_prunes_later_child_literal", Child(b, Range(rangeNoEpsilonFixture, 0, 1)), Empty),
      Law("bad_nonempty_identity_negative_control", NonEmpty(x), x, expected = "sat"),
      Law("bad_patch_child_identity_negative_control", PatchChild(x, a, y), x, expected = "sat"),
      Law("bad_diff_commutative_negative_control", Diff(x, y), Diff(y, x), expected = "sat"),
      Law(
        "bad_child_restriction_without_nullable_negative_control",
        Child(a, Restriction(x, p)),
        Restriction(Child(a, x), Child(a, p)),
        expected = "sat",
      ),
      Law(
        "bad_child_product_without_length_guard_negative_control",
        Child(a, Product(x, y)),
        Union(Product(Child(a, x), y), IfNullable(x, Child(a, y))),
        expected = "sat",
        note = "Product derivative without the no-concatenation-escapes-universe guard is false in the bounded model because the RHS can create tails that did not come from an in-universe concatenated source path.",
      ),
      Law("bad_wrap_unwrap_wrong_prefix_negative_control", Unwrap(Wrap(Vector(a), x), Vector(b)), x, expected = "sat"),
      Law("bad_tails_union_as_head_negative_control", TailsUnion(x), Head(x), expected = "sat"),
      Law("bad_suffix_closure_as_prefix_closure_negative_control", SuffixClosure(x), PrefixClosure(x), expected = "sat"),
      Law("bad_iteration_independent_without_head_negative_control", iterConstY, y, expected = "sat"),
      Law("bad_range_first_is_full_negative_control", Range(x, 0, 1), x, expected = "sat"),
      Law("bad_range_first_child_is_full_negative_control", Child(a, Range(rangeBorderFixture, 0, 2)), Child(a, rangeBorderFixture), expected = "sat"),
      Law("bad_range_last_is_first_border_negative_control", Range(rangeBorderFixture, -1, 0), Range(rangeBorderFixture, 0, 1), expected = "sat"),
      Law("bad_range_drop_last_keeps_last_head_negative_control", Child(b, Range(rangeBorderFixture, 0, -1)), Child(b, rangeBorderFixture), expected = "sat"),
      Law("bad_range_negative_window_keeps_last_head_negative_control", Child(b, Range(rangeBorderFixture, -2, -1)), Child(b, rangeBorderFixture), expected = "sat"),
    ) ++ generatedNegativeControls

  private def block(lines: String*): String = lines.filter(_.nonEmpty).mkString("\n")

  val trieSetMemberTptp: String = block(
    "% Path-set membership and eager trie membership.",
    "fof(path_cons_not_nil, axiom, ! [I,P] : ~(cons(I,P) = nil)).",
    "fof(path_cons_injective, axiom, ! [I,J,P,Q] : (cons(I,P) = cons(J,Q) <=> (I = J & P = Q))).",
    "fof(path_append_nil_left, axiom, ! [P] : p_append(nil,P,P)).",
    "fof(path_append_nil_right, axiom, ! [P] : p_append(P,nil,P)).",
    "fof(path_append_to_nil, axiom, ! [P,Q] : (p_append(P,Q,nil) <=> (P = nil & Q = nil))).",
    "fof(path_append_right_nil_unique, axiom, ! [P,Q] : (p_append(P,nil,Q) <=> Q = P)).",
    "fof(path_append_singleton_left_unique, axiom, ! [I,P,Q] : (p_append(cons(I,nil),P,Q) <=> Q = cons(I,P))).",
    "fof(path_append_cons, axiom, ! [I,P,Q,R] : (p_append(cons(I,P),Q,cons(I,R)) <=> p_append(P,Q,R))).",
    "fof(path_append_head_decompose, axiom, ! [I,P,Q,R] : (p_append(Q,R,cons(I,P)) <=> ((Q = nil & R = cons(I,P)) | ? [Tail] : (Q = cons(I,Tail) & p_append(Tail,R,P))))).",
    "fof(path_prefix_def, axiom, ! [Prefix,P] : (p_prefix(Prefix,P) <=> ? [Tail] : p_append(Prefix,Tail,P))).",
    "fof(path_prefix_cons_left, axiom, ! [I,P,Q] : (p_prefix(cons(I,P),Q) <=> ? [Tail] : (Q = cons(I,Tail) & p_prefix(P,Tail)))).",
    "fof(path_suffix_step_decompose, axiom, ! [I,P,Full] : ((? [Prefix] : p_append(Prefix,cons(I,P),Full)) <=> (Full = cons(I,P) | ? [H,Prefix] : p_append(Prefix,cons(H,cons(I,P)),Full)))).",
    "fof(trie_member_nil, axiom, ! [T] : (tmem(nil,T) <=> tterminal(T))).",
    "fof(trie_member_cons, axiom, ! [T,I,P] : (tmem(cons(I,P),T) <=> tmem(P,tchild(T,I)))).",
    "fof(trie_terminal_set, axiom, ! [T] : (tterminal(T) <=> p_mem(nil,tset(T)))).",
    "fof(trie_child_set, axiom, ! [T,I,P] : (p_mem(P,tset(tchild(T,I))) <=> p_mem(cons(I,P),tset(T)))).",
  )

  val pathNormalizerTptp: String = block(
    trieSetMemberTptp,
    "",
    "% Path expression monoid identities used by egg path normalizers.",
    "% They are stated over p_append, the semantic relation behind Path.Concat.",
  )

  val trieSetTptp: String = block(
    trieSetMemberTptp,
    "",
    "% Set operations.",
    "fof(set_union, axiom, ! [P,A,B] : (p_mem(P,sunion(A,B)) <=> (p_mem(P,A) | p_mem(P,B)))).",
    "fof(set_intersection, axiom, ! [P,A,B] : (p_mem(P,sinter(A,B)) <=> (p_mem(P,A) & p_mem(P,B)))).",
    "fof(set_diff, axiom, ! [P,A,B] : (p_mem(P,sdiff(A,B)) <=> (p_mem(P,A) & ~p_mem(P,B)))).",
    "fof(set_nonempty_paths, axiom, ! [P,S] : (p_mem(P,snonempty_paths(S)) <=> (p_mem(P,S) & ~(P = nil)))).",
    "fof(set_product, axiom, ! [P,A,B] : (p_mem(P,sproduct(A,B)) <=> ? [Q,R] : (p_mem(Q,A) & p_mem(R,B) & p_append(Q,R,P)))).",
    "fof(set_restriction, axiom, ! [P,A,B] : (p_mem(P,srestriction(A,B)) <=> (p_mem(P,A) & ? [Q] : (p_mem(Q,B) & p_prefix(Q,P))))).",
    "fof(set_raffination, axiom, ! [P,A,B] : (p_mem(P,sraffination(A,B)) <=> (p_mem(P,A) & ~ ? [Q] : (p_mem(Q,B) & p_prefix(Q,P))))).",
    "fof(set_wrap, axiom, ! [P,A,Prefix] : (p_mem(P,swrap(A,Prefix)) <=> ? [Tail] : (p_mem(Tail,A) & p_append(Prefix,Tail,P)))).",
    "fof(set_unwrap, axiom, ! [P,A,Prefix] : (p_mem(P,sunwrap(A,Prefix)) <=> ? [Full] : (p_append(Prefix,P,Full) & p_mem(Full,A)))).",
    "",
    "% Ordered Range over path sets.  The full ordering/rank definition is kept",
    "% abstract; these axioms expose the public membership contract and sentinel",
    "% cases used by the eager trie, zipper, and graph proof layers.",
    "fof(set_range, axiom, ! [P,S,Start,End] : (p_mem(P,srange(S,Start,End)) <=> (p_mem(P,S) & range_select(P,S,Start,End)))).",
    "fof(range_select_full_sentinel, axiom, ! [P,S] : range_select(P,S,n0,n0)).",
    "fof(range_select_empty_one_one, axiom, ! [P,S] : ~range_select(P,S,n1,n1)).",
    "fof(range_select_first_epsilon, axiom, ! [S] : (p_mem(nil,S) => range_select(nil,S,n0,n1))).",
    "",
    "% Headed grouping and MORKL iteration over first path items.",
    "fof(set_child, axiom, ! [P,S,I] : (p_mem(P,schild(S,I)) <=> p_mem(cons(I,P),S))).",
    "fof(set_nonempty, axiom, ! [S] : (snonempty(S) <=> ? [P] : p_mem(P,S))).",
    "fof(set_tails_union, axiom, ! [P,S] : (p_mem(P,stails_union(S)) <=> ? [I] : p_mem(cons(I,P),S))).",
    "fof(set_tails_intersection, axiom, ! [P,S] : (p_mem(P,stails_intersection(S)) <=> (? [I] : snonempty(schild(S,I))) & ! [I] : (snonempty(schild(S,I)) => p_mem(P,schild(S,I))))).",
    "fof(closed_frontier_def, axiom, ! [S,Keys] : (closed_frontier(S,Keys) <=> ! [I] : (frontier_key(I,Keys) <=> snonempty(schild(S,I))))).",
    "fof(frontier_meet_def, axiom, ! [P,S,Keys] : (p_mem(P,sfrontier_meet(S,Keys)) <=> ((? [I] : frontier_key(I,Keys)) & ! [I] : (frontier_key(I,Keys) => p_mem(P,schild(S,I)))))).",
    "fof(set_head, axiom, ! [P,S] : (p_mem(P,shead(S)) <=> ? [I,Q] : (p_mem(cons(I,Q),S) & P = cons(I,nil)))).",
    "fof(set_headed, axiom, ! [P,S] : (p_mem(P,sheaded(S)) <=> ? [I,Q] : (P = cons(I,Q) & p_mem(P,S)))).",
    "fof(set_prefix_closure, axiom, ! [P,S] : (p_mem(P,sprefix_closure(S)) <=> (~(P = nil) & ? [Q] : (p_mem(Q,S) & p_prefix(P,Q))))).",
    "fof(set_prefix_closure_below, axiom, ! [P,S] : (p_mem(P,sprefix_closure_below(S)) <=> ? [Q] : (p_mem(Q,S) & p_prefix(P,Q)))).",
    "fof(set_suffix_closure, axiom, ! [P,S] : (p_mem(P,ssuffix_closure(S)) <=> (~(P = nil) & ? [Prefix,Full] : (p_append(Prefix,P,Full) & p_mem(Full,S))))).",
    "fof(set_tails_closure, axiom, ! [P,S] : (p_mem(P,stails_closure(S)) <=> (snonempty(S) & (P = nil | p_mem(P,ssuffix_closure(S)))))).",
    "fof(template_tail, axiom, ! [P,I,T] : (p_mem(P,sapply(tail_template,I,T)) <=> p_mem(P,T))).",
    "fof(template_head, axiom, ! [P,I,T] : (p_mem(P,sapply(head_template,I,T)) <=> P = cons(I,nil))).",
    "fof(template_reconstruct, axiom, ! [P,I,T] : (p_mem(P,sapply(reconstruct_template,I,T)) <=> ? [Q] : (p_mem(Q,T) & P = cons(I,Q)))).",
    "fof(template_prefixed_reconstruct, axiom, ! [P,I,T,Prefix] : (p_mem(P,sapply(prefixed_reconstruct_template(Prefix),I,T)) <=> ? [Q] : (p_mem(Q,T) & p_append(Prefix,cons(I,Q),P)))).",
    "fof(template_range_tail, axiom, ! [P,I,T,Start,End] : (p_mem(P,sapply(range_tail_template(Start,End),I,T)) <=> p_mem(P,srange(T,Start,End)))).",
    "fof(template_range_reconstruct, axiom, ! [P,I,T,Start,End] : (p_mem(P,sapply(range_reconstruct_template(Start,End),I,T)) <=> ? [Q] : (p_mem(Q,srange(T,Start,End)) & P = cons(I,Q)))).",
    "fof(template_prefixed_range_reconstruct, axiom, ! [P,I,T,Prefix,Start,End] : (p_mem(P,sapply(prefixed_range_reconstruct_template(Prefix,Start,End),I,T)) <=> ? [Q] : (p_mem(Q,srange(T,Start,End)) & p_append(Prefix,cons(I,Q),P)))).",
    "",
    "% General Iteration body algebra. These constructors encode arbitrary body",
    "% expression DAGs; head_template/tail_template are the two bound leaves and",
    "% template_static embeds a binder-independent Space expression.",
    "fof(template_empty_general, axiom, ! [P,I,T] : ~p_mem(P,sapply(template_empty,I,T))).",
    "fof(template_static_general, axiom, ! [P,I,T,A] : (p_mem(P,sapply(template_static(A),I,T)) <=> p_mem(P,A))).",
    "fof(template_union_general, axiom, ! [P,I,T,F,G] : (p_mem(P,sapply(template_union(F,G),I,T)) <=> (p_mem(P,sapply(F,I,T)) | p_mem(P,sapply(G,I,T))))).",
    "fof(template_intersection_general, axiom, ! [P,I,T,F,G] : (p_mem(P,sapply(template_intersection(F,G),I,T)) <=> (p_mem(P,sapply(F,I,T)) & p_mem(P,sapply(G,I,T))))).",
    "fof(template_diff_general, axiom, ! [P,I,T,F,G] : (p_mem(P,sapply(template_diff(F,G),I,T)) <=> (p_mem(P,sapply(F,I,T)) & ~p_mem(P,sapply(G,I,T))))).",
    "fof(template_product_general, axiom, ! [P,I,T,F,G] : (p_mem(P,sapply(template_product(F,G),I,T)) <=> ? [Q,R] : (p_mem(Q,sapply(F,I,T)) & p_mem(R,sapply(G,I,T)) & p_append(Q,R,P)))).",
    "fof(template_restriction_general, axiom, ! [P,I,T,F,G] : (p_mem(P,sapply(template_restriction(F,G),I,T)) <=> (p_mem(P,sapply(F,I,T)) & ? [Q] : (p_mem(Q,sapply(G,I,T)) & p_prefix(Q,P))))).",
    "fof(template_wrap_general, axiom, ! [P,I,T,F,Prefix] : (p_mem(P,sapply(template_wrap(F,Prefix),I,T)) <=> ? [Q] : (p_mem(Q,sapply(F,I,T)) & p_append(Prefix,Q,P)))).",
    "fof(template_unwrap_general, axiom, ! [P,I,T,F,Prefix] : (p_mem(P,sapply(template_unwrap(F,Prefix),I,T)) <=> ? [Full] : (p_append(Prefix,P,Full) & p_mem(Full,sapply(F,I,T))))).",
    "fof(template_tails_union_general, axiom, ! [P,I,T,F] : (p_mem(P,sapply(template_tails_union(F),I,T)) <=> ? [J] : p_mem(cons(J,P),sapply(F,I,T)))).",
    "fof(template_tails_intersection_general, axiom, ! [P,I,T,F] : (p_mem(P,sapply(template_tails_intersection(F),I,T)) <=> ((? [J] : snonempty(schild(sapply(F,I,T),J))) & ! [J] : (snonempty(schild(sapply(F,I,T),J)) => p_mem(P,schild(sapply(F,I,T),J)))))).",
    "fof(template_prefix_closure_general, axiom, ! [P,I,T,F] : (p_mem(P,sapply(template_prefix_closure(F),I,T)) <=> (~(P = nil) & ? [Q] : (p_mem(Q,sapply(F,I,T)) & p_prefix(P,Q))))).",
    "fof(template_suffix_closure_general, axiom, ! [P,I,T,F] : (p_mem(P,sapply(template_suffix_closure(F),I,T)) <=> (~(P = nil) & ? [Prefix,Full] : (p_append(Prefix,P,Full) & p_mem(Full,sapply(F,I,T)))))).",
    "fof(template_tails_closure_general, axiom, ! [P,I,T,F] : (p_mem(P,sapply(template_tails_closure(F),I,T)) <=> (snonempty(sapply(F,I,T)) & (P = nil | p_mem(P,ssuffix_closure(sapply(F,I,T))))))).",
    "fof(template_range_general, axiom, ! [P,I,T,F,Start,End] : (p_mem(P,sapply(template_range(F,Start,End),I,T)) <=> p_mem(P,srange(sapply(F,I,T),Start,End)))).",
    "fof(iter_source_headed_def, axiom, ! [S] : (iter_source_headed(S) <=> ? [I] : snonempty(schild(S,I)))).",
    "fof(template_independent_static, axiom, ! [A] : template_independent(template_static(A))).",
    "fof(template_independent_union, axiom, ! [F,G] : ((template_independent(F) & template_independent(G)) => template_independent(template_union(F,G)))).",
    "fof(template_independent_intersection, axiom, ! [F,G] : ((template_independent(F) & template_independent(G)) => template_independent(template_intersection(F,G)))).",
    "fof(template_independent_diff, axiom, ! [F,G] : ((template_independent(F) & template_independent(G)) => template_independent(template_diff(F,G)))).",
    "fof(template_independent_product, axiom, ! [F,G] : ((template_independent(F) & template_independent(G)) => template_independent(template_product(F,G)))).",
    "fof(template_independent_restriction, axiom, ! [F,G] : ((template_independent(F) & template_independent(G)) => template_independent(template_restriction(F,G)))).",
    "fof(template_independent_wrap, axiom, ! [F,Prefix] : (template_independent(F) => template_independent(template_wrap(F,Prefix)))).",
    "fof(template_independent_unwrap, axiom, ! [F,Prefix] : (template_independent(F) => template_independent(template_unwrap(F,Prefix)))).",
    "fof(template_independent_tails_union, axiom, ! [F] : (template_independent(F) => template_independent(template_tails_union(F)))).",
    "fof(template_independent_tails_intersection, axiom, ! [F] : (template_independent(F) => template_independent(template_tails_intersection(F)))).",
    "fof(template_independent_prefix_closure, axiom, ! [F] : (template_independent(F) => template_independent(template_prefix_closure(F)))).",
    "fof(template_independent_suffix_closure, axiom, ! [F] : (template_independent(F) => template_independent(template_suffix_closure(F)))).",
    "fof(template_independent_tails_closure, axiom, ! [F] : (template_independent(F) => template_independent(template_tails_closure(F)))).",
    "fof(template_independent_range, axiom, ! [F,Start,End] : (template_independent(F) => template_independent(template_range(F,Start,End)))).",
    "fof(template_independent_apply, axiom, ! [P,F,I,T] : (template_independent(F) => (p_mem(P,sapply(F,I,T)) <=> p_mem(P,template_value(F))))).",
    "fof(template_static_value, axiom, ! [A] : template_value(template_static(A)) = A).",
    "fof(set_iter, axiom, ! [P,S,F] : (p_mem(P,siter(S,F)) <=> ? [I] : (snonempty(schild(S,I)) & p_mem(P,sapply(F,I,schild(S,I)))))).",
    "",
    "% Eager trie operations mapped into path-set operations.",
    "fof(trie_set_union, axiom, ! [P,A,B] : (p_mem(P,tset(tunion(A,B))) <=> p_mem(P,sunion(tset(A),tset(B))))).",
    "fof(trie_set_intersection, axiom, ! [P,A,B] : (p_mem(P,tset(tinter(A,B))) <=> p_mem(P,sinter(tset(A),tset(B))))).",
    "fof(trie_set_diff, axiom, ! [P,A,B] : (p_mem(P,tset(tdiff(A,B))) <=> p_mem(P,sdiff(tset(A),tset(B))))).",
    "fof(trie_set_nonempty_paths, axiom, ! [P,T] : (p_mem(P,tset(tnonempty_paths(T))) <=> p_mem(P,snonempty_paths(tset(T))))).",
    "fof(trie_set_product, axiom, ! [P,A,B] : (p_mem(P,tset(tproduct(A,B))) <=> p_mem(P,sproduct(tset(A),tset(B))))).",
    "fof(trie_set_restriction, axiom, ! [P,A,B] : (p_mem(P,tset(trestriction(A,B))) <=> p_mem(P,srestriction(tset(A),tset(B))))).",
    "fof(trie_set_raffination, axiom, ! [P,A,B] : (p_mem(P,tset(traffination(A,B))) <=> p_mem(P,sraffination(tset(A),tset(B))))).",
    "fof(trie_set_wrap, axiom, ! [P,T,Prefix] : (p_mem(P,tset(twrap(T,Prefix))) <=> p_mem(P,swrap(tset(T),Prefix)))).",
    "fof(trie_set_unwrap, axiom, ! [P,T,Prefix] : (p_mem(P,tset(tunwrap(T,Prefix))) <=> p_mem(P,sunwrap(tset(T),Prefix)))).",
    "fof(trie_set_range, axiom, ! [P,T,Start,End] : (p_mem(P,tset(trange(T,Start,End))) <=> p_mem(P,srange(tset(T),Start,End)))).",
    "fof(trie_set_tails_union, axiom, ! [P,T] : (p_mem(P,tset(ttails_union(T))) <=> p_mem(P,stails_union(tset(T))))).",
    "fof(trie_set_tails_intersection, axiom, ! [P,T] : (p_mem(P,tset(ttails_intersection(T))) <=> p_mem(P,stails_intersection(tset(T))))).",
    "fof(trie_set_head, axiom, ! [P,T] : (p_mem(P,tset(thead(T))) <=> p_mem(P,shead(tset(T))))).",
    "fof(trie_set_prefix_closure, axiom, ! [P,T] : (p_mem(P,tset(tprefix_closure(T))) <=> p_mem(P,sprefix_closure(tset(T))))).",
    "fof(trie_set_prefix_closure_below, axiom, ! [P,T] : (p_mem(P,tset(tprefix_closure_below(T))) <=> p_mem(P,sprefix_closure_below(tset(T))))).",
    "fof(trie_set_suffix_closure, axiom, ! [P,T] : (p_mem(P,tset(tsuffix_closure(T))) <=> p_mem(P,ssuffix_closure(tset(T))))).",
    "fof(trie_set_tails_closure, axiom, ! [P,T] : (p_mem(P,tset(ttails_closure(T))) <=> p_mem(P,stails_closure(tset(T))))).",
    "fof(trie_set_iter, axiom, ! [P,T,F] : (p_mem(P,tset(titer(T,F))) <=> p_mem(P,siter(tset(T),F)))).",
    "fof(trie_set_fix_tail, axiom, ! [P,T] : (p_mem(P,tset(tfix_tail(T))) <=> p_mem(P,tset(ttails_closure(T))))).",
    "",
    "% Eager trie local observations for constructors.",
    "fof(trie_terminal_union, axiom, ! [A,B] : (tterminal(tunion(A,B)) <=> (tterminal(A) | tterminal(B)))).",
    "fof(trie_terminal_intersection, axiom, ! [A,B] : (tterminal(tinter(A,B)) <=> (tterminal(A) & tterminal(B)))).",
    "fof(trie_terminal_diff, axiom, ! [A,B] : (tterminal(tdiff(A,B)) <=> (tterminal(A) & ~tterminal(B)))).",
    "fof(trie_child_union, axiom, ! [A,B,I] : (tchild(tunion(A,B),I) = tunion(tchild(A,I),tchild(B,I)))).",
    "fof(trie_child_intersection, axiom, ! [A,B,I] : (tchild(tinter(A,B),I) = tinter(tchild(A,I),tchild(B,I)))).",
    "fof(trie_child_diff, axiom, ! [A,B,I] : (tchild(tdiff(A,B),I) = tdiff(tchild(A,I),tchild(B,I)))).",
  )

  val rangeSetTptp: String = trieSetTptp

  val keySetTptp: String = block(
    "% Finite child-key set algebra used by the zipper scheduler.",
    "% This is intentionally separated from path-set denotation: key sets are",
    "% observations over immediate child labels, not materialized path spaces.",
    "fof(keyset_empty, axiom, ! [I] : ~kmem(I,kempty)).",
    "fof(keyset_one, axiom, ! [I,J] : (kmem(I,kone(J)) <=> I = J)).",
    "fof(keyset_union, axiom, ! [I,A,B] : (kmem(I,kunion(A,B)) <=> (kmem(I,A) | kmem(I,B)))).",
    "fof(keyset_intersection, axiom, ! [I,A,B] : (kmem(I,kintersection(A,B)) <=> (kmem(I,A) & kmem(I,B)))).",
    "fof(keyset_diff, axiom, ! [I,A,B] : (kmem(I,kdiff(A,B)) <=> (kmem(I,A) & ~kmem(I,B)))).",
    "fof(keyset_extensional, axiom, ! [A,B] : ((! [I] : (kmem(I,A) <=> kmem(I,B))) => A = B)).",
  )

  val rangeOrderTptp: String = block(
    trieSetTptp,
    "",
    "% Ordered-key border calculus for Range.  This is the unbounded path-set",
    "% counterpart of the demand-driven range_border egg scheduler: first/last",
    "% are defined by lexicographic path order, and child movement is proved",
    "% from those definitions rather than by enumerating fixture alphabets.",
    "fof(item_lt_irreflexive, axiom, ! [A] : ~item_lt(A,A)).",
    "fof(item_lt_asymmetric, axiom, ! [A,B] : (item_lt(A,B) => ~item_lt(B,A))).",
    "fof(item_lt_transitive, axiom, ! [A,B,C] : ((item_lt(A,B) & item_lt(B,C)) => item_lt(A,C))).",
    "fof(item_lt_total, axiom, ! [A,B] : (~(A = B) => (item_lt(A,B) | item_lt(B,A)))).",
    "",
    "fof(path_lt_irreflexive, axiom, ! [P] : ~path_lt(P,P)).",
    "fof(path_lt_nil_cons, axiom, ! [I,P] : path_lt(nil,cons(I,P))).",
    "fof(path_lt_cons_nil, axiom, ! [I,P] : ~path_lt(cons(I,P),nil)).",
    "fof(path_lt_cons_cons, axiom, ! [I,P,J,Q] : (path_lt(cons(I,P),cons(J,Q)) <=> (item_lt(I,J) | (I = J & path_lt(P,Q))))).",
    "fof(path_leq_def, axiom, ! [P,Q] : (path_leq(P,Q) <=> (P = Q | path_lt(P,Q)))).",
    "",
    "fof(range_first_path_def, axiom, ! [S,P] : (range_first_path(S,P) <=> (p_mem(P,S) & ! [Q] : (p_mem(Q,S) => path_leq(P,Q))))).",
    "fof(range_last_path_def, axiom, ! [S,P] : (range_last_path(S,P) <=> (p_mem(P,S) & ! [Q] : (p_mem(Q,S) => path_leq(Q,P))))).",
    "fof(range_first_key_def, axiom, ! [S,I] : (range_first_key(S,I) <=> ? [P] : range_first_path(S,cons(I,P)))).",
    "fof(range_last_key_def, axiom, ! [S,I] : (range_last_key(S,I) <=> ? [P] : range_last_path(S,cons(I,P)))).",
    "",
    "fof(range_select_first_ordered, axiom, ! [P,S] : (range_select(P,S,n0,n1) <=> range_first_path(S,P))).",
    "fof(range_select_last_ordered, axiom, ! [P,S] : (range_select(P,S,nm1,n0) <=> range_last_path(S,P))).",
    "fof(range_select_drop_last_ordered, axiom, ! [P,S] : (range_select(P,S,n0,nm1) <=> (p_mem(P,S) & ~range_last_path(S,P)))).",
  )

  val iterationSetLemmaTptp: String = block(
    "% Lemmas in this block are also emitted as standalone Vampire problems.",
    "% They are included by constructor-level zipper proofs so the ATP can chain",
    "% through named facts instead of rediscovering each Iter template expansion.",
    "fof(lemma_set_iteration_tail_identity, axiom, ! [P,S] : (p_mem(P,siter(S,tail_template)) <=> p_mem(P,stails_union(S)))).",
    "fof(lemma_set_iteration_head_identity, axiom, ! [P,S] : (p_mem(P,siter(S,head_template)) <=> p_mem(P,shead(S)))).",
    "fof(lemma_set_iteration_reconstruct_headed, axiom, ! [P,S] : (p_mem(P,siter(S,reconstruct_template)) <=> p_mem(P,sheaded(S)))).",
    "fof(lemma_set_iteration_prefixed_reconstruct_definition, axiom, ! [P,S,Prefix] : (p_mem(P,siter(S,prefixed_reconstruct_template(Prefix))) <=> ? [I,Q] : (snonempty(schild(S,I)) & p_mem(Q,schild(S,I)) & p_append(Prefix,cons(I,Q),P)))).",
    "fof(lemma_set_iteration_range_tail_definition, axiom, ! [P,S,Start,End] : (p_mem(P,siter(S,range_tail_template(Start,End))) <=> ? [I] : (snonempty(schild(S,I)) & p_mem(P,srange(schild(S,I),Start,End))))).",
    "fof(lemma_set_iteration_range_reconstruct_definition, axiom, ! [P,S,Start,End] : (p_mem(P,siter(S,range_reconstruct_template(Start,End))) <=> ? [I,Q] : (snonempty(schild(S,I)) & p_mem(Q,srange(schild(S,I),Start,End)) & P = cons(I,Q)))).",
    "fof(lemma_set_iteration_prefixed_range_reconstruct_definition, axiom, ! [P,S,Prefix,Start,End] : (p_mem(P,siter(S,prefixed_range_reconstruct_template(Prefix,Start,End))) <=> ? [I,Q] : (snonempty(schild(S,I)) & p_mem(Q,srange(schild(S,I),Start,End)) & p_append(Prefix,cons(I,Q),P)))).",
  )

  val zipperAbstractTptp: String = block(
    trieSetMemberTptp,
    "",
    "% Abstract zipper observations.  These are exactly the local contract a",
    "% virtual zipper must satisfy to be equivalent to its eager trie view.",
    "fof(zipper_member_nil, axiom, ! [Z] : (zmem(nil,Z) <=> zterminal(Z))).",
    "fof(zipper_member_cons, axiom, ! [Z,I,P] : (zmem(cons(I,P),Z) <=> zmem(P,zchild(Z,I)))).",
    "fof(zipper_terminal_trie, axiom, ! [Z] : (zterminal(Z) <=> tterminal(ztrie(Z)))).",
    "fof(zipper_child_trie, axiom, ! [Z,I] : (ztrie(zchild(Z,I)) = tchild(ztrie(Z),I))).",
  )

  val zipperConstructorTptp: String = block(
    trieSetTptp,
    "",
    iterationSetLemmaTptp,
    "",
    "% Concrete zipper constructors and their local implementation rules.",
    "fof(ztrie_base, axiom, ! [T] : (ztrie(triez(T)) = T)).",
    "fof(zterminal_base, axiom, ! [T] : (zterminal(triez(T)) <=> tterminal(T))).",
    "fof(zchild_base, axiom, ! [T,I] : (zchild(triez(T),I) = triez(tchild(T,I)))).",
    "",
    "% Memo is a pure operational cache wrapper.  It must preserve the eager trie",
    "% denotation and forward local terminal/child observations to the wrapped zipper.",
    "fof(ztrie_memo, axiom, ! [Z] : (ztrie(zmemo(Z)) = ztrie(Z))).",
    "fof(zterminal_memo, axiom, ! [Z] : (zterminal(zmemo(Z)) <=> zterminal(Z))).",
    "fof(zchild_memo, axiom, ! [Z,I] : (zchild(zmemo(Z),I) = zmemo(zchild(Z,I)))).",
    "",
    "fof(ztrie_union, axiom, ! [A,B] : (ztrie(zunion(A,B)) = tunion(ztrie(A),ztrie(B)))).",
    "fof(zterminal_union, axiom, ! [A,B] : (zterminal(zunion(A,B)) <=> (zterminal(A) | zterminal(B)))).",
    "fof(zchild_union, axiom, ! [A,B,I] : (zchild(zunion(A,B),I) = zunion(zchild(A,I),zchild(B,I)))).",
    "",
    "fof(ztrie_intersection, axiom, ! [A,B] : (ztrie(zinter(A,B)) = tinter(ztrie(A),ztrie(B)))).",
    "fof(zterminal_intersection, axiom, ! [A,B] : (zterminal(zinter(A,B)) <=> (zterminal(A) & zterminal(B)))).",
    "fof(zchild_intersection, axiom, ! [A,B,I] : (zchild(zinter(A,B),I) = zinter(zchild(A,I),zchild(B,I)))).",
    "",
    "fof(ztrie_diff, axiom, ! [A,B] : (ztrie(zdiff(A,B)) = tdiff(ztrie(A),ztrie(B)))).",
    "fof(zterminal_diff, axiom, ! [A,B] : (zterminal(zdiff(A,B)) <=> (zterminal(A) & ~zterminal(B)))).",
    "fof(zchild_diff, axiom, ! [A,B,I] : (zchild(zdiff(A,B),I) = zdiff(zchild(A,I),zchild(B,I)))).",
    "",
    "fof(ztrie_nonempty_paths, axiom, ! [Z] : (ztrie(znonempty_paths(Z)) = tnonempty_paths(ztrie(Z)))).",
    "fof(ztrie_product, axiom, ! [A,B] : (ztrie(zproduct(A,B)) = tproduct(ztrie(A),ztrie(B)))).",
    "fof(ztrie_restriction, axiom, ! [A,B] : (ztrie(zrestriction(A,B)) = trestriction(ztrie(A),ztrie(B)))).",
    "fof(ztrie_raffination, axiom, ! [A,B] : (ztrie(zraffination(A,B)) = traffination(ztrie(A),ztrie(B)))).",
    "fof(ztrie_wrap, axiom, ! [Z,Prefix] : (ztrie(zwrap(Z,Prefix)) = twrap(ztrie(Z),Prefix))).",
    "fof(ztrie_unwrap, axiom, ! [Z,Prefix] : (ztrie(zunwrap(Z,Prefix)) = tunwrap(ztrie(Z),Prefix))).",
    "fof(ztrie_range, axiom, ! [Z,Start,End] : (ztrie(zrange(Z,Start,End)) = trange(ztrie(Z),Start,End))).",
    "fof(ztrie_range_first, axiom, ! [Z] : (ztrie(zrange_first(Z)) = trange(ztrie(Z),n0,n1))).",
    "fof(ztrie_range_last, axiom, ! [Z] : (ztrie(zrange_last(Z)) = trange(ztrie(Z),nm1,n0))).",
    "fof(ztrie_range_drop_last, axiom, ! [Z] : (ztrie(zrange_drop_last(Z)) = trange(ztrie(Z),n0,nm1))).",
    "fof(ztrie_tails_union, axiom, ! [Z] : (ztrie(ztails_union(Z)) = ttails_union(ztrie(Z)))).",
    "fof(ztrie_tails_intersection, axiom, ! [Z] : (ztrie(ztails_intersection(Z)) = ttails_intersection(ztrie(Z)))).",
    "fof(ztrie_head, axiom, ! [Z] : (ztrie(zhead(Z)) = thead(ztrie(Z)))).",
    "fof(ztrie_prefix_closure, axiom, ! [Z] : (ztrie(zprefix_closure(Z)) = tprefix_closure(ztrie(Z)))).",
    "fof(ztrie_prefix_closure_below, axiom, ! [Z] : (ztrie(zprefix_closure_below(Z)) = tprefix_closure_below(ztrie(Z)))).",
    "fof(ztrie_suffix_closure, axiom, ! [Z] : (ztrie(zsuffix_closure(Z)) = tsuffix_closure(ztrie(Z)))).",
    "fof(ztrie_tails_closure, axiom, ! [Z] : (ztrie(ztails_closure(Z)) = ttails_closure(ztrie(Z)))).",
    "",
    "fof(ztrie_iter, axiom, ! [Z,F] : (ztrie(ziter(Z,F)) = titer(ztrie(Z),F))).",
    "fof(ztrie_iter_tail, axiom, ! [Z] : (ztrie(ziter_tail(Z)) = titer(ztrie(Z),tail_template))).",
    "fof(ztrie_iter_head, axiom, ! [Z] : (ztrie(ziter_head(Z)) = titer(ztrie(Z),head_template))).",
    "fof(ztrie_iter_reconstruct, axiom, ! [Z] : (ztrie(ziter_reconstruct(Z)) = titer(ztrie(Z),reconstruct_template))).",
    "fof(ztrie_iter_prefixed_reconstruct, axiom, ! [Z,Prefix] : (ztrie(ziter_prefixed_reconstruct(Z,Prefix)) = titer(ztrie(Z),prefixed_reconstruct_template(Prefix)))).",
    "fof(ztrie_iter_range_tail, axiom, ! [Z,Start,End] : (ztrie(ziter_range_tail(Z,Start,End)) = titer(ztrie(Z),range_tail_template(Start,End)))).",
    "fof(ztrie_iter_range_reconstruct, axiom, ! [Z,Start,End] : (ztrie(ziter_range_reconstruct(Z,Start,End)) = titer(ztrie(Z),range_reconstruct_template(Start,End)))).",
    "fof(ztrie_iter_prefixed_range_reconstruct, axiom, ! [Z,Prefix,Start,End] : (ztrie(ziter_prefixed_range_reconstruct(Z,Prefix,Start,End)) = titer(ztrie(Z),prefixed_range_reconstruct_template(Prefix,Start,End)))).",
    "fof(ztrie_fix_tail, axiom, ! [Z] : (ztrie(zfix_tail(Z)) = tfix_tail(ztrie(Z)))).",
    "fof(ztrie_fix_head, axiom, ! [Z] : (ztrie(zfix_head(Z)) = tunion(ztrie(Z),thead(ztrie(Z))))).",
    "fof(ztrie_fix_reconstruct, axiom, ! [Z] : (ztrie(zfix_reconstruct(Z)) = ztrie(Z))).",
    "fof(ztrie_fix_range_tail_full, axiom, ! [Z] : (ztrie(zfix_range_tail(Z,n0,n0)) = tfix_tail(ztrie(Z)))).",
    "fof(ztrie_fix_range_tail_empty, axiom, ! [Z] : (ztrie(zfix_range_tail(Z,n1,n1)) = ztrie(Z))).",
    "fof(ztrie_fix_range_reconstruct, axiom, ! [Z,Start,End] : (ztrie(zfix_range_reconstruct(Z,Start,End)) = ztrie(Z))).",
    "fof(ztrie_fix_prefixed_range_reconstruct_empty, axiom, ! [Z,Start,End] : (ztrie(zfix_prefixed_range_reconstruct(Z,nil,Start,End)) = ztrie(Z))).",
  )

  val zipperObservationTptp: String = block(
    zipperConstructorTptp,
    "",
    keySetTptp,
    "",
    "% Canonical trie literals used by concrete operational observation rows.",
    "fof(trie_empty_set, axiom, ! [P] : ~p_mem(P,tset(tempty))).",
    "fof(trie_singleton_set, axiom, ! [P,Q] : (p_mem(P,tset(tsingleton(Q))) <=> P = Q)).",
    "fof(ztrie_emptyz, axiom, ztrie(zempty) = tempty).",
    "",
    "% Observation predicates used by the egg model.",
    "fof(zempty_focus_def, axiom, ! [Z] : (zempty_focus(Z) <=> ! [P] : ~p_mem(P,tset(ztrie(Z))))).",
    "fof(znonterminal_def, axiom, ! [Z] : (znonterminal_obs(Z) <=> ~p_mem(nil,tset(ztrie(Z))))).",
    "fof(zkeys_def, axiom, ! [I,Z] : (kmem(I,zkeys(Z)) <=> ? [Tail] : p_mem(cons(I,Tail),tset(ztrie(Z))))).",
  )

  val zipperFrontierTptp: String = block(
    zipperConstructorTptp,
    "",
    keySetTptp,
    "",
    "% Frontier relations are sound candidate subsets, not necessarily complete",
    "% child/key-set equalities.  This is the operational contract used by the",
    "% lazy Antimirov scheduler for union-like frontier states.",
    "fof(zempty_focus_def, axiom, ! [Z] : (zempty_focus(Z) <=> ! [P] : ~p_mem(P,tset(ztrie(Z))))).",
    "fof(znonempty_focus_def, axiom, ! [Z] : (znonempty_focus(Z) <=> ? [P] : p_mem(P,tset(ztrie(Z))))).",
    "fof(zhas_key_def, axiom, ! [Z,I] : (zhas_key(Z,I) <=> ? [P] : p_mem(cons(I,P),tset(ztrie(Z))))).",
    "fof(zabsent_key_def, axiom, ! [Z,I] : (zabsent_key(Z,I) <=> ~zhas_key(Z,I))).",
    "fof(zkeyset_sound_def, axiom, ! [Z,K] : (zkeyset_sound(Z,K) <=> ! [I] : (kmem(I,K) => zhas_key(Z,I)))).",
    "fof(zchild_focus_def, axiom, ! [Z,I,C] : (zchild_focus(Z,I,C) <=> ztrie(C) = tchild(ztrie(Z),I))).",
    "fof(zsingle_frontier_def, axiom, ! [Z,I,T] : (zsingle_frontier(Z,I,T) <=> (zhas_key(Z,I) & ztrie(T) = tchild(ztrie(Z),I) & ! [J] : (zhas_key(Z,J) => J = I)))).",
    "fof(ztail_frontier_def, axiom, ! [Z,I,T] : (ztail_frontier(Z,I,T) <=> ! [P] : (p_mem(P,tset(ztrie(T))) => p_mem(cons(I,P),tset(ztrie(Z)))))).",
    "fof(zobserved_key_def, axiom, ! [I] : (zobserved_key(I) <=> ((? [Z] : zhas_key(Z,I)) | (? [Z,T] : ztail_frontier(Z,I,T))))).",
    "fof(zobservable_focus_def, axiom, ! [T] : (zobservable_focus(T) <=> ? [Z,I] : ztail_frontier(Z,I,T))).",
    "fof(zfrontier_candidate_def, axiom, ! [Z,C] : (zfrontier_candidate(Z,C) <=> ! [P] : (p_mem(P,tset(ztrie(C))) => p_mem(P,tset(ztrie(Z)))))).",
    "fof(zfrontier_state_candidate_def, axiom, ! [Active,C] : (zfrontier_candidate(Active,C) => zfrontier_candidate(zfrontier_state(Active),C))).",
  )

  val zipperChildFocusTptp: String = block(
    "% Minimal child-focus contract used by the operational scheduler.",
    "% A child-focus term is just the local derivative focus at a known key.",
    "fof(zchild_trie, axiom, ! [Z,I] : (ztrie(zchild(Z,I)) = tchild(ztrie(Z),I))).",
    "fof(zchild_focus_def, axiom, ! [Z,I,C] : (zchild_focus(Z,I,C) <=> ztrie(C) = tchild(ztrie(Z),I))).",
  )

  val zipperContextTptp: String = block(
    "% Virtual context and patch-child semantics.  Context plug is the denotation",
    "% of walking back up a zipper spine; patch-child is the copy-on-write update",
    "% used by virtual up/graft movement.",
    "fof(ztrie_child, axiom, ! [Z,Item] : (ztrie(zchild(Z,Item)) = tchild(ztrie(Z),Item))).",
    "fof(ztrie_patch_child, axiom, ! [Parent,Item,Replacement] : (ztrie(zpatch(Parent,Item,Replacement)) = tpatch(ztrie(Parent),Item,ztrie(Replacement)))).",
    "fof(zterminal_patch_child, axiom, ! [Parent,Item,Replacement] : (zterminal(zpatch(Parent,Item,Replacement)) <=> zterminal(Parent))).",
    "fof(zchild_patch_child_hit, axiom, ! [Parent,Item,Replacement] : (zchild(zpatch(Parent,Item,Replacement),Item) = Replacement)).",
    "fof(zchild_patch_child_miss, axiom, ! [Parent,Item,Other,Replacement] : (~(Item = Other) => (ztrie(zchild(zpatch(Parent,Item,Replacement),Other)) = ztrie(zchild(Parent,Other))))).",
    "fof(tpatch_child_hit, axiom, ! [Parent,Item,Replacement] : (tchild(tpatch(Parent,Item,Replacement),Item) = Replacement)).",
    "fof(tpatch_child_miss, axiom, ! [Parent,Item,Other,Replacement] : (~(Item = Other) => (tchild(tpatch(Parent,Item,Replacement),Other) = tchild(Parent,Other)))).",
    "fof(tpatch_terminal, axiom, ! [Parent,Item,Replacement] : (tterminal(tpatch(Parent,Item,Replacement)) <=> tterminal(Parent))).",
    "fof(trie_patch_child_identity, axiom, ! [T,Item] : (tpatch(T,Item,tchild(T,Item)) = T)).",
    "",
    "fof(ctx_plug_root, axiom, ! [Focus] : (ctxplug(root_ctx,Focus) = Focus)).",
    "fof(ctx_plug_patch_frame, axiom, ! [Ctx,Item,Original,Focus] : (ctxplug(patch_frame(Ctx,Item,Original),Focus) = ctxplug(Ctx,zpatch(Original,Item,Focus)))).",
    "fof(ctx_plug_extensional, axiom, ! [Ctx,Left,Right] : ((ztrie(Left) = ztrie(Right)) => (ztrie(ctxplug(Ctx,Left)) = ztrie(ctxplug(Ctx,Right))))).",
    "fof(ctx_path_root, axiom, ctxpath(root_ctx) = nil).",
    "fof(ctx_path_patch_frame, axiom, ! [Ctx,Item,Original] : (ctxpath(patch_frame(Ctx,Item,Original)) = psnoc(ctxpath(Ctx),Item))).",
    "fof(ctx_down_ctx, axiom, ! [Ctx,Focus,Item] : (down_ctx(Ctx,Focus,Item) = patch_frame(Ctx,Item,Focus))).",
    "fof(ctx_down_focus, axiom, ! [Ctx,Focus,Item] : (down_focus(Ctx,Focus,Item) = zchild(Focus,Item))).",
    "fof(ctx_up_ctx, axiom, ! [Ctx,Item,Original,Focus] : (up_ctx(patch_frame(Ctx,Item,Original),Focus) = Ctx)).",
    "fof(ctx_up_focus, axiom, ! [Ctx,Item,Original,Focus] : (up_focus(patch_frame(Ctx,Item,Original),Focus) = zpatch(Original,Item,Focus))).",
    "fof(ctx_sibling_ctx, axiom, ! [Ctx,Item,Original,Focus,Sibling] : (sibling_ctx(patch_frame(Ctx,Item,Original),Focus,Sibling) = patch_frame(Ctx,Sibling,zpatch(Original,Item,Focus)))).",
    "fof(ctx_sibling_focus, axiom, ! [Ctx,Item,Original,Focus,Sibling] : (sibling_focus(patch_frame(Ctx,Item,Original),Focus,Sibling) = zchild(zpatch(Original,Item,Focus),Sibling))).",
    "fof(ctx_cursor_source, axiom, ! [Ctx,Focus] : (cursor_source(Ctx,Focus) = ctxplug(Ctx,Focus))).",
  )

  private val graphSetAxiomsTptp: String = block(
    "% Operation-graph denotation over arbitrary input data.",
    "fof(graph_from_set, axiom, ! [P,S] : (p_mem(P,gset(gfrom_set(S))) <=> p_mem(P,S))).",
    "fof(graph_from_trie, axiom, ! [P,T] : (p_mem(P,gset(gfrom_trie(T))) <=> p_mem(P,tset(T)))).",
    "fof(graph_set_union, axiom, ! [P,A,B] : (p_mem(P,gset(gunion(A,B))) <=> p_mem(P,sunion(gset(A),gset(B))))).",
    "fof(graph_set_intersection, axiom, ! [P,A,B] : (p_mem(P,gset(ginter(A,B))) <=> p_mem(P,sinter(gset(A),gset(B))))).",
    "fof(graph_set_diff, axiom, ! [P,A,B] : (p_mem(P,gset(gdiff(A,B))) <=> p_mem(P,sdiff(gset(A),gset(B))))).",
    "fof(graph_set_iter, axiom, ! [P,G,F] : (p_mem(P,gset(giter(G,F))) <=> p_mem(P,siter(gset(G),F)))).",
  )

  private val graphZipperAxiomTptp: String =
    "fof(graph_from_zipper, axiom, ! [P,Z] : (p_mem(P,gset(gfrom_zipper(Z))) <=> p_mem(P,tset(ztrie(Z)))))."

  val graphSetTptp: String = block(
    trieSetTptp,
    "",
    graphSetAxiomsTptp,
  )

  val graphOnlyTptp: String = block(
    "% Minimal operation-graph denotation over arbitrary input data.",
    "fof(graph_from_set, axiom, ! [P,S] : (p_mem(P,gset(gfrom_set(S))) <=> p_mem(P,S))).",
    "fof(graph_set_iter, axiom, ! [P,G,F] : (p_mem(P,gset(giter(G,F))) <=> p_mem(P,siter(gset(G),F)))).",
    "fof(set_iter_extensional, axiom, ! [S,T,F] : ((! [Q] : (p_mem(Q,S) <=> p_mem(Q,T))) => (! [P] : (p_mem(P,siter(S,F)) <=> p_mem(P,siter(T,F)))))).",
  )

  val graphConstructorTptp: String = block(
    zipperConstructorTptp,
    "",
    graphSetAxiomsTptp,
    graphZipperAxiomTptp,
  )

  case class VampireProblem(name: String, prelude: String, conjecture: String, expected: String = "Theorem"):
    def tptp: String = Vector("% Generated by morkl.ProofArtifactGeneratorMain", s"% $name", prelude, conjecture, "").mkString("\n")

  private def pathTerm(depth: Int): (String, Vector[String]) =
    val vars = (0 until depth).toVector.map(i => s"I$i")
    val term = vars.reverse.foldLeft("nil")((acc, variable) => s"cons($variable,$acc)")
    term -> vars

  private def trieSetMemberProblem(depth: Int): VampireProblem =
    val (path, vars) = pathTerm(depth)
    val quant = ("T" +: vars).mkString(",")
    VampireProblem(
      s"trie_set_member_depth_$depth",
      trieSetMemberTptp,
      s"fof(conj, conjecture, ! [$quant] : (tmem($path,T) <=> p_mem($path,tset(T)))).",
    )

  private def zipperTrieMemberProblem(depth: Int): VampireProblem =
    val (path, vars) = pathTerm(depth)
    val quant = ("Z" +: vars).mkString(",")
    VampireProblem(
      s"zipper_trie_member_depth_$depth",
      zipperAbstractTptp,
      s"fof(conj, conjecture, ! [$quant] : (zmem($path,Z) <=> tmem($path,ztrie(Z)))).",
    )

  def vampireProblems: Vector[VampireProblem] =
    val base = (0 to 4).toVector.map(trieSetMemberProblem) ++ (0 to 4).toVector.map(zipperTrieMemberProblem)
    val direct = Vector(
      VampireProblem(
        "eager_union_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(tunion(A,B))) <=> (p_mem(P,tset(A)) | p_mem(P,tset(B))))).",
      ),
      VampireProblem(
        "eager_intersection_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(tinter(A,B))) <=> (p_mem(P,tset(A)) & p_mem(P,tset(B))))).",
      ),
      VampireProblem(
        "eager_diff_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(tdiff(A,B))) <=> (p_mem(P,tset(A)) & ~p_mem(P,tset(B))))).",
      ),
      VampireProblem(
        "path_concat_epsilon_left_fo",
        pathNormalizerTptp,
        "fof(conj, conjecture, ! [P] : p_append(nil,P,P)).",
      ),
      VampireProblem(
        "path_concat_epsilon_right_fo",
        pathNormalizerTptp,
        "fof(conj, conjecture, ! [P] : p_append(P,nil,P)).",
      ),
      VampireProblem(
        "set_union_idempotent_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A] : (p_mem(P,sunion(A,A)) <=> p_mem(P,A))).",
      ),
      VampireProblem(
        "set_union_associative_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B,C] : (p_mem(P,sunion(sunion(A,B),C)) <=> p_mem(P,sunion(A,sunion(B,C))))).",
      ),
      VampireProblem(
        "set_intersection_idempotent_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A] : (p_mem(P,sinter(A,A)) <=> p_mem(P,A))).",
      ),
      VampireProblem(
        "set_intersection_associative_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B,C] : (p_mem(P,sinter(sinter(A,B),C)) <=> p_mem(P,sinter(A,sinter(B,C))))).",
      ),
      VampireProblem(
        "set_diff_self_empty_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A] : ~ p_mem(P,sdiff(A,A))).",
      ),
      VampireProblem(
        "set_diff_union_rhs_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B,C] : (p_mem(P,sdiff(A,sunion(B,C))) <=> p_mem(P,sdiff(sdiff(A,B),C)))).",
      ),
      VampireProblem(
        "set_child_intersection_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B,I] : (p_mem(P,schild(sinter(A,B),I)) <=> (p_mem(P,schild(A,I)) & p_mem(P,schild(B,I))))).",
      ),
      VampireProblem(
        "set_child_diff_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B,I] : (p_mem(P,schild(sdiff(A,B),I)) <=> (p_mem(P,schild(A,I)) & ~p_mem(P,schild(B,I))))).",
      ),
      VampireProblem(
        "set_restriction_raffination_partition_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,sunion(srestriction(A,B),sraffination(A,B))) <=> p_mem(P,A))).",
      ),
      VampireProblem(
        "set_restriction_raffination_disjoint_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B] : ~ p_mem(P,sinter(srestriction(A,B),sraffination(A,B)))).",
      ),
      VampireProblem(
        "keyset_union_empty_left_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [K] : kunion(kempty,K) = K).",
      ),
      VampireProblem(
        "keyset_union_empty_right_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [K] : kunion(K,kempty) = K).",
      ),
      VampireProblem(
        "keyset_union_idempotent_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [K] : kunion(K,K) = K).",
      ),
      VampireProblem(
        "keyset_intersection_empty_left_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [K] : kintersection(kempty,K) = kempty).",
      ),
      VampireProblem(
        "keyset_intersection_empty_right_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [K] : kintersection(K,kempty) = kempty).",
      ),
      VampireProblem(
        "keyset_intersection_idempotent_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [K] : kintersection(K,K) = K).",
      ),
      VampireProblem(
        "keyset_intersection_one_hit_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [I] : kintersection(kone(I),kone(I)) = kone(I)).",
      ),
      VampireProblem(
        "keyset_intersection_one_miss_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [I,J] : (~(I = J) => kintersection(kone(I),kone(J)) = kempty)).",
      ),
      VampireProblem(
        "keyset_diff_empty_left_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [K] : kdiff(kempty,K) = kempty).",
      ),
      VampireProblem(
        "keyset_diff_empty_right_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [K] : kdiff(K,kempty) = K).",
      ),
      VampireProblem(
        "keyset_diff_self_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [K] : kdiff(K,K) = kempty).",
      ),
      VampireProblem(
        "keyset_diff_one_hit_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [I] : kdiff(kone(I),kone(I)) = kempty).",
      ),
      VampireProblem(
        "keyset_diff_one_miss_fo",
        keySetTptp,
        "fof(conj, conjecture, ! [I,J] : (~(I = J) => kdiff(kone(I),kone(J)) = kone(I))).",
      ),
      VampireProblem(
        "ordered_before_transitive_fo",
        rangeOrderTptp,
        "fof(conj, conjecture, ! [A,B,C] : ((item_lt(A,B) & item_lt(B,C)) => item_lt(A,C))).",
      ),
      VampireProblem(
        "has_key_keyset_singleton_fo",
        zipperFrontierTptp,
        "fof(conj, conjecture, ! [Z,I] : (zhas_key(Z,I) => zkeyset_sound(Z,kone(I)))).",
      ),
      VampireProblem(
        "child_focus_child_fo",
        zipperChildFocusTptp,
        "fof(conj, conjecture, ! [Z,I] : zchild_focus(Z,I,zchild(Z,I))).",
      ),
      VampireProblem(
        "child_focus_empty_absent_key_fo",
        zipperFrontierTptp,
        "fof(conj, conjecture, ! [Z,I,C] : ((zchild_focus(Z,I,C) & zempty_focus(C)) => zabsent_key(Z,I))).",
      ),
      VampireProblem(
        "scheduler_has_key_observes_fo",
        zipperFrontierTptp,
        "fof(conj, conjecture, ! [Z,I] : (zhas_key(Z,I) => (znonempty_focus(Z) & zobserved_key(I)))).",
      ),
      VampireProblem(
        "scheduler_tail_frontier_observes_fo",
        zipperFrontierTptp,
        "fof(conj, conjecture, ! [Z,I,T] : (ztail_frontier(Z,I,T) => (zobserved_key(I) & zobservable_focus(T)))).",
      ),
      VampireProblem(
        "frontier_candidate_keyset_fo",
        zipperFrontierTptp,
        "fof(conj, conjecture, ! [Z,C,K] : ((zfrontier_candidate(Z,C) & zkeyset_sound(C,K)) => zkeyset_sound(Z,K))).",
      ),
      VampireProblem(
        "frontier_state_candidate_keyset_fo",
        zipperFrontierTptp,
        "fof(conj, conjecture, ! [Active,C,K] : ((zfrontier_candidate(Active,C) & zkeyset_sound(C,K)) => zkeyset_sound(zfrontier_state(Active),K))).",
      ),
      VampireProblem(
        "eager_nonempty_paths_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,T] : (p_mem(P,tset(tnonempty_paths(T))) <=> (p_mem(P,tset(T)) & ~(P = nil)))).",
      ),
      VampireProblem(
        "eager_product_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(tproduct(A,B))) <=> ? [Q,R] : (p_mem(Q,tset(A)) & p_mem(R,tset(B)) & p_append(Q,R,P)))).",
      ),
      VampireProblem(
        "eager_restriction_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(trestriction(A,B))) <=> (p_mem(P,tset(A)) & ? [Q] : (p_mem(Q,tset(B)) & p_prefix(Q,P))))).",
      ),
      VampireProblem(
        "eager_raffination_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(traffination(A,B))) <=> (p_mem(P,tset(A)) & ~ ? [Q] : (p_mem(Q,tset(B)) & p_prefix(Q,P))))).",
      ),
      VampireProblem(
        "eager_wrap_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,T,Prefix] : (p_mem(P,tset(twrap(T,Prefix))) <=> ? [Tail] : (p_mem(Tail,tset(T)) & p_append(Prefix,Tail,P)))).",
      ),
      VampireProblem(
        "eager_unwrap_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,T,Prefix] : (p_mem(P,tset(tunwrap(T,Prefix))) <=> ? [Full] : (p_append(Prefix,P,Full) & p_mem(Full,tset(T))))).",
      ),
      VampireProblem(
        "zipper_memo_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zmemo(Z)))) <=> p_mem(P,tset(ztrie(Z))))).",
      ),
      VampireProblem(
        "zipper_memo_terminal_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [Z] : (zterminal(zmemo(Z)) <=> zterminal(Z))).",
      ),
      VampireProblem(
        "zipper_memo_child_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [Z,I] : (zchild(zmemo(Z),I) = zmemo(zchild(Z,I)))).",
      ),
      VampireProblem(
        "zipper_emptyz_empty_focus_fo",
        zipperObservationTptp,
        "fof(conj, conjecture, zempty_focus(zempty)).",
      ),
      VampireProblem(
        "zipper_emptyz_nonterminal_fo",
        zipperObservationTptp,
        "fof(conj, conjecture, znonterminal_obs(zempty)).",
      ),
      VampireProblem(
        "zipper_keyset_emptyz_fo",
        zipperObservationTptp,
        "fof(conj, conjecture, zkeys(zempty) = kempty).",
      ),
      VampireProblem(
        "zipper_keyset_trie_empty_fo",
        zipperObservationTptp,
        "fof(conj, conjecture, zkeys(triez(tempty)) = kempty).",
      ),
      VampireProblem(
        "zipper_keyset_trie_epsilon_fo",
        zipperObservationTptp,
        "fof(conj, conjecture, zkeys(triez(tsingleton(nil))) = kempty).",
      ),
      VampireProblem(
        "zipper_keyset_trie_item_fo",
        zipperObservationTptp,
        "fof(conj, conjecture, ! [Head] : zkeys(triez(tsingleton(cons(Head,nil)))) = kone(Head)).",
      ),
      VampireProblem(
        "zipper_keyset_trie_concat_fo",
        zipperObservationTptp,
        "fof(conj, conjecture, ! [Head,Rest] : zkeys(triez(tsingleton(cons(Head,Rest)))) = kone(Head)).",
      ),
      VampireProblem(
        "eager_tails_union_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,T] : (p_mem(P,tset(ttails_union(T))) <=> ? [I] : p_mem(cons(I,P),tset(T)))).",
      ),
      VampireProblem(
        "eager_tails_intersection_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,T] : (p_mem(P,tset(ttails_intersection(T))) <=> p_mem(P,stails_intersection(tset(T))))).",
      ),
      VampireProblem(
        "eager_head_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,T] : (p_mem(P,tset(thead(T))) <=> ? [I,Q] : (p_mem(cons(I,Q),tset(T)) & P = cons(I,nil)))).",
      ),
      VampireProblem(
        "eager_prefix_closure_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,T] : (p_mem(P,tset(tprefix_closure(T))) <=> p_mem(P,sprefix_closure(tset(T))))).",
      ),
      VampireProblem(
        "eager_suffix_closure_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,T] : (p_mem(P,tset(tsuffix_closure(T))) <=> p_mem(P,ssuffix_closure(tset(T))))).",
      ),
      VampireProblem(
        "eager_tails_closure_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,T] : (p_mem(P,tset(ttails_closure(T))) <=> p_mem(P,stails_closure(tset(T))))).",
      ),
      VampireProblem(
        "eager_iteration_set_equiv",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,T,F] : (p_mem(P,tset(titer(T,F))) <=> p_mem(P,siter(tset(T),F)))).",
      ),
      VampireProblem(
        "set_child_union_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B,I] : (p_mem(P,schild(sunion(A,B),I)) <=> (p_mem(P,schild(A,I)) | p_mem(P,schild(B,I))))).",
      ),
      VampireProblem(
        "set_iteration_tail_identity",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S] : (p_mem(P,siter(S,tail_template)) <=> p_mem(P,stails_union(S)))).",
      ),
      VampireProblem(
        "set_iteration_head_identity",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S] : (p_mem(P,siter(S,head_template)) <=> p_mem(P,shead(S)))).",
      ),
      VampireProblem(
        "set_iteration_reconstruct_headed",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S] : (p_mem(P,siter(S,reconstruct_template)) <=> p_mem(P,sheaded(S)))).",
      ),
      VampireProblem(
        "set_iteration_prefixed_reconstruct_definition_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,Prefix] : (p_mem(P,siter(S,prefixed_reconstruct_template(Prefix))) <=> ? [I,Q] : (snonempty(schild(S,I)) & p_mem(Q,schild(S,I)) & p_append(Prefix,cons(I,Q),P)))).",
      ),
      VampireProblem(
        "set_iteration_range_tail_definition_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,Start,End] : (p_mem(P,siter(S,range_tail_template(Start,End))) <=> ? [I] : (snonempty(schild(S,I)) & p_mem(P,srange(schild(S,I),Start,End))))).",
      ),
      VampireProblem(
        "set_iteration_range_reconstruct_definition_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,Start,End] : (p_mem(P,siter(S,range_reconstruct_template(Start,End))) <=> ? [I,Q] : (snonempty(schild(S,I)) & p_mem(Q,srange(schild(S,I),Start,End)) & P = cons(I,Q)))).",
      ),
      VampireProblem(
        "set_iteration_prefixed_range_reconstruct_definition_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,Prefix,Start,End] : (p_mem(P,siter(S,prefixed_range_reconstruct_template(Prefix,Start,End))) <=> ? [I,Q] : (snonempty(schild(S,I)) & p_mem(Q,srange(schild(S,I),Start,End)) & p_append(Prefix,cons(I,Q),P)))).",
      ),
      VampireProblem(
        "set_iteration_general_body_union_distribution_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,F,G] : (p_mem(P,siter(S,template_union(F,G))) <=> p_mem(P,sunion(siter(S,F),siter(S,G))))).",
      ),
      VampireProblem(
        "set_iteration_general_invariant_left_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,F,G] : ((iter_source_headed(S) & template_independent(F)) => (p_mem(P,siter(S,template_union(F,G))) <=> p_mem(P,sunion(template_value(F),siter(S,G)))))).",
      ),
      VampireProblem(
        "set_iteration_general_invariant_right_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,F,G] : ((iter_source_headed(S) & template_independent(G)) => (p_mem(P,siter(S,template_union(F,G))) <=> p_mem(P,sunion(siter(S,F),template_value(G)))))).",
      ),
      VampireProblem(
        "set_iteration_general_wrap_hoist_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,F,Prefix] : (p_mem(P,siter(S,template_wrap(F,Prefix))) <=> p_mem(P,swrap(siter(S,F),Prefix)))).",
      ),
      VampireProblem(
        "set_iteration_general_product_right_hoist_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,F,G] : (template_independent(G) => (p_mem(P,siter(S,template_product(F,G))) <=> p_mem(P,sproduct(siter(S,F),template_value(G)))))).",
      ),
      VampireProblem(
        "set_iteration_general_intersection_right_hoist_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,F,G] : (template_independent(G) => (p_mem(P,siter(S,template_intersection(F,G))) <=> p_mem(P,sinter(siter(S,F),template_value(G)))))).",
      ),
      VampireProblem(
        "set_iteration_general_diff_right_hoist_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,F,G] : (template_independent(G) => (p_mem(P,siter(S,template_diff(F,G))) <=> p_mem(P,sdiff(siter(S,F),template_value(G)))))).",
      ),
      VampireProblem(
        "set_iteration_general_restriction_right_hoist_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,F,G] : (template_independent(G) => (p_mem(P,siter(S,template_restriction(F,G))) <=> p_mem(P,srestriction(siter(S,F),template_value(G)))))).",
      ),
      VampireProblem(
        "set_iteration_general_independence_structural_fo",
        trieSetTptp,
        "fof(conj, conjecture, (! [A] : template_independent(template_static(A))) & (! [F,G] : ((template_independent(F) & template_independent(G)) => (template_independent(template_union(F,G)) & template_independent(template_intersection(F,G)) & template_independent(template_diff(F,G)) & template_independent(template_product(F,G)) & template_independent(template_restriction(F,G))))) & (! [F,Prefix] : (template_independent(F) => (template_independent(template_wrap(F,Prefix)) & template_independent(template_unwrap(F,Prefix))))) & (! [F] : (template_independent(F) => (template_independent(template_tails_union(F)) & template_independent(template_tails_intersection(F)) & template_independent(template_prefix_closure(F)) & template_independent(template_suffix_closure(F)) & template_independent(template_tails_closure(F))))) & (! [F,Start,End] : (template_independent(F) => template_independent(template_range(F,Start,End))))).",
      ),
      VampireProblem(
        "set_tails_intersection_closed_two_head_frontier_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,A,B] : ((~(A = B) & snonempty(schild(S,A)) & snonempty(schild(S,B)) & ! [I] : (snonempty(schild(S,I)) => (I = A | I = B))) => (p_mem(P,stails_intersection(S)) <=> p_mem(P,sinter(schild(S,A),schild(S,B)))))).",
      ),
      VampireProblem(
        "set_tails_intersection_closed_frontier_refinement_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,Keys] : (closed_frontier(S,Keys) => (p_mem(P,stails_intersection(S)) <=> p_mem(P,sfrontier_meet(S,Keys))))).",
      ),
      VampireProblem(
        "set_prefix_closure_interior_terminal_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [S,I] : (snonempty(schild(S,I)) => p_mem(nil,schild(sprefix_closure(S),I)))).",
      ),
      VampireProblem(
        "set_product_prefix_closure_left_progress_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,S,R,I,J] : ((snonempty(schild(S,I)) & p_mem(P,schild(R,J))) => p_mem(P,schild(sproduct(schild(sprefix_closure(S),I),R),J)))).",
      ),
      VampireProblem(
        "set_child_product_derivative",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B,I] : (p_mem(P,schild(sproduct(A,B),I)) <=> (p_mem(P,sproduct(schild(A,I),B)) | (p_mem(nil,A) & p_mem(P,schild(B,I)))))).",
      ),
      VampireProblem(
        "set_child_restriction_derivative",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B,I] : (p_mem(P,schild(srestriction(A,B),I)) <=> ((p_mem(nil,B) & p_mem(P,schild(A,I))) | p_mem(P,srestriction(schild(A,I),schild(B,I)))))).",
      ),
      VampireProblem(
        "set_child_raffination_derivative",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,B,I] : (p_mem(P,schild(sraffination(A,B),I)) <=> p_mem(P,sdiff(schild(A,I),schild(srestriction(A,B),I))))).",
      ),
      VampireProblem(
        "set_child_wrap_hit",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,I,Prefix] : (p_mem(P,schild(swrap(A,cons(I,Prefix)),I)) <=> p_mem(P,swrap(A,Prefix)))).",
      ),
      VampireProblem(
        "set_child_unwrap_singleton",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,I] : (p_mem(P,sunwrap(A,cons(I,nil))) <=> p_mem(P,schild(A,I)))).",
      ),
      VampireProblem(
        "set_child_head",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,I] : (p_mem(P,schild(shead(A),I)) <=> (P = nil & snonempty(schild(A,I))))).",
      ),
      VampireProblem(
        "set_child_nonempty_paths",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,I] : (p_mem(P,schild(snonempty_paths(A),I)) <=> p_mem(P,schild(A,I)))).",
      ),
      VampireProblem(
        "set_child_prefix_closure",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,I] : (p_mem(P,schild(sprefix_closure(A),I)) <=> p_mem(P,sprefix_closure_below(schild(A,I))))).",
      ),
      VampireProblem(
        "set_child_prefix_closure_below",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,I] : (p_mem(P,schild(sprefix_closure_below(A),I)) <=> p_mem(P,sprefix_closure_below(schild(A,I))))).",
      ),
      VampireProblem(
        "set_child_suffix_closure_derivative",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,I] : (p_mem(P,schild(ssuffix_closure(A),I)) <=> p_mem(P,schild(sunion(snonempty_paths(A),stails_union(ssuffix_closure(A))),I)))).",
      ),
      VampireProblem(
        "set_child_tails_closure_derivative",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,I] : (p_mem(P,schild(stails_closure(A),I)) <=> p_mem(P,schild(ssuffix_closure(A),I)))).",
      ),
      VampireProblem(
        "antimirov_suffix_frontier_state_child_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,I] : (p_mem(P,schild(ssuffix_closure(A),I)) <=> p_mem(P,schild(sunion(snonempty_paths(A),stails_union(ssuffix_closure(A))),I)))).",
      ),
      VampireProblem(
        "antimirov_tails_frontier_state_child_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,I] : (p_mem(P,schild(stails_closure(A),I)) <=> p_mem(P,schild(ssuffix_closure(A),I)))).",
      ),
      VampireProblem(
        "antimirov_suffix_frontier_nested_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,I,J] : (p_mem(P,schild(schild(ssuffix_closure(A),I),J)) <=> p_mem(P,schild(schild(sunion(snonempty_paths(A),stails_union(ssuffix_closure(A))),I),J)))).",
      ),
      VampireProblem(
        "antimirov_tails_frontier_nested_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A,I,J] : (p_mem(P,schild(schild(stails_closure(A),I),J)) <=> p_mem(P,schild(schild(ssuffix_closure(A),I),J)))).",
      ),
      VampireProblem(
        "frontier_tail_nonempty_has_key_fo",
        zipperFrontierTptp,
        "fof(conj, conjecture, ! [Z,I,T] : ((ztail_frontier(Z,I,T) & znonempty_focus(T)) => zhas_key(Z,I))).",
      ),
      VampireProblem(
        "frontier_candidate_has_key_fo",
        zipperFrontierTptp,
        "fof(conj, conjecture, ! [Z,C,I] : ((zfrontier_candidate(Z,C) & zhas_key(C,I)) => zhas_key(Z,I))).",
      ),
      VampireProblem(
        "frontier_candidate_tail_frontier_fo",
        zipperFrontierTptp,
        "fof(conj, conjecture, ! [Z,C,I,T] : ((zfrontier_candidate(Z,C) & ztail_frontier(C,I,T)) => ztail_frontier(Z,I,T))).",
      ),
      VampireProblem(
        "tails_intersection_single_frontier_keyset_fo",
        zipperFrontierTptp,
        "fof(conj, conjecture, ! [Z,H,T,K] : ((zsingle_frontier(Z,H,T) & zkeyset_sound(T,K)) => zkeyset_sound(ztails_intersection(Z),K))).",
      ),
      VampireProblem(
        "set_terminal_product",
        trieSetTptp,
        "fof(conj, conjecture, ! [A,B] : (p_mem(nil,sproduct(A,B)) <=> (p_mem(nil,A) & p_mem(nil,B)))).",
      ),
      VampireProblem(
        "set_terminal_wrap",
        trieSetTptp,
        "fof(conj, conjecture, ! [A,Prefix] : (p_mem(nil,swrap(A,Prefix)) <=> (Prefix = nil & p_mem(nil,A)))).",
      ),
      VampireProblem(
        "set_terminal_unwrap",
        trieSetTptp,
        "fof(conj, conjecture, ! [A,Prefix] : (p_mem(nil,sunwrap(A,Prefix)) <=> p_mem(Prefix,A))).",
      ),
      VampireProblem(
        "set_terminal_head_empty",
        trieSetTptp,
        "fof(conj, conjecture, ! [A] : ~p_mem(nil,shead(A))).",
      ),
      VampireProblem(
        "set_terminal_nonempty_paths_empty",
        trieSetTptp,
        "fof(conj, conjecture, ! [A] : ~p_mem(nil,snonempty_paths(A))).",
      ),
      VampireProblem(
        "set_terminal_prefix_closure_empty",
        trieSetTptp,
        "fof(conj, conjecture, ! [A] : ~p_mem(nil,sprefix_closure(A))).",
      ),
      VampireProblem(
        "set_terminal_prefix_closure_below",
        trieSetTptp,
        "fof(conj, conjecture, ! [A] : (p_mem(nil,sprefix_closure_below(A)) <=> snonempty(A))).",
      ),
      VampireProblem(
        "set_terminal_suffix_closure_empty",
        trieSetTptp,
        "fof(conj, conjecture, ! [A] : ~p_mem(nil,ssuffix_closure(A))).",
      ),
      VampireProblem(
        "set_tails_closure_definition_fo",
        trieSetTptp,
        "fof(conj, conjecture, ! [P,A] : (p_mem(P,stails_closure(A)) <=> (snonempty(A) & (P = nil | p_mem(P,ssuffix_closure(A)))))).",
      ),
      VampireProblem(
        "set_range_full_sentinel",
        rangeSetTptp,
        "fof(conj, conjecture, ! [P,S] : (p_mem(P,srange(S,n0,n0)) <=> p_mem(P,S))).",
      ),
      VampireProblem(
        "set_range_empty_one_one",
        rangeSetTptp,
        "fof(conj, conjecture, ! [P,S] : ~p_mem(P,srange(S,n1,n1))).",
      ),
      VampireProblem(
        "eager_range_set_equiv",
        rangeSetTptp,
        "fof(conj, conjecture, ! [P,T,Start,End] : (p_mem(P,tset(trange(T,Start,End))) <=> p_mem(P,srange(tset(T),Start,End)))).",
      ),
      VampireProblem(
        "set_range_subset_fo",
        rangeSetTptp,
        "fof(conj, conjecture, ! [P,S,Start,End] : (p_mem(P,srange(S,Start,End)) => p_mem(P,S))).",
      ),
      VampireProblem(
        "set_range_first_terminal_fo",
        rangeSetTptp,
        "fof(conj, conjecture, ! [S] : (p_mem(nil,S) => p_mem(nil,srange(S,n0,n1)))).",
      ),
      VampireProblem(
        "set_range_first_child_terminal_empty_fo",
        rangeOrderTptp,
        "fof(conj, conjecture, ! [P,S,I] : (p_mem(nil,S) => ~p_mem(P,schild(srange(S,n0,n1),I)))).",
      ),
      VampireProblem(
        "set_range_first_child_selected_sound_fo",
        rangeOrderTptp,
        "fof(conj, conjecture, ! [P,S,I] : ((range_first_key(S,I) & p_mem(P,schild(srange(S,n0,n1),I))) => p_mem(P,srange(schild(S,I),n0,n1)))).",
      ),
      VampireProblem(
        "set_range_first_child_pruned_fo",
        rangeOrderTptp,
        "fof(conj, conjecture, ! [P,S,I,H] : ((range_first_key(S,H) & ~(I = H)) => ~p_mem(P,schild(srange(S,n0,n1),I)))).",
      ),
      VampireProblem(
        "set_range_last_child_selected_sound_fo",
        rangeOrderTptp,
        "fof(conj, conjecture, ! [P,S,I] : ((range_last_key(S,I) & p_mem(P,schild(srange(S,nm1,n0),I))) => p_mem(P,srange(schild(S,I),nm1,n0)))).",
      ),
      VampireProblem(
        "set_range_last_child_pruned_fo",
        rangeOrderTptp,
        "fof(conj, conjecture, ! [P,S,I,H] : ((range_last_key(S,H) & ~(I = H)) => ~p_mem(P,schild(srange(S,nm1,n0),I)))).",
      ),
      VampireProblem(
        "set_range_drop_last_child_before_last_fo",
        rangeOrderTptp,
        "fof(conj, conjecture, ! [P,S,I,H] : ((range_last_key(S,H) & item_lt(I,H)) => (p_mem(P,schild(srange(S,n0,nm1),I)) <=> p_mem(P,schild(S,I))))).",
      ),
      VampireProblem(
        "set_range_drop_last_child_after_last_fo",
        rangeOrderTptp,
        "fof(conj, conjecture, ! [P,S,I,H] : ((range_last_key(S,H) & item_lt(H,I)) => ~p_mem(P,schild(srange(S,n0,nm1),I)))).",
      ),
      VampireProblem(
        "zipper_base_terminal_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [T] : (zterminal(triez(T)) <=> tterminal(ztrie(triez(T))))).",
      ),
      VampireProblem(
        "zipper_base_child_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [T,I] : (ztrie(zchild(triez(T),I)) = tchild(ztrie(triez(T)),I))).",
      ),
      VampireProblem(
        "zipper_iteration_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z,F] : (p_mem(P,tset(ztrie(ziter(Z,F)))) <=> p_mem(P,siter(tset(ztrie(Z)),F)))).",
      ),
      VampireProblem(
        "zipper_iter_tail_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(ziter_tail(Z)))) <=> p_mem(P,stails_union(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "zipper_iter_head_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(ziter_head(Z)))) <=> p_mem(P,shead(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "zipper_iter_reconstruct_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(ziter_reconstruct(Z)))) <=> p_mem(P,sheaded(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "zipper_iter_prefixed_reconstruct_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z,Prefix] : (p_mem(P,tset(ztrie(ziter_prefixed_reconstruct(Z,Prefix)))) <=> ? [I,Q] : (snonempty(schild(tset(ztrie(Z)),I)) & p_mem(Q,schild(tset(ztrie(Z)),I)) & p_append(Prefix,cons(I,Q),P)))).",
      ),
      VampireProblem(
        "zipper_iter_range_tail_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z,Start,End] : (p_mem(P,tset(ztrie(ziter_range_tail(Z,Start,End)))) <=> ? [I] : (snonempty(schild(tset(ztrie(Z)),I)) & p_mem(P,srange(schild(tset(ztrie(Z)),I),Start,End))))).",
      ),
      VampireProblem(
        "zipper_iter_range_reconstruct_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z,Start,End] : (p_mem(P,tset(ztrie(ziter_range_reconstruct(Z,Start,End)))) <=> ? [I,Q] : (snonempty(schild(tset(ztrie(Z)),I)) & p_mem(Q,srange(schild(tset(ztrie(Z)),I),Start,End)) & P = cons(I,Q)))).",
      ),
      VampireProblem(
        "zipper_iter_prefixed_range_reconstruct_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z,Prefix,Start,End] : (p_mem(P,tset(ztrie(ziter_prefixed_range_reconstruct(Z,Prefix,Start,End)))) <=> ? [I,Q] : (snonempty(schild(tset(ztrie(Z)),I)) & p_mem(Q,srange(schild(tset(ztrie(Z)),I),Start,End)) & p_append(Prefix,cons(I,Q),P)))).",
      ),
      VampireProblem(
        "zipper_fixpoint_tail_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zfix_tail(Z)))) <=> p_mem(P,stails_closure(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "zipper_fixpoint_head_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zfix_head(Z)))) <=> p_mem(P,sunion(tset(ztrie(Z)),shead(tset(ztrie(Z))))))).",
      ),
      VampireProblem(
        "zipper_fixpoint_reconstruct_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zfix_reconstruct(Z)))) <=> p_mem(P,tset(ztrie(Z))))).",
      ),
      VampireProblem(
        "zipper_fixpoint_range_tail_full_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zfix_range_tail(Z,n0,n0)))) <=> p_mem(P,stails_closure(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "zipper_fixpoint_range_tail_empty_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zfix_range_tail(Z,n1,n1)))) <=> p_mem(P,tset(ztrie(Z))))).",
      ),
      VampireProblem(
        "zipper_fixpoint_range_reconstruct_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z,Start,End] : (p_mem(P,tset(ztrie(zfix_range_reconstruct(Z,Start,End)))) <=> p_mem(P,tset(ztrie(Z))))).",
      ),
      VampireProblem(
        "zipper_nonempty_paths_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(znonempty_paths(Z)))) <=> (p_mem(P,tset(ztrie(Z))) & ~(P = nil)))).",
      ),
      VampireProblem(
        "zipper_product_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(ztrie(zproduct(A,B)))) <=> ? [Q,R] : (p_mem(Q,tset(ztrie(A))) & p_mem(R,tset(ztrie(B))) & p_append(Q,R,P)))).",
      ),
      VampireProblem(
        "zipper_restriction_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(ztrie(zrestriction(A,B)))) <=> (p_mem(P,tset(ztrie(A))) & ? [Q] : (p_mem(Q,tset(ztrie(B))) & p_prefix(Q,P))))).",
      ),
      VampireProblem(
        "zipper_raffination_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(ztrie(zraffination(A,B)))) <=> (p_mem(P,tset(ztrie(A))) & ~ ? [Q] : (p_mem(Q,tset(ztrie(B))) & p_prefix(Q,P))))).",
      ),
      VampireProblem(
        "zipper_wrap_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z,Prefix] : (p_mem(P,tset(ztrie(zwrap(Z,Prefix)))) <=> ? [Tail] : (p_mem(Tail,tset(ztrie(Z))) & p_append(Prefix,Tail,P)))).",
      ),
      VampireProblem(
        "zipper_unwrap_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z,Prefix] : (p_mem(P,tset(ztrie(zunwrap(Z,Prefix)))) <=> ? [Full] : (p_append(Prefix,P,Full) & p_mem(Full,tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "zipper_range_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z,Start,End] : (p_mem(P,tset(ztrie(zrange(Z,Start,End)))) <=> p_mem(P,srange(tset(ztrie(Z)),Start,End)))).",
      ),
      VampireProblem(
        "zipper_range_first_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zrange_first(Z)))) <=> p_mem(P,srange(tset(ztrie(Z)),n0,n1)))).",
      ),
      VampireProblem(
        "zipper_range_last_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zrange_last(Z)))) <=> p_mem(P,srange(tset(ztrie(Z)),nm1,n0)))).",
      ),
      VampireProblem(
        "zipper_range_drop_last_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zrange_drop_last(Z)))) <=> p_mem(P,srange(tset(ztrie(Z)),n0,nm1)))).",
      ),
      VampireProblem(
        "zipper_range_full_terminal_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [Z] : (p_mem(nil,tset(ztrie(zrange(Z,n0,n0)))) <=> p_mem(nil,tset(ztrie(Z))))).",
      ),
      VampireProblem(
        "zipper_range_first_terminal_fo",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [Z] : (p_mem(nil,tset(ztrie(Z))) => p_mem(nil,tset(ztrie(zrange_first(Z)))))).",
      ),
      VampireProblem(
        "zipper_tails_union_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(ztails_union(Z)))) <=> ? [I] : p_mem(cons(I,P),tset(ztrie(Z))))).",
      ),
      VampireProblem(
        "zipper_tails_intersection_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(ztails_intersection(Z)))) <=> p_mem(P,stails_intersection(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "zipper_head_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zhead(Z)))) <=> ? [I,Q] : (p_mem(cons(I,Q),tset(ztrie(Z))) & P = cons(I,nil)))).",
      ),
      VampireProblem(
        "zipper_prefix_closure_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zprefix_closure(Z)))) <=> p_mem(P,sprefix_closure(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "zipper_suffix_closure_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zsuffix_closure(Z)))) <=> p_mem(P,ssuffix_closure(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "zipper_tails_closure_materialization_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(ztails_closure(Z)))) <=> p_mem(P,stails_closure(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "zipper_patch_child_terminal_equiv",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Parent,Item,Replacement] : (zterminal(zpatch(Parent,Item,Replacement)) <=> zterminal(Parent))).",
      ),
      VampireProblem(
        "zipper_patch_child_hit_equiv",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Parent,Item,Replacement] : (ztrie(zchild(zpatch(Parent,Item,Replacement),Item)) = ztrie(Replacement))).",
      ),
      VampireProblem(
        "zipper_patch_child_miss_equiv",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Parent,Item,Other,Replacement] : (~(Item = Other) => (ztrie(zchild(zpatch(Parent,Item,Replacement),Other)) = ztrie(zchild(Parent,Other))))).",
      ),
      VampireProblem(
        "zipper_patch_child_identity_equiv",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Parent,Item] : (ztrie(zpatch(Parent,Item,zchild(Parent,Item))) = ztrie(Parent))).",
      ),
      VampireProblem(
        "zipper_context_root_plug_equiv",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Focus] : (ztrie(ctxplug(root_ctx,Focus)) = ztrie(Focus))).",
      ),
      VampireProblem(
        "zipper_context_down_plug_invariance",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Focus,Item] : (ztrie(ctxplug(down_ctx(Ctx,Focus,Item),down_focus(Ctx,Focus,Item))) = ztrie(ctxplug(Ctx,Focus)))).",
      ),
      VampireProblem(
        "zipper_context_up_after_down_context",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Focus,Item] : (up_ctx(down_ctx(Ctx,Focus,Item),down_focus(Ctx,Focus,Item)) = Ctx)).",
      ),
      VampireProblem(
        "zipper_context_up_after_down_focus",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Focus,Item] : (ztrie(up_focus(down_ctx(Ctx,Focus,Item),down_focus(Ctx,Focus,Item))) = ztrie(Focus))).",
      ),
      VampireProblem(
        "zipper_context_graft_materialization",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Focus,Item,Replacement] : (ztrie(ctxplug(down_ctx(Ctx,Focus,Item),Replacement)) = ztrie(ctxplug(Ctx,zpatch(Focus,Item,Replacement))))).",
      ),
      VampireProblem(
        "zipper_context_cursor_source_plug",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Focus] : (ztrie(cursor_source(Ctx,Focus)) = ztrie(ctxplug(Ctx,Focus)))).",
      ),
      VampireProblem(
        "zipper_context_root_path",
        zipperContextTptp,
        "fof(conj, conjecture, ctxpath(root_ctx) = nil).",
      ),
      VampireProblem(
        "zipper_context_down_path",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Focus,Item] : (ctxpath(down_ctx(Ctx,Focus,Item)) = psnoc(ctxpath(Ctx),Item))).",
      ),
      VampireProblem(
        "zipper_context_up_after_down_path",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Focus,Item] : (ctxpath(up_ctx(down_ctx(Ctx,Focus,Item),down_focus(Ctx,Focus,Item))) = ctxpath(Ctx))).",
      ),
      VampireProblem(
        "zipper_context_sibling_path",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Item,Original,Focus,Sibling] : (ctxpath(sibling_ctx(patch_frame(Ctx,Item,Original),Focus,Sibling)) = psnoc(ctxpath(Ctx),Sibling))).",
      ),
      VampireProblem(
        "zipper_context_sibling_target_context",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Item,Original,Focus,Sibling] : (sibling_ctx(patch_frame(Ctx,Item,Original),Focus,Sibling) = patch_frame(Ctx,Sibling,zpatch(Original,Item,Focus)))).",
      ),
      VampireProblem(
        "zipper_context_sibling_target_focus",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Item,Original,Focus,Sibling] : (sibling_focus(patch_frame(Ctx,Item,Original),Focus,Sibling) = zchild(zpatch(Original,Item,Focus),Sibling))).",
      ),
      VampireProblem(
        "zipper_context_sibling_target_path",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Item,Original,Focus,Sibling] : (ctxpath(patch_frame(Ctx,Sibling,zpatch(Original,Item,Focus))) = psnoc(ctxpath(Ctx),Sibling))).",
      ),
      VampireProblem(
        "zipper_context_sibling_target_plug_invariance",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Item,Original,Focus,Sibling] : (ztrie(ctxplug(patch_frame(Ctx,Sibling,zpatch(Original,Item,Focus)),zchild(zpatch(Original,Item,Focus),Sibling))) = ztrie(ctxplug(Ctx,zpatch(Original,Item,Focus))))).",
      ),
      VampireProblem(
        "zipper_context_sibling_plug_invariance",
        zipperContextTptp,
        "fof(conj, conjecture, ! [Ctx,Item,Original,Focus,Sibling] : (ztrie(ctxplug(sibling_ctx(patch_frame(Ctx,Item,Original),Focus,Sibling),sibling_focus(patch_frame(Ctx,Item,Original),Focus,Sibling))) = ztrie(ctxplug(Ctx,zpatch(Original,Item,Focus))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_union_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(ztrie(zunion(A,B)))) <=> p_mem(P,sunion(tset(ztrie(A)),tset(ztrie(B)))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_intersection_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(ztrie(zinter(A,B)))) <=> p_mem(P,sinter(tset(ztrie(A)),tset(ztrie(B)))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_diff_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(ztrie(zdiff(A,B)))) <=> p_mem(P,sdiff(tset(ztrie(A)),tset(ztrie(B)))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_nonempty_paths_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(znonempty_paths(Z)))) <=> p_mem(P,snonempty_paths(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_product_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(ztrie(zproduct(A,B)))) <=> p_mem(P,sproduct(tset(ztrie(A)),tset(ztrie(B)))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_restriction_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(ztrie(zrestriction(A,B)))) <=> p_mem(P,srestriction(tset(ztrie(A)),tset(ztrie(B)))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_raffination_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,tset(ztrie(zraffination(A,B)))) <=> p_mem(P,sraffination(tset(ztrie(A)),tset(ztrie(B)))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_wrap_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z,Prefix] : (p_mem(P,tset(ztrie(zwrap(Z,Prefix)))) <=> p_mem(P,swrap(tset(ztrie(Z)),Prefix)))).",
      ),
      VampireProblem(
        "arbitrary_zipper_unwrap_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z,Prefix] : (p_mem(P,tset(ztrie(zunwrap(Z,Prefix)))) <=> p_mem(P,sunwrap(tset(ztrie(Z)),Prefix)))).",
      ),
      VampireProblem(
        "arbitrary_zipper_tails_union_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(ztails_union(Z)))) <=> p_mem(P,stails_union(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_tails_intersection_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(ztails_intersection(Z)))) <=> p_mem(P,stails_intersection(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_head_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zhead(Z)))) <=> p_mem(P,shead(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_prefix_closure_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zprefix_closure(Z)))) <=> p_mem(P,sprefix_closure(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_suffix_closure_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(zsuffix_closure(Z)))) <=> p_mem(P,ssuffix_closure(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "arbitrary_zipper_tails_closure_set_equiv",
        zipperConstructorTptp,
        "fof(conj, conjecture, ! [P,Z] : (p_mem(P,tset(ztrie(ztails_closure(Z)))) <=> p_mem(P,stails_closure(tset(ztrie(Z)))))).",
      ),
      VampireProblem(
        "arbitrary_graph_union_set_equiv",
        graphSetTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,gset(gunion(gfrom_set(A),gfrom_set(B)))) <=> p_mem(P,sunion(A,B)))).",
      ),
      VampireProblem(
        "arbitrary_graph_intersection_set_equiv",
        graphSetTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,gset(ginter(gfrom_set(A),gfrom_set(B)))) <=> p_mem(P,sinter(A,B)))).",
      ),
      VampireProblem(
        "arbitrary_graph_diff_set_equiv",
        graphSetTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,gset(gdiff(gfrom_set(A),gfrom_set(B)))) <=> p_mem(P,sdiff(A,B)))).",
      ),
      VampireProblem(
        "arbitrary_graph_iter_set_equiv",
        graphOnlyTptp,
        "fof(conj, conjecture, ! [P,S,F] : (p_mem(P,gset(giter(gfrom_set(S),F))) <=> p_mem(P,siter(S,F)))).",
      ),
      VampireProblem(
        "arbitrary_graph_trie_union_equiv",
        graphSetTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,gset(gunion(gfrom_trie(A),gfrom_trie(B)))) <=> p_mem(P,tset(tunion(A,B))))).",
      ),
      VampireProblem(
        "arbitrary_graph_zipper_union_equiv",
        graphConstructorTptp,
        "fof(conj, conjecture, ! [P,A,B] : (p_mem(P,gset(gunion(gfrom_zipper(A),gfrom_zipper(B)))) <=> p_mem(P,tset(ztrie(zunion(A,B)))))).",
      ),
    )
    val ctor = Vector("union" -> "zunion", "intersection" -> "zinter", "diff" -> "zdiff").flatMap { (name, zctor) =>
      Vector(
        VampireProblem(
          s"zipper_${name}_terminal_equiv",
          zipperConstructorTptp,
          s"fof(conj, conjecture, ! [A,B] : (((zterminal(A) <=> tterminal(ztrie(A))) & (zterminal(B) <=> tterminal(ztrie(B)))) => (zterminal($zctor(A,B)) <=> tterminal(ztrie($zctor(A,B)))))).",
        ),
        VampireProblem(
          s"zipper_${name}_child_equiv",
          zipperConstructorTptp,
          s"fof(conj, conjecture, ! [A,B,I] : (((! [J] : (ztrie(zchild(A,J)) = tchild(ztrie(A),J))) & (! [J] : (ztrie(zchild(B,J)) = tchild(ztrie(B),J)))) => (ztrie(zchild($zctor(A,B),I)) = tchild(ztrie($zctor(A,B)),I)))).",
        ),
      )
    }
    base ++ direct ++ ctor

  case class EggProblem(name: String, program: String, expected: String = "exit-0", note: String = "")

  def eggProblems: Vector[EggProblem] =
    Vector(EggProblem(
      "arbitrary_backend_rewrite_equivalence",
      """; Generated by morkl.ProofArtifactGeneratorMain
        |; Symbolic backend equivalence over arbitrary input data.
        |;
        |; This is an egg-level certificate that source, optimized source, trie,
        |; zipper, and graph forms for the same operation rewrite to one semantic
        |; normal form while preserving the arbitrary input variables X, Y, and F.
        |
        |(datatype Program
        |  (Input String)
        |  (Template String)
        |  (SemUnion Program Program)
        |  (SemIntersection Program Program)
        |  (SemDiff Program Program)
        |  (SemIter Program Program)
        |  (SourceUnion Program Program)
        |  (OptimizedUnion Program Program)
        |  (TrieUnion Program Program)
        |  (ZipperUnion Program Program)
        |  (GraphUnion Program Program)
        |  (SourceIntersection Program Program)
        |  (OptimizedIntersection Program Program)
        |  (TrieIntersection Program Program)
        |  (ZipperIntersection Program Program)
        |  (GraphIntersection Program Program)
        |  (SourceDiff Program Program)
        |  (OptimizedDiff Program Program)
        |  (TrieDiff Program Program)
        |  (ZipperDiff Program Program)
        |  (GraphDiff Program Program)
        |  (SourceIter Program Program)
        |  (OptimizedIter Program Program)
        |  (TrieIter Program Program)
        |  (ZipperIter Program Program)
        |  (GraphIter Program Program))
        |
        |(rewrite (SourceUnion x y) (SemUnion x y))
        |(rewrite (OptimizedUnion x y) (SemUnion x y))
        |(rewrite (TrieUnion x y) (SemUnion x y))
        |(rewrite (ZipperUnion x y) (SemUnion x y))
        |(rewrite (GraphUnion x y) (SemUnion x y))
        |
        |(rewrite (SourceIntersection x y) (SemIntersection x y))
        |(rewrite (OptimizedIntersection x y) (SemIntersection x y))
        |(rewrite (TrieIntersection x y) (SemIntersection x y))
        |(rewrite (ZipperIntersection x y) (SemIntersection x y))
        |(rewrite (GraphIntersection x y) (SemIntersection x y))
        |
        |(rewrite (SourceDiff x y) (SemDiff x y))
        |(rewrite (OptimizedDiff x y) (SemDiff x y))
        |(rewrite (TrieDiff x y) (SemDiff x y))
        |(rewrite (ZipperDiff x y) (SemDiff x y))
        |(rewrite (GraphDiff x y) (SemDiff x y))
        |
        |(rewrite (SourceIter x f) (SemIter x f))
        |(rewrite (OptimizedIter x f) (SemIter x f))
        |(rewrite (TrieIter x f) (SemIter x f))
        |(rewrite (ZipperIter x f) (SemIter x f))
        |(rewrite (GraphIter x f) (SemIter x f))
        |
        |(let $x (Input "X"))
        |(let $y (Input "Y"))
        |(let $f (Template "F"))
        |(let $source_union (SourceUnion $x $y))
        |(let $optimized_union (OptimizedUnion $x $y))
        |(let $trie_union (TrieUnion $x $y))
        |(let $zipper_union (ZipperUnion $x $y))
        |(let $graph_union (GraphUnion $x $y))
        |(let $source_intersection (SourceIntersection $x $y))
        |(let $optimized_intersection (OptimizedIntersection $x $y))
        |(let $trie_intersection (TrieIntersection $x $y))
        |(let $zipper_intersection (ZipperIntersection $x $y))
        |(let $graph_intersection (GraphIntersection $x $y))
        |(let $source_diff (SourceDiff $x $y))
        |(let $optimized_diff (OptimizedDiff $x $y))
        |(let $trie_diff (TrieDiff $x $y))
        |(let $zipper_diff (ZipperDiff $x $y))
        |(let $graph_diff (GraphDiff $x $y))
        |(let $source_iter (SourceIter $x $f))
        |(let $optimized_iter (OptimizedIter $x $f))
        |(let $trie_iter (TrieIter $x $f))
        |(let $zipper_iter (ZipperIter $x $f))
        |(let $graph_iter (GraphIter $x $f))
        |
        |(run 10)
        |
        |(check (= $source_union $optimized_union))
        |(check (= $source_union $trie_union))
        |(check (= $source_union $zipper_union))
        |(check (= $source_union $graph_union))
        |(check (= $source_intersection $optimized_intersection))
        |(check (= $source_intersection $trie_intersection))
        |(check (= $source_intersection $zipper_intersection))
        |(check (= $source_intersection $graph_intersection))
        |(check (= $source_diff $optimized_diff))
        |(check (= $source_diff $trie_diff))
        |(check (= $source_diff $zipper_diff))
        |(check (= $source_diff $graph_diff))
        |(check (= $source_iter $optimized_iter))
        |(check (= $source_iter $trie_iter))
        |(check (= $source_iter $zipper_iter))
        |(check (= $source_iter $graph_iter))
        |""".stripMargin,
      note = "Symbolic egg certificate over arbitrary X/Y/F backend inputs."
    ))

  case class Artifact(kind: String, name: String, expected: String, artifact: String, note: String = "")

  def writeArtifacts(ctx: Ctx,
                     outDir: JPath,
                     vampireOutDir: JPath,
                     manifest: JPath): Vector[Artifact] =
    Files.createDirectories(outDir)
    Files.createDirectories(vampireOutDir)
    val eggOutDir = outDir.resolve("egg")
    Files.createDirectories(eggOutDir)
    Files.createDirectories(manifest.getParent)
    val z3Artifacts = laws.map { law =>
      val artifact = outDir.resolve(s"${law.name}.smt2")
      Files.writeString(artifact, law.smt2(ctx), StandardCharsets.UTF_8)
      Artifact("z3", law.name, law.expected, artifact.toString, law.note)
    }
    val vampireArtifacts = vampireProblems.map { problem =>
      val artifact = vampireOutDir.resolve(s"${problem.name}.p")
      Files.writeString(artifact, problem.tptp, StandardCharsets.UTF_8)
      Artifact("vampire", problem.name, problem.expected, artifact.toString)
    }
    val eggArtifacts = eggProblems.map { problem =>
      val artifact = eggOutDir.resolve(s"${problem.name}.egg")
      Files.writeString(artifact, problem.program, StandardCharsets.UTF_8)
      Artifact("egg", problem.name, problem.expected, artifact.toString, problem.note)
    }
    val artifacts = vampireArtifacts ++ z3Artifacts ++ eggArtifacts
    val manifestText =
      ("kind\tname\texpected\tartifact\tnote" +:
        artifacts.map(a => Vector(a.kind, a.name, a.expected, a.artifact, a.note).map(manifestField).mkString("\t")))
        .mkString("\n") + "\n"
    Files.writeString(manifest, manifestText, StandardCharsets.UTF_8)
    artifacts

  private def manifestField(s: String): String =
    if s.isEmpty then "-" else tsvEscape(s)

  private def tsvEscape(s: String): String =
    s.replace("\\", "\\\\").replace("\t", "\\t").replace("\n", "\\n")

  def generate(alphabet: String = "a,b",
               maxLen: Int = 3,
               outDir: String = "proofs/generated",
               vampireOutDir: String = "proofs/vampire/generated",
               manifest: String = "proofs/proof_manifest.tsv"): Vector[Artifact] =
    val ctx = Ctx(alphabet.split(",").toVector.filter(_.nonEmpty), maxLen)
    writeArtifacts(ctx, Paths.get(outDir), Paths.get(vampireOutDir), Paths.get(manifest))

object ProofArtifactGeneratorMain:
  def main(args: Array[String]): Unit =
    val opts = parseArgs(args.toVector)
    val artifacts = ProofArtifacts.generate(
      alphabet = opts.getOrElse("alphabet", "a,b"),
      maxLen = opts.get("max-len").map(_.toInt).getOrElse(3),
      outDir = opts.getOrElse("out-dir", "proofs/generated"),
      vampireOutDir = opts.getOrElse("vampire-out-dir", "proofs/vampire/generated"),
      manifest = opts.getOrElse("manifest", "proofs/proof_manifest.tsv"),
    )
    println(s"wrote ${artifacts.count(_.kind == "z3")} SMT2 artifacts and ${artifacts.count(_.kind == "vampire")} TPTP artifacts")

  private def parseArgs(args: Vector[String]): Map[String, String] =
    var i = 0
    val out = Map.newBuilder[String, String]
    while i < args.length do
      val key = args(i)
      require(key.startsWith("--"), s"Expected --key, got: $key")
      require(i + 1 < args.length, s"Missing value for $key")
      out += key.drop(2) -> args(i + 1)
      i += 2
    out.result()
