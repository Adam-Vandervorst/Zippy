package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** Drill-down on the aunt-query specimen: print the program, the per-node DAG with baseline
 *  intervals, the lowered SMT, and A/B what each candidate improvement buys. */
class SizeZ3Drilldown extends FunSuite:
  import Space.*
  val INF = Lower.SizeBounds.INF
  def fmt(b: Lower.SizeBounds): String = s"[${b.lo},${if b.hi == INF then "inf" else b.hi};hd${b.loHeaded}]"

  test("aunt-query: program, DAG intervals, lowered z3, and the blocking chain") {
    assume(SizeZ3.available, "z3 not on PATH")
    val fam = AuntQuery.context.m(SpaceMention("family"))
    val prog = subs(Routines.aunt_query_routine.body)(spre = {
      case Space.Mention(sm) if sm.s == "family" => Space.Literal(fam)
      case Space.Mention(sm) if sm.s == "people" => Space.Literal(SpaceValue("Jim", "Pam")) })
    println("=== program (closed) ===")
    println(prog.show)
    println(s"=== |family| = ${fam.paths.size}; eval size = ${eval(prog).paths.size} ===")

    // per-node DAG with baseline intervals
    val ids = collection.mutable.LinkedHashMap.empty[Space, Int]
    def children(sp: Space): List[Space] = sp match
      case Space.Union(a, b) => List(a, b);        case Space.Intersection(a, b) => List(a, b)
      case Space.Subtraction(a, b) => List(a, b);  case Space.Restriction(a, b) => List(a, b)
      case Space.Raffination(a, b) => List(a, b);  case Space.Composition(a, b) => List(a, b)
      case Space.Wrap(a, _) => List(a);            case Space.Unwrap(a, _) => List(a)
      case Space.TailsUnion(a) => List(a);         case Space.TailsIntersection(a) => List(a)
      case Space.Range(a, _, _) => List(a);        case Space.Iteration(src, _, _, b) => List(src, b)
      case Space.Fixpoint(init, _, b) => List(init, b); case _ => Nil
    def id(sp: Space): Int = ids.getOrElseUpdate(sp, { children(sp).foreach(id); ids.size })
    id(prog)
    println("=== DAG (node: kind [baseline] children) ===")
    for (sp, i) <- ids.toVector.sortBy(_._2) do
      val kind = sp.getClass.getSimpleName.stripSuffix("$")
      val extra = sp match
        case Space.Literal(SpaceValue(ps)) => s"|${ps.size}|"
        case Space.Unwrap(_, p) => s"@${p.show}"
        case Space.Wrap(_, p) => s"×${p.show}"
        case Space.Iteration(_, sy, re, _) => s"(${sy.s},${re.s})"
        case _ => ""
      println(f"  n$i%-4s $kind%-16s $extra%-22s ${fmt(Lower.sizeBounds(sp))}%-16s <- ${children(sp).map(c => "n" + ids(c)).mkString(",")}")

    println("=== lowered z3 ===")
    println(SizeZ3.encodeText(prog))
    val (zb, st) = SizeZ3.boundsWithStatus(prog)
    println(s"=== z3 answer: ${fmt(zb)} ($st) ===")

    // A/B: what does pre-optimization (unroll + ground folding) buy?
    val opt = (R"q"() := prog).optimized(using PartialFunction.empty).body
    println("=== after optimized() (IterateLiteral_Union unroll + ground folding) ===")
    println(opt.show)
    println(s"  baseline(opt) = ${fmt(Lower.sizeBounds(opt))}")
    val (zbo, sto) = SizeZ3.boundsWithStatus(opt)
    println(s"  z3(opt)       = ${fmt(zbo)} ($sto)")
  }
  test("open pure GoL: program, DAG intervals, lowered z3") {
    assume(SizeZ3.available, "z3 not on PATH")
    val rules = GoL.Rules(0, 7)
    val inlined = inlineCalls(Space.Call(RoutinePtr("nextStep"), Vector(), Vector(S"field")), rules.defs)
    val open = (R"main"(S"field") := inlined).optimized(using PartialFunction.empty).body
    println("=== open pure GoL (nextStep+neigh inlined, field free) ===")
    println(open.show)
    println(s"=== baseline: ${fmt(Lower.sizeBounds(open))} ===")
    val (zb, st) = SizeZ3.boundsWithStatus(open)
    println(s"=== z3: ${fmt(zb)} ($st) ===")

    // DAG summary: per-kind counts + the interesting nodes (Range windows, exactly-k parts)
    val ids = collection.mutable.LinkedHashMap.empty[Space, Int]
    def children(sp: Space): List[Space] = sp match
      case Space.Union(a, b) => List(a, b);        case Space.Intersection(a, b) => List(a, b)
      case Space.Subtraction(a, b) => List(a, b);  case Space.Restriction(a, b) => List(a, b)
      case Space.Raffination(a, b) => List(a, b);  case Space.Composition(a, b) => List(a, b)
      case Space.Wrap(a, _) => List(a);            case Space.Unwrap(a, _) => List(a)
      case Space.TailsUnion(a) => List(a);         case Space.TailsIntersection(a) => List(a)
      case Space.Range(a, _, _) => List(a);        case Space.Iteration(src, _, _, b) => List(src, b)
      case Space.Fixpoint(init, _, b) => List(init, b); case _ => Nil
    def id(sp: Space): Int = ids.getOrElseUpdate(sp, { children(sp).foreach(id); ids.size })
    id(open)
    println(s"=== DAG: ${ids.size} nodes ===")
    for (sp, i) <- ids.toVector.sortBy(_._2) do
      val kind = sp.getClass.getSimpleName.stripSuffix("$")
      val extra = sp match
        case Space.Literal(SpaceValue(ps)) => s"|${ps.size}|"
        case Space.Unwrap(_, p) => s"@${p.show.take(24)}"
        case Space.Wrap(_, p) => s"×${p.show.take(24)}"
        case Space.Range(_, a, b) => s"[$a,$b)"
        case Space.Iteration(_, sy, re, _) => s"(${sy.s},${re.s})"
        case _ => ""
      println(f"  n$i%-4s $kind%-16s $extra%-26s ${fmt(Lower.sizeBounds(sp))}%-18s <- ${children(sp).map(c => "n" + ids(c)).mkString(",")}")

    // closed contrast: the glider world should now ground-fold
    val glider = SpaceValue(Set((1,0),(2,1),(0,2),(1,2),(2,2)).map((x,y) => Syntax.parse(s"Cell.$x.$y")))
    val closed = subs(open)(spre = { case Space.Mention(sm) if sm.s == "field" => Space.Literal(glider) })
    println(s"=== closed (glider): eval=${eval(closed).paths.size} baseline=${fmt(Lower.sizeBounds(closed))} z3=${fmt(SizeZ3.bounds(closed))} ===")
  }
end SizeZ3Drilldown
