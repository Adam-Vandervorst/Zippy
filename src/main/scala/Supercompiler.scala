package morkl

import scala.collection.mutable
import scala.util.Try

object Matching:
  import Space.*

  private val GeneratedPrefix = "#sc$"
  private val BoundPrefix = "#sc$bound$"

  private def sameFn(a: Any, b: Any): Boolean =
    (a.asInstanceOf[AnyRef] eq b.asInstanceOf[AnyRef])

  private def pathNames(p: Path): (Set[String], Set[String]) =
    val refs = mutable.Set.empty[String]
    val mentions = mutable.Set.empty[String]
    def recp(x: Path): Unit = x match
      case Path.Deref(pr) => refs += pr.s
      case Path.Constant(_) => ()
      case Path.Concat(l, r) =>
        recp(l)
        recp(r)
      case Path.GroundedPP(p, _) => recp(p)
      case Path.GroundedSP(s, _) => recs(s)
    def recs(x: Space): Unit = x match
      case Space.Mention(sm) => mentions += sm.s
      case Space.Empty | Space.Literal(_) => ()
      case Space.Call(_, refs0, mentions0) =>
        refs0.foreach(recp)
        mentions0.foreach(recs)
      case Space.Singleton(p) => recp(p)
      case Space.Union(a, b) => recs(a); recs(b)
      case Space.Intersection(a, b) => recs(a); recs(b)
      case Space.Subtraction(a, b) => recs(a); recs(b)
      case Space.Restriction(a, b) => recs(a); recs(b)
      case Space.Raffination(a, b) => recs(a); recs(b)
      case Space.Composition(a, b) => recs(a); recs(b)
      case Space.Iteration(s, sym, rest, body) =>
        recs(s); refs += sym.s; mentions += rest.s; recs(body)
      case Space.Fold(s, initial, acc, sym, rest, body, update) =>
        recs(s); recp(initial); refs += acc.s; refs += sym.s; mentions += rest.s; recs(body); recp(update)
      case Space.Fixpoint(initial, variable, step) =>
        recs(initial); mentions += variable.s; recs(step)
      case Space.Wrap(s, p) => recs(s); recp(p)
      case Space.Unwrap(s, p) => recs(s); recp(p)
      case Space.TailsUnion(s) => recs(s)
      case Space.TailsIntersection(s) => recs(s)
      case Space.PrefixClosure(s) => recs(s)
      case Space.SuffixClosure(s) => recs(s)
      case Space.TailsClosure(s) => recs(s)
      case Space.GroundedPS(p, _) => recp(p)
      case Space.GroundedSS(s, _) => recs(s)
      case Space.Range(s, _, _) => recs(s)
    recp(p)
    refs.toSet -> mentions.toSet

  private def spaceNames(s: Space): (Set[String], Set[String]) =
    pathNames(Path.GroundedSP(s, _ => PathValue(Nil)))

  private def substNames(sm: Map[SpaceMention, Space], pm: Map[PathRef, Path]): (Set[String], Set[String]) =
    val pns = pm.values.map(pathNames).foldLeft(Set.empty[String] -> Set.empty[String]) {
      case ((pr, sr), (p, s)) => (pr ++ p) -> (sr ++ s)
    }
    val sns = sm.values.map(spaceNames).foldLeft(Set.empty[String] -> Set.empty[String]) {
      case ((pr, sr), (p, s)) => (pr ++ p) -> (sr ++ s)
    }
    (pns._1 ++ sns._1) -> (pns._2 ++ sns._2)

  def freeMentions(s: Space): Set[SpaceMention] = freeMentionsV(s).toSet

  def freeMentionsV(s: Space): Vector[SpaceMention] =
    val out = mutable.LinkedHashSet.empty[SpaceMention]
    def recp(p: Path, boundS: Set[String]): Unit = p match
      case Path.Deref(_) | Path.Constant(_) => ()
      case Path.Concat(l, r) => recp(l, boundS); recp(r, boundS)
      case Path.GroundedPP(p, _) => recp(p, boundS)
      case Path.GroundedSP(s, _) => recs(s, boundS)
    def recs(x: Space, boundS: Set[String]): Unit = x match
      case Space.Mention(sm) => if !boundS(sm.s) then out += sm
      case Space.Empty | Space.Literal(_) => ()
      case Space.Call(_, refs, mentions) =>
        refs.foreach(recp(_, boundS))
        mentions.foreach(recs(_, boundS))
      case Space.Singleton(p) => recp(p, boundS)
      case Space.Union(a, b) => recs(a, boundS); recs(b, boundS)
      case Space.Intersection(a, b) => recs(a, boundS); recs(b, boundS)
      case Space.Subtraction(a, b) => recs(a, boundS); recs(b, boundS)
      case Space.Restriction(a, b) => recs(a, boundS); recs(b, boundS)
      case Space.Raffination(a, b) => recs(a, boundS); recs(b, boundS)
      case Space.Composition(a, b) => recs(a, boundS); recs(b, boundS)
      case Space.Iteration(src, _, rest, body) => recs(src, boundS); recs(body, boundS + rest.s)
      case Space.Fold(src, initial, _, _, rest, body, update) =>
        recs(src, boundS); recp(initial, boundS); recs(body, boundS + rest.s); recp(update, boundS)
      case Space.Fixpoint(initial, variable, step) =>
        recs(initial, boundS); recs(step, boundS + variable.s)
      case Space.Wrap(src, p) => recs(src, boundS); recp(p, boundS)
      case Space.Unwrap(src, p) => recs(src, boundS); recp(p, boundS)
      case Space.TailsUnion(src) => recs(src, boundS)
      case Space.TailsIntersection(src) => recs(src, boundS)
      case Space.PrefixClosure(src) => recs(src, boundS)
      case Space.SuffixClosure(src) => recs(src, boundS)
      case Space.TailsClosure(src) => recs(src, boundS)
      case Space.GroundedPS(p, _) => recp(p, boundS)
      case Space.GroundedSS(src, _) => recs(src, boundS)
      case Space.Range(src, _, _) => recs(src, boundS)
    recs(s, Set.empty)
    out.toVector

  def freeRefs(s: Space): Set[PathRef] = freeRefsV(s).toSet

  def freeRefsV(s: Space): Vector[PathRef] =
    val out = mutable.LinkedHashSet.empty[PathRef]
    def recp(p: Path, boundP: Set[String]): Unit = p match
      case Path.Deref(pr) => if !boundP(pr.s) then out += pr
      case Path.Constant(_) => ()
      case Path.Concat(l, r) => recp(l, boundP); recp(r, boundP)
      case Path.GroundedPP(p, _) => recp(p, boundP)
      case Path.GroundedSP(s, _) => recs(s, boundP)
    def recs(x: Space, boundP: Set[String]): Unit = x match
      case Space.Empty | Space.Mention(_) | Space.Literal(_) => ()
      case Space.Call(_, refs, mentions) =>
        refs.foreach(recp(_, boundP))
        mentions.foreach(recs(_, boundP))
      case Space.Singleton(p) => recp(p, boundP)
      case Space.Union(a, b) => recs(a, boundP); recs(b, boundP)
      case Space.Intersection(a, b) => recs(a, boundP); recs(b, boundP)
      case Space.Subtraction(a, b) => recs(a, boundP); recs(b, boundP)
      case Space.Restriction(a, b) => recs(a, boundP); recs(b, boundP)
      case Space.Raffination(a, b) => recs(a, boundP); recs(b, boundP)
      case Space.Composition(a, b) => recs(a, boundP); recs(b, boundP)
      case Space.Iteration(src, sym, _, body) => recs(src, boundP); recs(body, boundP + sym.s)
      case Space.Fold(src, initial, acc, sym, _, body, update) =>
        recs(src, boundP); recp(initial, boundP); recs(body, boundP + acc.s + sym.s); recp(update, boundP + acc.s + sym.s)
      case Space.Fixpoint(initial, _, step) =>
        recs(initial, boundP); recs(step, boundP)
      case Space.Wrap(src, p) => recs(src, boundP); recp(p, boundP)
      case Space.Unwrap(src, p) => recs(src, boundP); recp(p, boundP)
      case Space.TailsUnion(src) => recs(src, boundP)
      case Space.TailsIntersection(src) => recs(src, boundP)
      case Space.PrefixClosure(src) => recs(src, boundP)
      case Space.SuffixClosure(src) => recs(src, boundP)
      case Space.TailsClosure(src) => recs(src, boundP)
      case Space.GroundedPS(p, _) => recp(p, boundP)
      case Space.GroundedSS(src, _) => recs(src, boundP)
      case Space.Range(src, _, _) => recs(src, boundP)
    recs(s, Set.empty)
    out.toVector

  private def makeFresh(used0: Set[String], prefix: String): () => String =
    var used = used0
    var i = 0
    () =>
      var candidate = s"$GeneratedPrefix$prefix$i"
      while used(candidate) do
        i += 1
        candidate = s"$GeneratedPrefix$prefix$i"
      used += candidate
      i += 1
      candidate

  private def renameBound(s: Space, smap: Map[String, SpaceMention], pmap: Map[String, PathRef]): Space =
    def recp(p: Path, activeS: Map[String, SpaceMention], activeP: Map[String, PathRef]): Path = p match
      case Path.Deref(pr) => activeP.get(pr.s).map(Path.Deref(_)).getOrElse(p)
      case Path.Constant(_) => p
      case Path.Concat(l, r) => Path.Concat(recp(l, activeS, activeP), recp(r, activeS, activeP))
      case Path.GroundedPP(p, f) => Path.GroundedPP(recp(p, activeS, activeP), f)
      case Path.GroundedSP(s, f) => Path.GroundedSP(recs(s, activeS, activeP), f)
    def recs(x: Space, activeS: Map[String, SpaceMention], activeP: Map[String, PathRef]): Space = x match
      case Space.Mention(sm) => activeS.get(sm.s).map(Space.Mention(_)).getOrElse(x)
      case Space.Empty | Space.Literal(_) => x
      case Space.Call(r, refs, mentions) => Space.Call(r, refs.map(recp(_, activeS, activeP)), mentions.map(recs(_, activeS, activeP)))
      case Space.Singleton(p) => Space.Singleton(recp(p, activeS, activeP))
      case Space.Union(a, b) => Space.Union(recs(a, activeS, activeP), recs(b, activeS, activeP))
      case Space.Intersection(a, b) => Space.Intersection(recs(a, activeS, activeP), recs(b, activeS, activeP))
      case Space.Subtraction(a, b) => Space.Subtraction(recs(a, activeS, activeP), recs(b, activeS, activeP))
      case Space.Restriction(a, b) => Space.Restriction(recs(a, activeS, activeP), recs(b, activeS, activeP))
      case Space.Raffination(a, b) => Space.Raffination(recs(a, activeS, activeP), recs(b, activeS, activeP))
      case Space.Composition(a, b) => Space.Composition(recs(a, activeS, activeP), recs(b, activeS, activeP))
      case Space.Iteration(src, sym, rest, body) =>
        val nextS = activeS - rest.s
        val nextP = activeP - sym.s
        Space.Iteration(recs(src, activeS, activeP), sym, rest, recs(body, nextS, nextP))
      case Space.Fold(src, initial, acc, sym, rest, body, update) =>
        val nextS = activeS - rest.s
        val nextP = activeP - acc.s - sym.s
        Space.Fold(recs(src, activeS, activeP), recp(initial, activeS, activeP), acc, sym, rest, recs(body, nextS, nextP), recp(update, nextS, nextP))
      case Space.Fixpoint(initial, variable, step) =>
        Space.Fixpoint(recs(initial, activeS, activeP), variable, recs(step, activeS - variable.s, activeP))
      case Space.Wrap(src, p) => Space.Wrap(recs(src, activeS, activeP), recp(p, activeS, activeP))
      case Space.Unwrap(src, p) => Space.Unwrap(recs(src, activeS, activeP), recp(p, activeS, activeP))
      case Space.TailsUnion(src) => Space.TailsUnion(recs(src, activeS, activeP))
      case Space.TailsIntersection(src) => Space.TailsIntersection(recs(src, activeS, activeP))
      case Space.PrefixClosure(src) => Space.PrefixClosure(recs(src, activeS, activeP))
      case Space.SuffixClosure(src) => Space.SuffixClosure(recs(src, activeS, activeP))
      case Space.TailsClosure(src) => Space.TailsClosure(recs(src, activeS, activeP))
      case Space.GroundedPS(p, f) => Space.GroundedPS(recp(p, activeS, activeP), f)
      case Space.GroundedSS(src, f) => Space.GroundedSS(recs(src, activeS, activeP), f)
      case Space.Range(src, start, end) => Space.Range(recs(src, activeS, activeP), start, end)
    recs(s, smap, pmap)

  def subst(s: Space, sm: Map[SpaceMention, Space] = Map.empty, pm: Map[PathRef, Path] = Map.empty): Space =
    val (termPNames, termSNames) = spaceNames(s)
    val (substPNames, substSNames) = substNames(sm, pm)
    val freshS = makeFresh(termSNames ++ substSNames ++ sm.keys.map(_.s), "s")
    val freshP = makeFresh(termPNames ++ substPNames ++ pm.keys.map(_.s), "p")

    def activeFreeMentions(ss: Map[SpaceMention, Space], pp: Map[PathRef, Path]): Set[String] = substNames(ss, pp)._2
    def activeFreeRefs(ss: Map[SpaceMention, Space], pp: Map[PathRef, Path]): Set[String] = substNames(ss, pp)._1

    def recp(p: Path, ss: Map[SpaceMention, Space], pp: Map[PathRef, Path]): Path = p match
      case Path.Deref(pr) => pp.getOrElse(pr, p)
      case Path.Constant(_) => p
      case Path.Concat(l, r) => Path.Concat(recp(l, ss, pp), recp(r, ss, pp))
      case Path.GroundedPP(p, f) => Path.GroundedPP(recp(p, ss, pp), f)
      case Path.GroundedSP(s, f) => Path.GroundedSP(recs(s, ss, pp), f)

    def recs(x: Space, ss: Map[SpaceMention, Space], pp: Map[PathRef, Path]): Space = x match
      case Space.Mention(sm0) => ss.getOrElse(sm0, x)
      case Space.Empty | Space.Literal(_) => x
      case Space.Call(r, refs, mentions) => Space.Call(r, refs.map(recp(_, ss, pp)), mentions.map(recs(_, ss, pp)))
      case Space.Singleton(p) => Space.Singleton(recp(p, ss, pp))
      case Space.Union(a, b) => Space.Union(recs(a, ss, pp), recs(b, ss, pp))
      case Space.Intersection(a, b) => Space.Intersection(recs(a, ss, pp), recs(b, ss, pp))
      case Space.Subtraction(a, b) => Space.Subtraction(recs(a, ss, pp), recs(b, ss, pp))
      case Space.Restriction(a, b) => Space.Restriction(recs(a, ss, pp), recs(b, ss, pp))
      case Space.Raffination(a, b) => Space.Raffination(recs(a, ss, pp), recs(b, ss, pp))
      case Space.Composition(a, b) => Space.Composition(recs(a, ss, pp), recs(b, ss, pp))
      case Space.Iteration(src, sym, rest, body) =>
        val src2 = recs(src, ss, pp)
        val ssBody0 = ss - rest
        val ppBody0 = pp - sym
        val renameS = activeFreeMentions(ssBody0, ppBody0)(rest.s)
        val renameP = activeFreeRefs(ssBody0, ppBody0)(sym.s)
        val rest2 = if renameS then SpaceMention(freshS()).known(rest.sizeHint) else rest
        val sym2 = if renameP then PathRef(freshP()).known(sym.lengthHint) else sym
        val body2 = if renameS || renameP then renameBound(body,
          if renameS then Map(rest.s -> rest2) else Map.empty,
          if renameP then Map(sym.s -> sym2) else Map.empty) else body
        Space.Iteration(src2, sym2, rest2, recs(body2, ssBody0, ppBody0))
      case Space.Fold(src, initial, acc, sym, rest, body, update) =>
        val src2 = recs(src, ss, pp)
        val init2 = recp(initial, ss, pp)
        val ssBody0 = ss - rest
        val ppBody0 = pp - acc - sym
        val freeS = activeFreeMentions(ssBody0, ppBody0)
        val freeP = activeFreeRefs(ssBody0, ppBody0)
        val rest2 = if freeS(rest.s) then SpaceMention(freshS()).known(rest.sizeHint) else rest
        val acc2 = if freeP(acc.s) then PathRef(freshP()).known(acc.lengthHint) else acc
        val sym2 = if freeP(sym.s) then PathRef(freshP()).known(sym.lengthHint) else sym
        val smap = List(rest.s -> rest2).filter((old, neu) => old != neu.s).toMap
        val pmap = List(acc.s -> acc2, sym.s -> sym2).filter((old, neu) => old != neu.s).toMap
        val body2 = if smap.nonEmpty || pmap.nonEmpty then renameBound(body, smap, pmap) else body
        val update2 = if pmap.nonEmpty then
          renameBound(Space.Singleton(update), Map.empty, pmap) match
            case Space.Singleton(p) => p
            case _ => update
        else update
        Space.Fold(src2, init2, acc2, sym2, rest2, recs(body2, ssBody0, ppBody0), recp(update2, ssBody0, ppBody0))
      case Space.Fixpoint(initial, variable, step) =>
        val initial2 = recs(initial, ss, pp)
        val ssStep0 = ss - variable
        val renameS = activeFreeMentions(ssStep0, pp)(variable.s)
        val variable2 = if renameS then SpaceMention(freshS()).known(variable.sizeHint) else variable
        val step2 = if renameS then renameBound(step, Map(variable.s -> variable2), Map.empty) else step
        Space.Fixpoint(initial2, variable2, recs(step2, ssStep0, pp))
      case Space.Wrap(src, p) => Space.Wrap(recs(src, ss, pp), recp(p, ss, pp))
      case Space.Unwrap(src, p) => Space.Unwrap(recs(src, ss, pp), recp(p, ss, pp))
      case Space.TailsUnion(src) => Space.TailsUnion(recs(src, ss, pp))
      case Space.TailsIntersection(src) => Space.TailsIntersection(recs(src, ss, pp))
      case Space.PrefixClosure(src) => Space.PrefixClosure(recs(src, ss, pp))
      case Space.SuffixClosure(src) => Space.SuffixClosure(recs(src, ss, pp))
      case Space.TailsClosure(src) => Space.TailsClosure(recs(src, ss, pp))
      case Space.GroundedPS(p, f) => Space.GroundedPS(recp(p, ss, pp), f)
      case Space.GroundedSS(src, f) => Space.GroundedSS(recs(src, ss, pp), f)
      case Space.Range(src, start, end) => Space.Range(recs(src, ss, pp), start, end)

    ReferenceHints.tag(recs(s, sm, pm))

  def canon(s: Space): Space =
    val (pnames, snames) = spaceNames(s)
    val freshS = makeFresh(snames, "bound$s")
    val freshP = makeFresh(pnames, "bound$p")
    def recp(p: Path, smap: Map[String, SpaceMention], pmap: Map[String, PathRef]): Path = p match
      case Path.Deref(pr) => pmap.get(pr.s).map(Path.Deref(_)).getOrElse(p)
      case Path.Constant(_) => p
      case Path.Concat(l, r) => Path.Concat(recp(l, smap, pmap), recp(r, smap, pmap))
      case Path.GroundedPP(p, f) => Path.GroundedPP(recp(p, smap, pmap), f)
      case Path.GroundedSP(src, f) => Path.GroundedSP(recs(src, smap, pmap), f)
    def recs(x: Space, smap: Map[String, SpaceMention], pmap: Map[String, PathRef]): Space = x match
      case Space.Mention(sm) => smap.get(sm.s).map(Space.Mention(_)).getOrElse(x)
      case Space.Empty | Space.Literal(_) => x
      case Space.Call(r, refs, mentions) => Space.Call(r, refs.map(recp(_, smap, pmap)), mentions.map(recs(_, smap, pmap)))
      case Space.Singleton(p) => Space.Singleton(recp(p, smap, pmap))
      case Space.Union(a, b) => Space.Union(recs(a, smap, pmap), recs(b, smap, pmap))
      case Space.Intersection(a, b) => Space.Intersection(recs(a, smap, pmap), recs(b, smap, pmap))
      case Space.Subtraction(a, b) => Space.Subtraction(recs(a, smap, pmap), recs(b, smap, pmap))
      case Space.Restriction(a, b) => Space.Restriction(recs(a, smap, pmap), recs(b, smap, pmap))
      case Space.Raffination(a, b) => Space.Raffination(recs(a, smap, pmap), recs(b, smap, pmap))
      case Space.Composition(a, b) => Space.Composition(recs(a, smap, pmap), recs(b, smap, pmap))
      case Space.Iteration(src, sym, rest, body) =>
        val sym2 = PathRef(freshP()).known(sym.lengthHint)
        val rest2 = SpaceMention(freshS()).known(rest.sizeHint)
        Space.Iteration(recs(src, smap, pmap), sym2, rest2, recs(body, smap + (rest.s -> rest2), pmap + (sym.s -> sym2)))
      case Space.Fold(src, initial, acc, sym, rest, body, update) =>
        val acc2 = PathRef(freshP()).known(acc.lengthHint)
        val sym2 = PathRef(freshP()).known(sym.lengthHint)
        val rest2 = SpaceMention(freshS()).known(rest.sizeHint)
        val smap2 = smap + (rest.s -> rest2)
        val pmap2 = pmap + (acc.s -> acc2) + (sym.s -> sym2)
        Space.Fold(recs(src, smap, pmap), recp(initial, smap, pmap), acc2, sym2, rest2, recs(body, smap2, pmap2), recp(update, smap2, pmap2))
      case Space.Fixpoint(initial, variable, step) =>
        val variable2 = SpaceMention(freshS()).known(variable.sizeHint)
        Space.Fixpoint(recs(initial, smap, pmap), variable2, recs(step, smap + (variable.s -> variable2), pmap))
      case Space.Wrap(src, p) => Space.Wrap(recs(src, smap, pmap), recp(p, smap, pmap))
      case Space.Unwrap(src, p) => Space.Unwrap(recs(src, smap, pmap), recp(p, smap, pmap))
      case Space.TailsUnion(src) => Space.TailsUnion(recs(src, smap, pmap))
      case Space.TailsIntersection(src) => Space.TailsIntersection(recs(src, smap, pmap))
      case Space.PrefixClosure(src) => Space.PrefixClosure(recs(src, smap, pmap))
      case Space.SuffixClosure(src) => Space.SuffixClosure(recs(src, smap, pmap))
      case Space.TailsClosure(src) => Space.TailsClosure(recs(src, smap, pmap))
      case Space.GroundedPS(p, f) => Space.GroundedPS(recp(p, smap, pmap), f)
      case Space.GroundedSS(src, f) => Space.GroundedSS(recs(src, smap, pmap), f)
      case Space.Range(src, start, end) => Space.Range(recs(src, smap, pmap), start, end)
    ReferenceHints.tag(recs(s, Map.empty, Map.empty))

  def alphaEqual(a: Space, b: Space): Boolean = canon(a) == canon(b)

  private def freeSVar(sm: SpaceMention): Boolean = !sm.s.startsWith(BoundPrefix)
  private def freePVar(pr: PathRef): Boolean = !pr.s.startsWith(BoundPrefix)

  def renaming(a0: Space, b0: Space): Option[(Map[SpaceMention, SpaceMention], Map[PathRef, PathRef])] =
    val a = canon(a0)
    val b = canon(b0)
    val sm = mutable.Map.empty[SpaceMention, SpaceMention]
    val smBack = mutable.Map.empty[SpaceMention, SpaceMention]
    val pm = mutable.Map.empty[PathRef, PathRef]
    val pmBack = mutable.Map.empty[PathRef, PathRef]
    def bindS(x: SpaceMention, y: SpaceMention): Boolean =
      if !freeSVar(x) || !freeSVar(y) then x == y
      else (sm.get(x), smBack.get(y)) match
        case (Some(y0), _) => y0 == y
        case (None, Some(_)) => false
        case (None, None) => sm(x) = y; smBack(y) = x; true
    def bindP(x: PathRef, y: PathRef): Boolean =
      if !freePVar(x) || !freePVar(y) then x == y
      else (pm.get(x), pmBack.get(y)) match
        case (Some(y0), _) => y0 == y
        case (None, Some(_)) => false
        case (None, None) => pm(x) = y; pmBack(y) = x; true
    if goS(a, b, bindS, bindP, strictLeaves = true) then Some(sm.toMap -> pm.toMap) else None

  private def goP(a: Path, b: Path,
                  bindS: (SpaceMention, SpaceMention) => Boolean,
                  bindP: (PathRef, PathRef) => Boolean,
                  strictLeaves: Boolean): Boolean = (a, b) match
    case (Path.Deref(x), Path.Deref(y)) => bindP(x, y)
    case (Path.Constant(x), Path.Constant(y)) => if strictLeaves then x == y else true
    case (Path.Concat(l1, r1), Path.Concat(l2, r2)) => goP(l1, l2, bindS, bindP, strictLeaves) && goP(r1, r2, bindS, bindP, strictLeaves)
    case (Path.GroundedPP(p1, f1), Path.GroundedPP(p2, f2)) => sameFn(f1, f2) && goP(p1, p2, bindS, bindP, strictLeaves)
    case (Path.GroundedSP(s1, f1), Path.GroundedSP(s2, f2)) => sameFn(f1, f2) && goS(s1, s2, bindS, bindP, strictLeaves)
    case _ => false

  private def goS(a: Space, b: Space,
                  bindS: (SpaceMention, SpaceMention) => Boolean,
                  bindP: (PathRef, PathRef) => Boolean,
                  strictLeaves: Boolean): Boolean = (a, b) match
    case (Space.Mention(x), Space.Mention(y)) => bindS(x, y)
    case (Space.Empty, Space.Empty) => true
    case (Space.Literal(x), Space.Literal(y)) => if strictLeaves then x == y else true
    case (Space.Singleton(p), Space.Singleton(q)) => goP(p, q, bindS, bindP, strictLeaves)
    case (Space.Call(r1, ps1, ss1), Space.Call(r2, ps2, ss2)) =>
      r1 == r2 && ps1.length == ps2.length && ss1.length == ss2.length &&
        ps1.lazyZip(ps2).forall(goP(_, _, bindS, bindP, strictLeaves)) &&
        ss1.lazyZip(ss2).forall(goS(_, _, bindS, bindP, strictLeaves))
    case (Space.Union(a1, b1), Space.Union(a2, b2)) => goS(a1, a2, bindS, bindP, strictLeaves) && goS(b1, b2, bindS, bindP, strictLeaves)
    case (Space.Intersection(a1, b1), Space.Intersection(a2, b2)) => goS(a1, a2, bindS, bindP, strictLeaves) && goS(b1, b2, bindS, bindP, strictLeaves)
    case (Space.Subtraction(a1, b1), Space.Subtraction(a2, b2)) => goS(a1, a2, bindS, bindP, strictLeaves) && goS(b1, b2, bindS, bindP, strictLeaves)
    case (Space.Restriction(a1, b1), Space.Restriction(a2, b2)) => goS(a1, a2, bindS, bindP, strictLeaves) && goS(b1, b2, bindS, bindP, strictLeaves)
    case (Space.Raffination(a1, b1), Space.Raffination(a2, b2)) => goS(a1, a2, bindS, bindP, strictLeaves) && goS(b1, b2, bindS, bindP, strictLeaves)
    case (Space.Composition(a1, b1), Space.Composition(a2, b2)) => goS(a1, a2, bindS, bindP, strictLeaves) && goS(b1, b2, bindS, bindP, strictLeaves)
    case (Space.Iteration(s1, y1, r1, b1), Space.Iteration(s2, y2, r2, b2)) =>
      goS(s1, s2, bindS, bindP, strictLeaves) && bindP(y1, y2) && bindS(r1, r2) && goS(b1, b2, bindS, bindP, strictLeaves)
    case (Space.Fold(s1, i1, a1, y1, r1, b1, u1), Space.Fold(s2, i2, a2, y2, r2, b2, u2)) =>
      goS(s1, s2, bindS, bindP, strictLeaves) && goP(i1, i2, bindS, bindP, strictLeaves) &&
        bindP(a1, a2) && bindP(y1, y2) && bindS(r1, r2) &&
        goS(b1, b2, bindS, bindP, strictLeaves) && goP(u1, u2, bindS, bindP, strictLeaves)
    case (Space.Fixpoint(i1, v1, s1), Space.Fixpoint(i2, v2, s2)) =>
      goS(i1, i2, bindS, bindP, strictLeaves) && bindS(v1, v2) && goS(s1, s2, bindS, bindP, strictLeaves)
    case (Space.Wrap(s1, p1), Space.Wrap(s2, p2)) => goS(s1, s2, bindS, bindP, strictLeaves) && goP(p1, p2, bindS, bindP, strictLeaves)
    case (Space.Unwrap(s1, p1), Space.Unwrap(s2, p2)) => goS(s1, s2, bindS, bindP, strictLeaves) && goP(p1, p2, bindS, bindP, strictLeaves)
    case (Space.TailsUnion(s1), Space.TailsUnion(s2)) => goS(s1, s2, bindS, bindP, strictLeaves)
    case (Space.TailsIntersection(s1), Space.TailsIntersection(s2)) => goS(s1, s2, bindS, bindP, strictLeaves)
    case (Space.PrefixClosure(s1), Space.PrefixClosure(s2)) => goS(s1, s2, bindS, bindP, strictLeaves)
    case (Space.SuffixClosure(s1), Space.SuffixClosure(s2)) => goS(s1, s2, bindS, bindP, strictLeaves)
    case (Space.TailsClosure(s1), Space.TailsClosure(s2)) => goS(s1, s2, bindS, bindP, strictLeaves)
    case (Space.GroundedPS(p1, f1), Space.GroundedPS(p2, f2)) => sameFn(f1, f2) && goP(p1, p2, bindS, bindP, strictLeaves)
    case (Space.GroundedSS(s1, f1), Space.GroundedSS(s2, f2)) => sameFn(f1, f2) && goS(s1, s2, bindS, bindP, strictLeaves)
    case (Space.Range(s1, start1, end1), Space.Range(s2, start2, end2)) =>
      start1 == start2 && end1 == end2 && goS(s1, s2, bindS, bindP, strictLeaves)
    case _ => false

  def instanceOf(pattern0: Space, term0: Space): Option[(Map[SpaceMention, Space], Map[PathRef, Path])] =
    val pattern = canon(pattern0)
    val term = canon(term0)
    val sm = mutable.Map.empty[SpaceMention, Space]
    val pm = mutable.Map.empty[PathRef, Path]
    def occursS(v: SpaceMention, t: Space): Boolean = freeMentions(t).exists(_.s == v.s)
    def occursP(v: PathRef, t: Path): Boolean =
      val (ps, _) = pathNames(t)
      ps(v.s)
    def bindS(v: SpaceMention, t: Space): Boolean =
      if !freeSVar(v) then t == Space.Mention(v)
      else if occursS(v, t) && t != Space.Mention(v) then false
      else sm.get(v) match
        case Some(t0) => t0 == t
        case None => sm(v) = t; true
    def bindP(v: PathRef, t: Path): Boolean =
      if !freePVar(v) then t == Path.Deref(v)
      else if occursP(v, t) && t != Path.Deref(v) then false
      else pm.get(v) match
        case Some(t0) => t0 == t
        case None => pm(v) = t; true
    def mp(p: Path, t: Path): Boolean = p match
      case Path.Deref(v) if freePVar(v) => bindP(v, t)
      case Path.Constant(a) => t match
        case Path.Constant(b) => a == b
        case _ => false
      case Path.Concat(l, r) => t match
        case Path.Concat(l2, r2) => mp(l, l2) && mp(r, r2)
        case _ => false
      case Path.GroundedPP(p, f) => t match
        case Path.GroundedPP(p2, f2) => sameFn(f, f2) && mp(p, p2)
        case _ => false
      case Path.GroundedSP(s, f) => t match
        case Path.GroundedSP(s2, f2) => sameFn(f, f2) && ms(s, s2)
        case _ => false
      case Path.Deref(v) => t == Path.Deref(v)
    def ms(p: Space, t: Space): Boolean = p match
      case Space.Mention(v) if freeSVar(v) => bindS(v, t)
      case Space.Mention(v) => t == Space.Mention(v)
      case Space.Empty => t == Space.Empty
      case Space.Literal(a) => t match
        case Space.Literal(b) => a == b
        case _ => false
      case Space.Singleton(a) => t match
        case Space.Singleton(b) => mp(a, b)
        case _ => false
      case Space.Call(r, ps, ss) => t match
        case Space.Call(r2, ps2, ss2) => r == r2 && ps.length == ps2.length && ss.length == ss2.length &&
          ps.lazyZip(ps2).forall(mp) && ss.lazyZip(ss2).forall(ms)
        case _ => false
      case Space.Union(a, b) => t match
        case Space.Union(a2, b2) => ms(a, a2) && ms(b, b2)
        case _ => false
      case Space.Intersection(a, b) => t match
        case Space.Intersection(a2, b2) => ms(a, a2) && ms(b, b2)
        case _ => false
      case Space.Subtraction(a, b) => t match
        case Space.Subtraction(a2, b2) => ms(a, a2) && ms(b, b2)
        case _ => false
      case Space.Restriction(a, b) => t match
        case Space.Restriction(a2, b2) => ms(a, a2) && ms(b, b2)
        case _ => false
      case Space.Raffination(a, b) => t match
        case Space.Raffination(a2, b2) => ms(a, a2) && ms(b, b2)
        case _ => false
      case Space.Composition(a, b) => t match
        case Space.Composition(a2, b2) => ms(a, a2) && ms(b, b2)
        case _ => false
      case Space.Iteration(s, sym, rest, body) => t match
        case Space.Iteration(s2, sym2, rest2, body2) => ms(s, s2) && sym == sym2 && rest == rest2 && ms(body, body2)
        case _ => false
      case Space.Fold(s, initial, acc, sym, rest, body, update) => t match
        case Space.Fold(s2, initial2, acc2, sym2, rest2, body2, update2) =>
          ms(s, s2) && mp(initial, initial2) && acc == acc2 && sym == sym2 && rest == rest2 && ms(body, body2) && mp(update, update2)
        case _ => false
      case Space.Fixpoint(initial, variable, step) => t match
        case Space.Fixpoint(initial2, variable2, step2) =>
          ms(initial, initial2) && variable == variable2 && ms(step, step2)
        case _ => false
      case Space.Wrap(s, p0) => t match
        case Space.Wrap(s2, p2) => ms(s, s2) && mp(p0, p2)
        case _ => false
      case Space.Unwrap(s, p0) => t match
        case Space.Unwrap(s2, p2) => ms(s, s2) && mp(p0, p2)
        case _ => false
      case Space.TailsUnion(s) => t match
        case Space.TailsUnion(s2) => ms(s, s2)
        case _ => false
      case Space.TailsIntersection(s) => t match
        case Space.TailsIntersection(s2) => ms(s, s2)
        case _ => false
      case Space.PrefixClosure(s) => t match
        case Space.PrefixClosure(s2) => ms(s, s2)
        case _ => false
      case Space.SuffixClosure(s) => t match
        case Space.SuffixClosure(s2) => ms(s, s2)
        case _ => false
      case Space.TailsClosure(s) => t match
        case Space.TailsClosure(s2) => ms(s, s2)
        case _ => false
      case Space.GroundedPS(p0, f) => t match
        case Space.GroundedPS(p2, f2) => sameFn(f, f2) && mp(p0, p2)
        case _ => false
      case Space.GroundedSS(s, f) => t match
        case Space.GroundedSS(s2, f2) => sameFn(f, f2) && ms(s, s2)
        case _ => false
      case Space.Range(s, start, end) => t match
        case Space.Range(s2, start2, end2) => start == start2 && end == end2 && ms(s, s2)
        case _ => false
    if ms(pattern, term) then Some(sm.toMap -> pm.toMap) else None

  private def childrenS(s: Space): List[Space | Path] = s match
    case Space.Singleton(p) => List(p)
    case Space.Call(_, refs, mentions) => refs.toList ++ mentions.toList
    case Space.Union(a, b) => List(a, b)
    case Space.Intersection(a, b) => List(a, b)
    case Space.Subtraction(a, b) => List(a, b)
    case Space.Restriction(a, b) => List(a, b)
    case Space.Raffination(a, b) => List(a, b)
    case Space.Composition(a, b) => List(a, b)
    case Space.Iteration(src, _, _, body) => List(src, body)
    case Space.Fold(src, init, _, _, _, body, update) => List(src, init, body, update)
    case Space.Fixpoint(initial, _, step) => List(initial, step)
    case Space.Wrap(src, p) => List(src, p)
    case Space.Unwrap(src, p) => List(src, p)
    case Space.TailsUnion(src) => List(src)
    case Space.TailsIntersection(src) => List(src)
    case Space.PrefixClosure(src) => List(src)
    case Space.SuffixClosure(src) => List(src)
    case Space.TailsClosure(src) => List(src)
    case Space.GroundedPS(p, _) => List(p)
    case Space.GroundedSS(src, _) => List(src)
    case Space.Range(src, _, _) => List(src)
    case _ => Nil

  private def childrenP(p: Path): List[Space | Path] = p match
    case Path.Concat(l, r) => List(l, r)
    case Path.GroundedPP(p, _) => List(p)
    case Path.GroundedSP(s, _) => List(s)
    case _ => Nil

  enum LiteralEmbeddingPolicy:
    case ExactLeaves, LeavesAsAtoms

  private def coupledS(a: Space, b: Space, policy: LiteralEmbeddingPolicy): Boolean = (a, b) match
    case (Space.Empty, Space.Empty) => true
    case (Space.Literal(x), Space.Literal(y)) => policy == LiteralEmbeddingPolicy.LeavesAsAtoms || x == y
    case (Space.Singleton(_), Space.Singleton(_)) => true
    case (Space.Call(r1, ps1, ss1), Space.Call(r2, ps2, ss2)) => r1 == r2 && ps1.length == ps2.length && ss1.length == ss2.length
    case (Space.Union(_, _), Space.Union(_, _)) => true
    case (Space.Intersection(_, _), Space.Intersection(_, _)) => true
    case (Space.Subtraction(_, _), Space.Subtraction(_, _)) => true
    case (Space.Restriction(_, _), Space.Restriction(_, _)) => true
    case (Space.Raffination(_, _), Space.Raffination(_, _)) => true
    case (Space.Composition(_, _), Space.Composition(_, _)) => true
    case (Space.Iteration(_, _, _, _), Space.Iteration(_, _, _, _)) => true
    case (Space.Fold(_, _, _, _, _, _, _), Space.Fold(_, _, _, _, _, _, _)) => true
    case (Space.Fixpoint(_, _, _), Space.Fixpoint(_, _, _)) => true
    case (Space.Wrap(_, _), Space.Wrap(_, _)) => true
    case (Space.Unwrap(_, _), Space.Unwrap(_, _)) => true
    case (Space.TailsUnion(_), Space.TailsUnion(_)) => true
    case (Space.TailsIntersection(_), Space.TailsIntersection(_)) => true
    case (Space.PrefixClosure(_), Space.PrefixClosure(_)) => true
    case (Space.SuffixClosure(_), Space.SuffixClosure(_)) => true
    case (Space.TailsClosure(_), Space.TailsClosure(_)) => true
    case (Space.GroundedPS(_, f1), Space.GroundedPS(_, f2)) => sameFn(f1, f2)
    case (Space.GroundedSS(_, f1), Space.GroundedSS(_, f2)) => sameFn(f1, f2)
    case (Space.Range(_, start1, end1), Space.Range(_, start2, end2)) => start1 == start2 && end1 == end2
    case (Space.Mention(x), Space.Mention(y)) => x == y || (freeSVar(x) && freeSVar(y))
    case _ => false

  private def coupledP(a: Path, b: Path, policy: LiteralEmbeddingPolicy): Boolean = (a, b) match
    case (Path.Constant(x), Path.Constant(y)) => policy == LiteralEmbeddingPolicy.LeavesAsAtoms || x == y
    case (Path.Concat(_, _), Path.Concat(_, _)) => true
    case (Path.Deref(x), Path.Deref(y)) => x == y || (freePVar(x) && freePVar(y))
    case (Path.GroundedPP(_, f1), Path.GroundedPP(_, f2)) => sameFn(f1, f2)
    case (Path.GroundedSP(_, f1), Path.GroundedSP(_, f2)) => sameFn(f1, f2)
    case _ => false

  private def embed(a: Space | Path, b: Space | Path, policy: LiteralEmbeddingPolicy): Boolean = (a, b) match
    case (as: Space, bs: Space) => embedsS(as, bs, policy)
    case (ap: Path, bp: Path) => embedsP(ap, bp, policy)
    case _ => false

  private def embedsS(a: Space, b: Space, policy: LiteralEmbeddingPolicy): Boolean =
    val dive = childrenS(b).exists(embed(a, _, policy))
    val couple = coupledS(a, b, policy) && childrenS(a).lazyZip(childrenS(b)).forall(embed(_, _, policy))
    dive || couple

  private def embedsP(a: Path, b: Path, policy: LiteralEmbeddingPolicy): Boolean =
    val dive = childrenP(b).exists(embed(a, _, policy))
    val couple = coupledP(a, b, policy) && childrenP(a).lazyZip(childrenP(b)).forall(embed(_, _, policy))
    dive || couple

  def embeds(a: Space, b: Space, policy: LiteralEmbeddingPolicy = LiteralEmbeddingPolicy.LeavesAsAtoms): Boolean =
    embedsS(canon(a), canon(b), policy)

  case class Gen(skeleton: Space,
                 lsm: Map[SpaceMention, Space], lpm: Map[PathRef, Path],
                 rsm: Map[SpaceMention, Space], rpm: Map[PathRef, Path])

  def msg(a0: Space, b0: Space): Gen =
    val a = canon(a0)
    val b = canon(b0)
    val (pnamesA, snamesA) = spaceNames(a)
    val (pnamesB, snamesB) = spaceNames(b)
    val freshS = makeFresh(snamesA ++ snamesB, "gS")
    val freshP = makeFresh(pnamesA ++ pnamesB, "gP")
    val sholes = mutable.LinkedHashMap.empty[(Space, Space), SpaceMention]
    val pholes = mutable.LinkedHashMap.empty[(Path, Path), PathRef]
    def holeS(x: Space, y: Space): Space =
      val commonSize = ReferenceHints.spaceSize(x).filter(size => ReferenceHints.spaceSize(y).contains(size))
      Space.Mention(sholes.getOrElseUpdate((x, y), {
        val fresh = SpaceMention(freshS())
        commonSize.fold(fresh)(fresh.known)
      }))
    def holeP(x: Path, y: Path): Path =
      val commonLength = ReferenceHints.pathLength(x).filter(length => ReferenceHints.pathLength(y).contains(length))
      Path.Deref(pholes.getOrElseUpdate((x, y), {
        val fresh = PathRef(freshP())
        commonLength.fold(fresh)(fresh.known)
      }))
    def gp(x: Path, y: Path): Path =
      if x == y then x
      else (x, y) match
        case (Path.Concat(l1, r1), Path.Concat(l2, r2)) => Path.Concat(gp(l1, l2), gp(r1, r2))
        case (Path.GroundedPP(p1, f1), Path.GroundedPP(p2, f2)) if sameFn(f1, f2) => Path.GroundedPP(gp(p1, p2), f1)
        case (Path.GroundedSP(s1, f1), Path.GroundedSP(s2, f2)) if sameFn(f1, f2) => Path.GroundedSP(gs(s1, s2), f1)
        case _ => holeP(x, y)
    def gs(x: Space, y: Space): Space =
      if x == y then x
      else (x, y) match
        case (Space.Singleton(p), Space.Singleton(q)) => Space.Singleton(gp(p, q))
        case (Space.Call(r, ps1, ss1), Space.Call(r2, ps2, ss2)) if r == r2 && ps1.length == ps2.length && ss1.length == ss2.length =>
          Space.Call(r, ps1.lazyZip(ps2).map(gp), ss1.lazyZip(ss2).map(gs))
        case (Space.Union(a1, b1), Space.Union(a2, b2)) => Space.Union(gs(a1, a2), gs(b1, b2))
        case (Space.Intersection(a1, b1), Space.Intersection(a2, b2)) => Space.Intersection(gs(a1, a2), gs(b1, b2))
        case (Space.Subtraction(a1, b1), Space.Subtraction(a2, b2)) => Space.Subtraction(gs(a1, a2), gs(b1, b2))
        case (Space.Restriction(a1, b1), Space.Restriction(a2, b2)) => Space.Restriction(gs(a1, a2), gs(b1, b2))
        case (Space.Raffination(a1, b1), Space.Raffination(a2, b2)) => Space.Raffination(gs(a1, a2), gs(b1, b2))
        case (Space.Composition(a1, b1), Space.Composition(a2, b2)) => Space.Composition(gs(a1, a2), gs(b1, b2))
        case (Space.Iteration(s1, y, r, b1), Space.Iteration(s2, _, _, b2)) => Space.Iteration(gs(s1, s2), y, r, gs(b1, b2))
        case (Space.Fold(s1, i1, a1, y1, r1, b1, u1), Space.Fold(s2, i2, _, _, _, b2, u2)) =>
          Space.Fold(gs(s1, s2), gp(i1, i2), a1, y1, r1, gs(b1, b2), gp(u1, u2))
        case (Space.Wrap(s1, p1), Space.Wrap(s2, p2)) => Space.Wrap(gs(s1, s2), gp(p1, p2))
        case (Space.Unwrap(s1, p1), Space.Unwrap(s2, p2)) => Space.Unwrap(gs(s1, s2), gp(p1, p2))
        case (Space.TailsUnion(s1), Space.TailsUnion(s2)) => Space.TailsUnion(gs(s1, s2))
        case (Space.TailsIntersection(s1), Space.TailsIntersection(s2)) => Space.TailsIntersection(gs(s1, s2))
        case (Space.PrefixClosure(s1), Space.PrefixClosure(s2)) => Space.PrefixClosure(gs(s1, s2))
        case (Space.SuffixClosure(s1), Space.SuffixClosure(s2)) => Space.SuffixClosure(gs(s1, s2))
        case (Space.TailsClosure(s1), Space.TailsClosure(s2)) => Space.TailsClosure(gs(s1, s2))
        case (Space.GroundedPS(p1, f1), Space.GroundedPS(p2, f2)) if sameFn(f1, f2) => Space.GroundedPS(gp(p1, p2), f1)
        case (Space.GroundedSS(s1, f1), Space.GroundedSS(s2, f2)) if sameFn(f1, f2) => Space.GroundedSS(gs(s1, s2), f1)
        case (Space.Range(s1, start1, end1), Space.Range(s2, start2, end2)) if start1 == start2 && end1 == end2 =>
          Space.Range(gs(s1, s2), start1, end1)
        case _ => holeS(x, y)
    val sk = gs(a, b)
    Gen(
      sk,
      sholes.map { case ((l, _), h) => h -> l }.toMap,
      pholes.map { case ((l, _), h) => h -> l }.toMap,
      sholes.map { case ((_, r), h) => h -> r }.toMap,
      pholes.map { case ((_, r), h) => h -> r }.toMap
    )

case class SCEvent(kind: String, detail: String, depth: Int, before: Option[SpaceStats] = None, after: Option[SpaceStats] = None)

case class SCReport(events: Vector[SCEvent],
                    routines: Int,
                    residualStats: SpaceStats,
                    elapsedMs: Double = 0.0,
                    maxMillis: Long = CompileBudget.Default.maxMillis):
  def folds: Int = events.count(_.kind == "fold")
  def unfolds: Int = events.count(_.kind == "unfold")
  def whistles: Int = events.count(_.kind == "whistle")
  def generalizations: Int = events.count(_.kind == "generalize")
  def summary: String =
    f"events=${events.size} unfolds=$unfolds folds=$folds whistles=$whistles generalizations=$generalizations routines=$routines residual=${residualStats.compact} compile=$elapsedMs%.3f ms / budget $maxMillis ms"

case class Residual(top: Space, routines: Map[RoutinePtr, Routine], report: SCReport):
  def env: PartialFunction[RoutinePtr, Routine] = routines
  def show: String =
    val rs = routines.values.toVector.sortBy(_.name.s).map(_.show).mkString("\n")
    s"top: ${top.show}\n$rs"

case class SupercompiledProgram(top: Space,
                                routines: Map[RoutinePtr, Routine],
                                report: SCReport,
                                graph: Option[RecursiveOpGraph],
                                graphOptimization: Option[GraphOptimizeResult] = None):
  def env: PartialFunction[RoutinePtr, Routine] = routines
  def resultSize(
    assumptions: Map[SpaceMention, ResultSizeEstimate] = Map.empty
  ): ResultSizeEstimate = ResultSpaceSize.estimate(top, assumptions)

  def resultPathLength(
    assumptions: Map[SpaceMention, PathLengthEstimate] = Map.empty,
    pathAssumptions: Map[PathRef, PathLengthEstimate] = Map.empty,
    sizeAssumptions: Map[SpaceMention, ResultSizeEstimate] = Map.empty
  ): PathLengthEstimate =
    ResultPathLength.estimate(top, assumptions, pathAssumptions, sizeAssumptions)

  def spatialType(
    assumptions: SpatialAssumptions = SpatialAssumptions(),
    routineInputs: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
  ): SpatialType = SpatialTypeAnalysis.output(top, assumptions, routineInputs)

object SC:
  import Space.*
  import Matching.LiteralEmbeddingPolicy

  val simplifyRules: List[Space => Space] = Supercompiler.defaultSourcePasses.map(_._2).toList

  case class Config(
    maxNodes: Int = 2000,
    maxDepth: Int = 400,
    maxReductionRounds: Int = 128,
    maxMillis: Long = CompileBudget.Default.maxMillis,
    generalize: Boolean = true,
    literalEmbeddingPolicy: LiteralEmbeddingPolicy = LiteralEmbeddingPolicy.LeavesAsAtoms,
    buildGraph: Boolean = false
  )

  private case class NodeInfo(name: RoutinePtr, config: Space, refs: Vector[PathRef], mentions: Vector[SpaceMention])

  private final class State(defs: PartialFunction[RoutinePtr, Routine], cfg: Config):
    private var counter = 0
    private val deadline = CompileBudget(cfg.maxMillis).start()
    private val routinesB = mutable.LinkedHashMap.empty[RoutinePtr, Routine]
    private val eventsB = Vector.newBuilder[SCEvent]
    private val names = mutable.Set.empty[String]

    def routines: Map[RoutinePtr, Routine] = routinesB.toMap
    def events: Vector[SCEvent] = eventsB.result()
    def elapsedMs: Double = deadline.elapsedMs

    private def checkBudget(phase: String): Unit =
      deadline.check(s"process supercompiler $phase")

    def event(kind: String, detail: String, depth: Int, before: Option[Space] = None, after: Option[Space] = None): Unit =
      checkBudget(s"event $kind")
      eventsB += SCEvent(kind, detail, depth, before.map(Supercompiler.stats), after.map(Supercompiler.stats))

    def fresh(hint: String): RoutinePtr =
      checkBudget("fresh routine")
      var candidate = s"${hint}_sc$counter"
      while names(candidate) do
        counter += 1
        candidate = s"${hint}_sc$counter"
      counter += 1
      names += candidate
      RoutinePtr(candidate)

    def reduce(s: Space, depth: Int): Space =
      checkBudget("reduction")
      var current = s
      var round = 0
      var changed = true
      while changed && round < cfg.maxReductionRounds do
        checkBudget("reduction round")
        changed = false
        for rule <- simplifyRules do
          checkBudget("reduction pass")
          val next = rule(current)
          if next != current then
            event("reduce", rule.toString, depth, Some(current), Some(next))
            current = next
            changed = true
        round += 1
      if changed then throw RuntimeException(s"SC reduction cap ${cfg.maxReductionRounds} exceeded at ${s.show}")
      current

    def paramsOf(c: Space): (Vector[PathRef], Vector[SpaceMention]) =
      Matching.freeRefsV(c) -> Matching.freeMentionsV(c)

    def callOf(node: NodeInfo, sm: Map[SpaceMention, Space], pm: Map[PathRef, Path]): Space =
      Space.Call(
        node.name,
        node.refs.map(pr => pm.getOrElse(pr, Path.Deref(pr))),
        node.mentions.map(m => sm.getOrElse(m, Space.Mention(m)))
      )

    def unfold(c: Space.Call): Space =
      val r = defs(c.r)
      Matching.subst(r.body, (r.mentions zip c.mentions).toMap, (r.refs zip c.refs).toMap)

    def drive(s: Space, path: List[NodeInfo], depth: Int): Space =
      checkBudget("drive")
      if depth > cfg.maxDepth then throw RuntimeException(s"SC depth cap ${cfg.maxDepth} exceeded")
      val r = reduce(s, depth)
      subs(r)(spost = { case c: Space.Call if defs.isDefinedAt(c.r) => scCall(c, path, depth) })

    def scCall(c: Space.Call, path: List[NodeInfo], depth: Int): Space =
      checkBudget("call")
      if path.size > cfg.maxNodes then throw RuntimeException(s"SC node cap ${cfg.maxNodes} exceeded")

      path.iterator.flatMap { n =>
        checkBudget("fold search")
        Matching.instanceOf(n.config, c).map((n, _))
      }.toSeq.headOption match
        case Some((n, (sm, pm))) =>
          event("fold", s"${c.r.s} -> ${n.name.s}", depth, Some(c), None)
          callOf(n, sm, pm)
        case None =>
          val whistler =
            if cfg.generalize then path.collectFirst {
              case n if {
                checkBudget("whistle search")
                Matching.embeds(n.config, c, cfg.literalEmbeddingPolicy) && Matching.instanceOf(n.config, c).isEmpty
              } => n
            }
            else None
          whistler match
            case Some(n) =>
              event("whistle", s"${n.name.s} embeds ${c.r.s}", depth, Some(n.config), Some(c))
              generalize(n, c, path, depth)
            case None => makeNode(c, path, depth)

    def makeNode(c: Space.Call, path: List[NodeInfo], depth: Int): Space =
      checkBudget("make node")
      val (refs, mentions) = paramsOf(c)
      val name = fresh(c.r.s)
      val node = NodeInfo(name, c, refs, mentions)
      event("unfold", s"${c.r.s} -> ${name.s}", depth, Some(c), None)
      val body = drive(unfold(c), node :: path, depth + 1)
      routinesB(name) = Routine(name, refs, mentions, body)
      Space.Call(name, refs.map(Path.Deref(_)), mentions.map(Space.Mention(_)))

    def generalize(n: NodeInfo, c: Space.Call, path: List[NodeInfo], depth: Int): Space =
      checkBudget("generalize")
      val gen = Matching.msg(n.config, c)
      event("generalize", s"${n.name.s} with ${c.r.s}", depth, Some(c), Some(gen.skeleton))
      gen.skeleton match
        case sk: Space.Call if !Matching.alphaEqual(sk, c) =>
          val resid = scCall(sk, path, depth + 1)
          val drivenSm = gen.rsm.view.mapValues(v => drive(v, path, depth + 1)).toMap
          Matching.subst(resid, drivenSm, gen.rpm)
        case _ => makeNode(c, path, depth)

  def supercompile(conf: Space, defs: PartialFunction[RoutinePtr, Routine], cfg: Config = Config()): Residual =
    val st = new State(defs, cfg)
    val top = st.drive(conf, Nil, 0)
    val routines = st.routines
    val residualStats = routines.values.map(r => Supercompiler.stats(r.body)).foldLeft(Supercompiler.stats(top))(_ + _)
    Residual(top, routines, SCReport(st.events, routines.size, residualStats, st.elapsedMs, cfg.maxMillis))

  def supercompile(r: Routine, defs: PartialFunction[RoutinePtr, Routine], cfg: Config): Residual =
    val entry = Space.Call(r.name, r.refs.map(Path.Deref(_)), r.mentions.map(Space.Mention(_)))
    supercompile(entry, defs, cfg)

  def supercompile(r: Routine, defs: PartialFunction[RoutinePtr, Routine]): Residual =
    supercompile(r, defs, Config())

  def compileProgram(conf: Space, defs: PartialFunction[RoutinePtr, Routine], cfg: Config = Config(buildGraph = true)): SupercompiledProgram =
    val residual = supercompile(conf, defs, cfg)
    val graphOptimization =
      if cfg.buildGraph && Supercompiler.backendUnsupported(residual.top).isEmpty && residual.routines.isEmpty then
        Try(optimizeTimed(transpile(Routine(RoutinePtr("sc_top"), Vector.empty, Vector.empty, residual.top)), deadline = CompileBudget(cfg.maxMillis).start())).toOption
      else None
    SupercompiledProgram(residual.top, residual.routines, residual.report, graphOptimization.map(_.graph), graphOptimization)
