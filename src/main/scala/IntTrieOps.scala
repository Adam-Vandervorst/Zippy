package scala.collection.immutable

import morkl.ITrie

/** Native merges of the `IntMap[ITrie]` children maps that back [[morkl.ITrie]].  This object lives
 *  in `scala.collection.immutable` so it can see IntMap's package-private Patricia structure
 *  (`IntMap.Bin/Tip/Nil`) and smart constructors (`IntMapUtils.bin/join`), which lets the ring
 *  operations be single simultaneous descents over both tries — no per-key `get` + `updated`
 *  round-trips, and whole shared sub-tries skipped by pointer identity.
 *
 *  Each op short-circuits on `eq` (identical sub-tries merge to themselves) — the common case under
 *  iteration/fixpoint, where most of one operand's structure is shared with the other. */
object IntTrieOps:
  import IntMapUtils.{hasMatch, zero, shorter, join}

  // ---- union: keep every key; combine the two sides where a key is in both -------------------
  def unionTries(a: IntMap[ITrie], b: IntMap[ITrie]): IntMap[ITrie] = (a, b) match
    case _ if a eq b => a
    case (IntMap.Nil, _) => b
    case (_, IntMap.Nil) => a
    case (IntMap.Tip(k, v), _) => b.updateWith(k, v, (x, y) => ITrie.union(x, y))
    case (_, IntMap.Tip(k, v)) => a.updateWith(k, v, (x, y) => ITrie.union(y, x))
    case (IntMap.Bin(p1, m1, l1, r1), IntMap.Bin(p2, m2, l2, r2)) =>
      if shorter(m1, m2) then
        if !hasMatch(p2, p1, m1) then join(p1, a, p2, b)
        else if zero(p2, m1) then IntMap.Bin(p1, m1, unionTries(l1, b), r1)
        else IntMap.Bin(p1, m1, l1, unionTries(r1, b))
      else if shorter(m2, m1) then
        if !hasMatch(p1, p2, m2) then join(p1, a, p2, b)
        else if zero(p1, m2) then IntMap.Bin(p2, m2, unionTries(a, l2), r2)
        else IntMap.Bin(p2, m2, l2, unionTries(a, r2))
      else if p1 == p2 then IntMap.Bin(p1, m1, unionTries(l1, l2), unionTries(r1, r2))
      else join(p1, a, p2, b)

  // ---- intersection: only keys in both, combined; drop sub-results that come out empty --------
  def intersectTries(a: IntMap[ITrie], b: IntMap[ITrie]): IntMap[ITrie] = (a, b) match
    case _ if a eq b => a
    case (IntMap.Nil, _) | (_, IntMap.Nil) => IntMap.Nil
    case (IntMap.Tip(k, v), _) => b.get(k) match
      case Some(w) => keep(k, ITrie.intersection(v, w)); case None => IntMap.Nil
    case (_, IntMap.Tip(k, w)) => a.get(k) match
      case Some(v) => keep(k, ITrie.intersection(v, w)); case None => IntMap.Nil
    case (IntMap.Bin(p1, m1, l1, r1), IntMap.Bin(p2, m2, l2, r2)) =>
      if shorter(m1, m2) then
        if !hasMatch(p2, p1, m1) then IntMap.Nil
        else if zero(p2, m1) then intersectTries(l1, b) else intersectTries(r1, b)
      else if shorter(m2, m1) then
        if !hasMatch(p1, p2, m2) then IntMap.Nil
        else if zero(p1, m2) then intersectTries(a, l2) else intersectTries(a, r2)
      else if p1 == p2 then binPrune(p1, m1, intersectTries(l1, l2), intersectTries(r1, r2))
      else IntMap.Nil

  // ---- restriction: keys of `x` that also appear in `prefixes`, recursively restricted; drop empties.
  //      (called only when `prefixes` is NOT terminal — the terminal "keep whole subtree" case is
  //      handled by ITrie.restriction before descent.) ------------------------------------------
  def restrictTries(x: IntMap[ITrie], p: IntMap[ITrie]): IntMap[ITrie] = (x, p) match
    case (IntMap.Nil, _) | (_, IntMap.Nil) => IntMap.Nil
    case (IntMap.Tip(k, v), _) => p.get(k) match
      case Some(w) => keep(k, ITrie.restriction(v, w)); case None => IntMap.Nil
    case (_, IntMap.Tip(k, w)) => x.get(k) match
      case Some(v) => keep(k, ITrie.restriction(v, w)); case None => IntMap.Nil
    case (IntMap.Bin(p1, m1, l1, r1), IntMap.Bin(p2, m2, l2, r2)) =>
      if shorter(m1, m2) then
        if !hasMatch(p2, p1, m1) then IntMap.Nil
        else if zero(p2, m1) then restrictTries(l1, p) else restrictTries(r1, p)
      else if shorter(m2, m1) then
        if !hasMatch(p1, p2, m2) then IntMap.Nil
        else if zero(p1, m2) then restrictTries(x, l2) else restrictTries(x, r2)
      else if p1 == p2 then binPrune(p1, m1, restrictTries(l1, l2), restrictTries(r1, r2))
      else IntMap.Nil

  // ---- difference: keys of `a`, minus (per matching key) what `b` removes; drop empties --------
  def diffTries(a: IntMap[ITrie], b: IntMap[ITrie]): IntMap[ITrie] = (a, b) match
    case _ if a eq b => IntMap.Nil
    case (IntMap.Nil, _) => IntMap.Nil
    case (_, IntMap.Nil) => a
    case (IntMap.Tip(k, v), _) => b.get(k) match
      case Some(w) => keep(k, ITrie.subtraction(v, w)); case None => a
    case (_, IntMap.Tip(k, w)) => a.get(k) match
      case Some(v) => val r = ITrie.subtraction(v, w); if r.isEmpty then a - k else a.updated(k, r)
      case None => a
    case (IntMap.Bin(p1, m1, l1, r1), IntMap.Bin(p2, m2, l2, r2)) =>
      if shorter(m1, m2) then
        if !hasMatch(p2, p1, m1) then a
        else if zero(p2, m1) then binPrune(p1, m1, diffTries(l1, b), r1)
        else binPrune(p1, m1, l1, diffTries(r1, b))
      else if shorter(m2, m1) then
        if !hasMatch(p1, p2, m2) then a
        else if zero(p1, m2) then diffTries(a, l2) else diffTries(a, r2)
      else if p1 == p2 then binPrune(p1, m1, diffTries(l1, l2), diffTries(r1, r2))
      else a

  /** a Tip if `v` is non-empty, else Nil — the leaf smart constructor for the prunable ops */
  private inline def keep(k: Int, v: ITrie): IntMap[ITrie] = if v.isEmpty then IntMap.Nil else IntMap.Tip(k, v)
  /** Bin that collapses when a side is Nil (mirrors IntMapUtils.bin, which we cannot rely on to
   *  prune our ITrie-empty values — those are non-Nil IntMap entries we must never have built). */
  private inline def binPrune(p: Int, m: Int, l: IntMap[ITrie], r: IntMap[ITrie]): IntMap[ITrie] =
    if r eq IntMap.Nil then l else if l eq IntMap.Nil then r else IntMap.Bin(p, m, l, r)
