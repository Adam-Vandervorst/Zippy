import morkl.TrieSpace

object TrieIntMapOps:
  import IntMapUtils.{hasMatch, join, shorter, zero}

  def unionTries(a: IntMap[TrieSpace], b: IntMap[TrieSpace]): IntMap[TrieSpace] = (a, b) match
    case _ if a eq b => a
    case (IntMap.Nil, _) => b
    case (_, IntMap.Nil) => a
    case (IntMap.Tip(k, v), _) =>
      b.get(k) match
        case Some(w) => b.updated(k, v.union(w))
        case None => b.updated(k, v)
    case (_, IntMap.Tip(k, v)) =>
      a.get(k) match
        case Some(w) => a.updated(k, w.union(v))
        case None => a.updated(k, v)
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

  def intersectTries(a: IntMap[TrieSpace], b: IntMap[TrieSpace]): IntMap[TrieSpace] = (a, b) match
    case _ if a eq b => a
    case (IntMap.Nil, _) | (_, IntMap.Nil) => IntMap.Nil
    case (IntMap.Tip(k, v), _) =>
      b.get(k).fold(IntMap.Nil)(w => keep(k, v.intersect(w)))
    case (_, IntMap.Tip(k, w)) =>
      a.get(k).fold(IntMap.Nil)(v => keep(k, v.intersect(w)))
    case (IntMap.Bin(p1, m1, l1, r1), IntMap.Bin(p2, m2, l2, r2)) =>
      if shorter(m1, m2) then
        if !hasMatch(p2, p1, m1) then IntMap.Nil
        else if zero(p2, m1) then intersectTries(l1, b) else intersectTries(r1, b)
      else if shorter(m2, m1) then
        if !hasMatch(p1, p2, m2) then IntMap.Nil
        else if zero(p1, m2) then intersectTries(a, l2) else intersectTries(a, r2)
      else if p1 == p2 then binPrune(p1, m1, intersectTries(l1, l2), intersectTries(r1, r2))
      else IntMap.Nil

  def diffTries(a: IntMap[TrieSpace], b: IntMap[TrieSpace]): IntMap[TrieSpace] = (a, b) match
    case _ if a eq b => IntMap.Nil
    case (IntMap.Nil, _) => IntMap.Nil
    case (_, IntMap.Nil) => a
    case (IntMap.Tip(k, v), _) =>
      b.get(k).fold(a)(w => keep(k, v.diff(w)))
    case (_, IntMap.Tip(k, w)) =>
      a.get(k) match
        case None => a
        case Some(v) =>
          val next = v.diff(w)
          if next.isEmpty then a - k else a.updated(k, next)
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

  def restrictTries(x: IntMap[TrieSpace], p: IntMap[TrieSpace]): IntMap[TrieSpace] = (x, p) match
    case (IntMap.Nil, _) | (_, IntMap.Nil) => IntMap.Nil
    case (IntMap.Tip(k, v), _) =>
      p.get(k).fold(IntMap.Nil)(w => keep(k, v.restrictBy(w)))
    case (_, IntMap.Tip(k, w)) =>
      x.get(k).fold(IntMap.Nil)(v => keep(k, v.restrictBy(w)))
    case (IntMap.Bin(p1, m1, l1, r1), IntMap.Bin(p2, m2, l2, r2)) =>
      if shorter(m1, m2) then
        if !hasMatch(p2, p1, m1) then IntMap.Nil
        else if zero(p2, m1) then restrictTries(l1, p) else restrictTries(r1, p)
      else if shorter(m2, m1) then
        if !hasMatch(p1, p2, m2) then IntMap.Nil
        else if zero(p1, m2) then restrictTries(x, l2) else restrictTries(x, r2)
      else if p1 == p2 then binPrune(p1, m1, restrictTries(l1, l2), restrictTries(r1, r2))
      else IntMap.Nil

  private inline def keep(k: Int, v: TrieSpace): IntMap[TrieSpace] =
    if v.isEmpty then IntMap.Nil else IntMap.Tip(k, v)

  private inline def binPrune(p: Int, m: Int, l: IntMap[TrieSpace], r: IntMap[TrieSpace]): IntMap[TrieSpace] =
    if r eq IntMap.Nil then l
    else if l eq IntMap.Nil then r
    else IntMap.Bin(p, m, l, r)
