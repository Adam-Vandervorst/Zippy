package scala.collection.immutable

import morkl.{ITrie, EffortEvent, effort, effortN}

/** Native merges of the `IntMap[ITrie]` children maps that back [[morkl.ITrie]].  This object lives
 *  in `scala.collection.immutable` so it can see IntMap's package-private Patricia structure
 *  (`IntMap.Bin/Tip/Nil`) and smart constructors (`IntMapUtils.bin/join`), which lets the ring
 *  operations be single simultaneous descents over both tries — no per-key `get` + `updated`
 *  round-trips, and whole shared sub-tries skipped by pointer identity.
 *
 *  ==POINTER PRESERVATION IS THE CONTRACT==
 *
 *  Every merge here returns **the argument map object itself** whenever the merged map is the same
 *  map — not merely an equal one.  That is the whole mechanism behind the case-returning algebra in
 *  [[morkl.ITrie]]: `ITrie.unionR` concludes `Identity(LEFT)` from `merged eq a.children` and hands
 *  the caller `a` unchanged, so a node — and with it an arbitrarily large subspace — is accepted by
 *  pointer with zero allocation and zero further traversal.  Concretely:
 *
 *   - `unionTries(a,b) eq a` ⟺ (the code detects that) `b`'s keys are absorbed by `a`;
 *   - `intersectTries(a,b) eq a` ⟺ `a` is contained in `b`;  `eq b` ⟺ `b` is contained in `a`;
 *   - `diffTries(a,b) eq a` ⟺ `b` removes nothing from `a` (disjointness);
 *   - `restrictTries(x,p) eq x` ⟺ every `x` branch is kept.
 *
 *  Reconstruction therefore goes through [[bin1]]/[[binP]]/[[binD]] rather than `IntMap.Bin`
 *  directly: a `Bin` whose two recursive results came back by pointer rebuilds NOTHING.  The previous
 *  revision allocated a fresh `Bin` on every level of every descent even when the descent changed
 *  nothing, which destroyed identity propagation before it could reach the `ITrie` node above.
 *
 *  Each op still short-circuits on `eq` (identical sub-tries merge to themselves) — the common case
 *  under iteration/fixpoint, where most of one operand's structure is shared with the other.
 *
 *  INSTRUMENTED.  Each recursive entry counts one
 *  [[morkl.EffortEvent.PatriciaVisit]], which — together with `ITrie`'s own
 *  [[morkl.EffortEvent.TrieNodeVisit]] — is the ORACLE for `SpatialCost`'s `touch` component.  The
 *  bound the cost models rely on is the Patricia one: a Patricia tree over `k` keys has at most
 *  `2k-1` nodes, and a simultaneous descent visits at most the nodes of the two trees, so one merge
 *  of children maps of sizes `m` and `n` counts at most `2(m + n)` visits.  In addition,
 *  [[morkl.EffortEvent.PatriciaEntry]] counts single-key entry operations (`get`/`updated`/`- k` and
 *  the `Tip` arms) and [[morkl.EffortEvent.SubtrieAcceptedByPointer]] /
 *  [[morkl.EffortEvent.SubtrieRejectedByPointer]] count the whole-subspace decisions — a cost model
 *  cannot express "an entire left subspace was accepted by pointer" unless the oracle counts it.
 *  The hook is one static load and a not-taken branch while the sink is disarmed (`morkl.effort` is
 *  `inline`), and that cost is measured in `SpatialEventsCheck`, not asserted.
 *
 *  AND THE N-ARY OPERAND LOOPS ARE COUNTED TOO.  The `Patricia*` events above count the DESCENT; they
 *  say nothing about the `O(k)` loops [[joinAllTries]]/[[meetAllTries]] run over their live operands at
 *  every recursive call — the dedup, the branching-bit scan, the split, the result-identity search.
 *  Those emit [[morkl.EffortEvent.NaryOperandProbe]] (`Work`) and their scratch arrays emit
 *  [[morkl.EffortEvent.NaryScratchSlot]] (`Alloc`).  Counting them is what turned a `Θ(k²)` dedup from an
 *  invisible degeneracy into a measured number (the first P0), and `OptimalTrieCheck`'s ARITY
 *  LADDER is the gate that reads them. */
object IntTrieOps:
  import IntMapUtils.{hasMatch, zero, shorter, join}

  /** one recursive entry into a simultaneous two-sided descent */
  private inline def enter(): Unit = effort(EffortEvent.PatriciaVisit)
  /** one single-key Patricia entry operation (`get`, `updated`, `- k`, or a `Tip` arm) */
  private inline def entry(): Unit = effort(EffortEvent.PatriciaEntry)
  /** a whole map / branch became part of the result without being descended */
  private inline def took(): Unit = effort(EffortEvent.SubtrieAcceptedByPointer)
  /** a whole map / branch was discarded without being descended */
  private inline def dropped(): Unit = effort(EffortEvent.SubtrieRejectedByPointer)
  /** `n` operands examined by the per-call operand handling of an n-ary op (the first P0: this
   *  work emits none of the three events the "actual steps" oracle summed, so it was invisible) */
  private inline def probes(n: Int): Unit = effortN(EffortEvent.NaryOperandProbe, n.toLong)
  /** `n` reference SLOTS of scratch storage allocated by an n-ary op */
  private inline def scratch(n: Int): Unit = effortN(EffortEvent.NaryScratchSlot, n.toLong)

  // ---- n-ary operand collection: EXPECTED O(k) PER CALL ----------------------------------------

  /** THE DEDUP THRESHOLD.  A linear identity scan while the distinct count is at most this, a
   *  `java.util.IdentityHashMap` past it — the same strategy and the same threshold as
   *  `ITrie.liveDistinct` (IntTrie.scala).
   *
   *  WHY IT IS NEEDED HERE TOO (the first P0).  `ITrie.joinAll`/`meetAll` do dedup their
   *  operand LIST before handing the children maps down, so the ROOT array is already distinct — but
   *  the arrays the descent builds are not: two DISTINCT operands may hold the SAME child object under
   *  the branching bit, which is the common case under iteration and fixpoint (an unchanged branch of
   *  an iterate is the same object).  So there is no operand-uniqueness invariant to inherit below the
   *  root and the descent must re-dedup; what it must not do is re-dedup QUADRATICALLY.  The previous
   *  revision scanned the whole accumulated prefix unconditionally: `k(k-1)/2` identity comparisons at
   *  the root, and `Θ(k²)` again at every recursive call, while the scaladoc claimed `O(k)` a level. */
  private final val dedupScanMax = 24

  /** Fill `live` with the DISTINCT (by pointer) non-`null`, non-`Nil` entries of `ms` and return how
   *  many there are; return `-1` at the first `IntMap.Nil` when `stopOnNil` (a `Nil` operand
   *  annihilates a meet, and the caller must not descend).
   *
   *  Cost: at most `dedupScanMax` identity comparisons per operand while the distinct count is under
   *  the threshold, one expected-`O(1)` `IdentityHashMap` probe per operand above it — expected `O(k)`
   *  for the whole call, with the constant stated rather than hidden.  Union and intersection are
   *  idempotent, so dropping a repeated operand object changes nothing about WHAT is computed; it is
   *  the reason the same tail trie handed in `k` times costs one pass. */
  private def collectLive(ms: Array[IntMap[ITrie]], n: Int, live: Array[IntMap[ITrie]],
                          stopOnNil: Boolean): Int =
    var k = 0
    var i = 0
    var pr = 0                                        // operand probes, emitted once at the end
    var seen: java.util.IdentityHashMap[IntMap[ITrie], IntMap[ITrie]] = null
    var annihilated = false
    while i < n && !annihilated do
      val m = ms(i)
      if m eq null then ()
      else if m eq IntMap.Nil then { if stopOnNil then annihilated = true }
      else
        var dup = false
        if seen ne null then { pr += 1; dup = seen.put(m, m) ne null }
        else
          var j = 0
          while j < k && !dup do { if live(j) eq m then dup = true; j += 1 }
          pr += j
        if dup then took()
        else
          live(k) = m
          k += 1
          if (seen eq null) && k > dedupScanMax then
            seen = new java.util.IdentityHashMap[IntMap[ITrie], IntMap[ITrie]](2 * k)
            scratch(2 * (k + 1))                      // the map's interleaved key/value table
            var j = 0
            while j < k do { seen.put(live(j), live(j)); j += 1 }
            pr += k
      i += 1
    probes(pr)
    if annihilated then -1 else k

  // ---- pointer-preserving reconstruction -------------------------------------------------------

  /** `Bin` rebuilt only if a side actually changed; otherwise the ORIGINAL (left) map object. */
  private inline def bin1(orig: IntMap[ITrie], p: Int, m: Int,
                          l0: IntMap[ITrie], r0: IntMap[ITrie],
                          l: IntMap[ITrie], r: IntMap[ITrie]): IntMap[ITrie] =
    if (l eq l0) && (r eq r0) then orig else IntMap.Bin(p, m, l, r)

  /** the same for a PRUNING op: either original when unchanged, else a `Bin` that collapses when a
   *  side came back empty (mirrors `IntMapUtils.bin`, which cannot prune our `ITrie`-empty values —
   *  those are non-`Nil` IntMap entries we must never have built in the first place). */
  private inline def binP(a: IntMap[ITrie], b: IntMap[ITrie], p: Int, m: Int,
                          l1: IntMap[ITrie], r1: IntMap[ITrie], l2: IntMap[ITrie], r2: IntMap[ITrie],
                          l: IntMap[ITrie], r: IntMap[ITrie]): IntMap[ITrie] =
    if (l eq l1) && (r eq r1) then a
    else if (l eq l2) && (r eq r2) then b
    else if l eq IntMap.Nil then r
    else if r eq IntMap.Nil then l
    else IntMap.Bin(p, m, l, r)

  /** the same for a one-sided pruning op (difference / raffination): only the LEFT map can be the
   *  result, because `a ∖ b == b` forces both to be empty (see `ITrie.AlgebraicResult`). */
  private inline def binD(a: IntMap[ITrie], p: Int, m: Int,
                          l0: IntMap[ITrie], r0: IntMap[ITrie],
                          l: IntMap[ITrie], r: IntMap[ITrie]): IntMap[ITrie] =
    if (l eq l0) && (r eq r0) then a
    else if l eq IntMap.Nil then r
    else if r eq IntMap.Nil then l
    else IntMap.Bin(p, m, l, r)

  // ---- union: keep every key; combine the two sides where a key is in both -------------------

  /** `insert-with-union` that preserves `m` by pointer when the inserted value is absorbed. */
  private def insUnion(m: IntMap[ITrie], k: Int, v: ITrie, vLeft: Boolean): IntMap[ITrie] =
    entry()
    m.get(k) match
      case Some(w) =>
        val u = if vLeft then ITrie.union(v, w) else ITrie.union(w, v)
        if u eq w then m else m.updated(k, u)
      case None => took(); m.updated(k, v)

  def unionTries(a: IntMap[ITrie], b: IntMap[ITrie]): IntMap[ITrie] =
    enter()
    if a eq b then a
    else a match
      case IntMap.Nil => took(); b
      case IntMap.Tip(k1, v1) => b match
        case IntMap.Nil => took(); a
        case IntMap.Tip(k2, v2) =>
          entry()
          if k1 == k2 then
            val u = ITrie.union(v1, v2)
            if u eq v1 then a else if u eq v2 then b else IntMap.Tip(k1, u)
          else { took(); took(); join(k1, a, k2, b) }
        case _ => insUnion(b, k1, v1, true)
      case IntMap.Bin(p1, m1, l1, r1) => b match
        case IntMap.Nil => took(); a
        case IntMap.Tip(k2, v2) => insUnion(a, k2, v2, false)
        case IntMap.Bin(p2, m2, l2, r2) =>
          if shorter(m1, m2) then
            if !hasMatch(p2, p1, m1) then { took(); took(); join(p1, a, p2, b) }
            else if zero(p2, m1) then bin1(a, p1, m1, l1, r1, unionTries(l1, b), r1)
            else bin1(a, p1, m1, l1, r1, l1, unionTries(r1, b))
          else if shorter(m2, m1) then
            if !hasMatch(p1, p2, m2) then { took(); took(); join(p1, a, p2, b) }
            else if zero(p1, m2) then bin1(b, p2, m2, l2, r2, unionTries(a, l2), r2)
            else bin1(b, p2, m2, l2, r2, l2, unionTries(a, r2))
          else if p1 == p2 then
            val l = unionTries(l1, l2)
            val r = unionTries(r1, r2)
            if (l eq l1) && (r eq r1) then a
            else if (l eq l2) && (r eq r2) then b
            else IntMap.Bin(p1, m1, l, r)
          else { took(); took(); join(p1, a, p2, b) }

  // ---- n-ary union: one simultaneous descent over k maps ---------------------------------------

  /** representative key of a map: a `Tip`'s key, a `Bin`'s prefix (bits ≤ mask cleared) */
  private def repKey(m: IntMap[ITrie]): Int = m match
    case IntMap.Tip(k, _) => k
    case IntMap.Bin(p, _, _, _) => p
    case _ => 0
  /** a map's own branching bit; `0` for a `Tip`/`Nil`, which branch nowhere */
  private def maskOf(m: IntMap[ITrie]): Int = m match
    case IntMap.Bin(_, mm, _, _) => mm
    case _ => 0
  /** `IntMapUtils.mask`: `i` with every bit up to and including `m` cleared */
  private inline def prefixOf(i: Int, m: Int): Int = i & (~(m - 1) ^ m)

  /** **THE N-ARY SIMULTANEOUS UNION.**  `ITrie.joinAll`'s previous children-map step grouped the
   *  children of all `k` operands into a `LongMap` of buffers and then rebuilt the result map key by
   *  key with `updated`.  That is `Θ(Σᵢ fan(mᵢ))` **whatever the operands look like** — and the
   *  pairwise Patricia union it replaced answers the decisive case in `O(1)`: two maps whose key
   *  ranges do not interleave are joined at the top by [[join]] without either being descended.  So on
   *  a `TailsUnion`/`Iteration` over few WIDE groups the n-ary pass was asymptotically WORSE than the
   *  fold it was introduced to beat — linear in the operand keys where the merge is constant.  The
   *  reverse case is just as real: `k` operands that all share one deep spine cost the fold `Θ(k·d)`
   *  intermediate nodes, one per operand per level, where an n-ary pass builds `d`.
   *
   *  This descends all `k` maps at once and keeps both wins:
   *
   *   - a branch in which exactly ONE operand is live is the result of that branch — returned BY
   *     POINTER, in constant time, however many keys it holds (the `k == 1` arm below);
   *   - `k == 2` delegates to [[unionTries]], the proven pairwise descent;
   *   - otherwise the operands are split at `br`, the HIGHEST bit at which their prefixes differ or
   *     any of them branches, so each level does `O(k)` work and the recursion follows the union of
   *     the `k` Patricia trees rather than their key sets;
   *   - where every live operand is a `Tip` on the same key, the values are combined by one n-ary
   *     `ITrie.joinAll` rather than `k-1` pairwise unions with an intermediate node each;
   *   - reconstruction is pointer-preserving throughout: if the merged sides are exactly some
   *     operand's own sides, that operand's map object is the answer, so `ITrie.joinAll` can conclude
   *     `Identity` and hand back a whole subspace with zero allocation.
   *
   *  Operands are identity-deduplicated as they are collected — union is idempotent and the same tail
   *  trie is handed in repeatedly under iteration and fixpoint — by [[collectLive]], in expected
   *  `O(k)`, so a LEVEL really costs `O(k)` as claimed and not `Θ(k²)`. */
  def joinAllTries(ms: Array[IntMap[ITrie]]): IntMap[ITrie] = joinAllTries(ms, ms.length)

  /** the same over the FIRST `n` entries of `ms`.  The recursion uses this rather than
   *  `java.util.Arrays.copyOf`: the split arrays are already exactly what the child call needs to read,
   *  and copying them cost two extra scratch arrays PER RECURSIVE CALL — `Θ(k)` slots each, the
   *  unbounded-in-arity allocation `EffortComponent.Alloc` had no event for. */
  def joinAllTries(ms: Array[IntMap[ITrie]], n: Int): IntMap[ITrie] =
    enter()
    val live = new Array[IntMap[ITrie]](n)
    scratch(n)
    val k = collectLive(ms, n, live, stopOnNil = false)
    var i = 0
    if k == 0 then IntMap.Nil
    else if k == 1 then { took(); live(0) }
    else if k == 2 then unionTries(live(0), live(1))
    else
      val rep = repKey(live(0))
      var acc = 0
      i = 0
      while i < k do { acc |= (repKey(live(i)) ^ rep) | maskOf(live(i)); i += 1 }
      probes(k)                                        // the branching-bit scan
      val br = java.lang.Integer.highestOneBit(acc)
      if br == 0 then
        // every live operand is a Tip on the SAME key: one n-ary join of the values
        val vs = new Array[ITrie](k)
        scratch(k)
        i = 0
        while i < k do { vs(i) = (live(i): @unchecked) match { case IntMap.Tip(_, v) => v }; i += 1 }
        probes(k)
        val u = ITrie.joinAll(ArraySeq.unsafeWrapArray(vs))
        var res: IntMap[ITrie] = null
        i = 0
        while i < k && (res eq null) do { if u eq vs(i) then res = live(i); i += 1 }
        probes(i)                                      // however far the identity search got
        if res ne null then res else IntMap.Tip(rep, u)
      else
        val ls = new Array[IntMap[ITrie]](k)
        val rs = new Array[IntMap[ITrie]](k)
        scratch(2 * k)
        var nl = 0
        var nr = 0
        i = 0
        while i < k do
          live(i) match
            case IntMap.Bin(_, mm, l0, r0) if mm == br =>
              ls(nl) = l0; nl += 1; rs(nr) = r0; nr += 1
            case t =>
              if (repKey(t) & br) == 0 then { ls(nl) = t; nl += 1 } else { rs(nr) = t; nr += 1 }
          i += 1
        probes(k)                                      // the split
        val l = joinAllTries(ls, nl)
        val r = joinAllTries(rs, nr)
        var res: IntMap[ITrie] = null
        i = 0
        while i < k && (res eq null) do
          live(i) match
            case IntMap.Bin(_, mm, l0, r0) if mm == br && (l eq l0) && (r eq r0) => res = live(i)
            case _ => ()
          i += 1
        probes(i)
        if res ne null then res
        else if l eq IntMap.Nil then r
        else if r eq IntMap.Nil then l
        else IntMap.Bin(prefixOf(rep, br), br, l, r)

  // ---- intersection: only keys in both, combined; drop sub-results that come out empty --------

  def intersectTries(a: IntMap[ITrie], b: IntMap[ITrie]): IntMap[ITrie] =
    enter()
    if a eq b then a
    else a match
      case IntMap.Nil => dropped(); IntMap.Nil
      case IntMap.Tip(k1, v1) => b match
        case IntMap.Nil => dropped(); IntMap.Nil
        case IntMap.Tip(k2, v2) =>
          entry()
          if k1 != k2 then { dropped(); dropped(); IntMap.Nil }
          else
            val r = ITrie.intersection(v1, v2)
            if r.isEmpty then IntMap.Nil else if r eq v1 then a else if r eq v2 then b else IntMap.Tip(k1, r)
        case _ =>
          entry()
          b.get(k1) match
            case Some(w) =>
              val r = ITrie.intersection(v1, w)
              if r.isEmpty then IntMap.Nil else if r eq v1 then a else IntMap.Tip(k1, r)
            case None => dropped(); IntMap.Nil
      case IntMap.Bin(p1, m1, l1, r1) => b match
        case IntMap.Nil => dropped(); IntMap.Nil
        case IntMap.Tip(k2, w2) =>
          entry()
          a.get(k2) match
            case Some(v) =>
              val r = ITrie.intersection(v, w2)
              if r.isEmpty then IntMap.Nil else if r eq w2 then b else IntMap.Tip(k2, r)
            case None => dropped(); IntMap.Nil
        case IntMap.Bin(p2, m2, l2, r2) =>
          if shorter(m1, m2) then
            if !hasMatch(p2, p1, m1) then { dropped(); IntMap.Nil }
            else if zero(p2, m1) then { dropped(); intersectTries(l1, b) } else { dropped(); intersectTries(r1, b) }
          else if shorter(m2, m1) then
            if !hasMatch(p1, p2, m2) then { dropped(); IntMap.Nil }
            else if zero(p1, m2) then { dropped(); intersectTries(a, l2) } else { dropped(); intersectTries(a, r2) }
          else if p1 == p2 then
            binP(a, b, p1, m1, l1, r1, l2, r2, intersectTries(l1, l2), intersectTries(r1, r2))
          else { dropped(); dropped(); IntMap.Nil }

  // ---- n-ary intersection: one simultaneous descent over k maps --------------------------------

  /** **THE N-ARY SIMULTANEOUS INTERSECTION.**  A key survives only if EVERY operand has it, so the
   *  descent must follow the smallest frontier AT EVERY LEVEL — not the smallest operand chosen once.
   *  `ITrie.meetAll`'s previous children step got that right by iterating the smallest node's keys and
   *  probing the other `k-1` maps, but it paid `Θ(fan)` probes to do it, so a meet of two 1024-head
   *  nodes whose key ranges do not interleave cost 1024 probes where a Patricia comparison rejects the
   *  pair at the top.  A pairwise fold has the opposite failure: it walks the first two operands' shared
   *  structure in full before the small third operand ever gets to prune it (`OptimalTrieCheck`'s
   *  before/after gate is exactly that shape and it is why a fold is not the fix).
   *
   *  This descends all `k` maps at once and keeps both properties:
   *
   *   - an operand that lives entirely on ONE side of the current branching bit FORCES the descent into
   *     that side: the other side is missing from it, so it is rejected in constant time however large
   *     the other operands are there.  That is "follow the smallest branch at every level", derived
   *     from the Patricia structure instead of from a fanout comparison;
   *   - two operands on OPPOSITE sides means disjoint key regions and the whole meet is empty;
   *   - `k == 2` delegates to [[intersectTries]], the proven pairwise descent;
   *   - reconstruction is pointer-preserving, so a meet that returns one operand unchanged lets
   *     `ITrie.meetAll` conclude `Identity` and hand back a whole subspace with zero allocation;
   *   - operands are identity-deduplicated by [[collectLive]] in expected `O(k)` per call (a repeated
   *     operand object is free: intersection is idempotent), so a LEVEL costs `O(k)`, not `Θ(k²)`. */
  def meetAllTries(ms: Array[IntMap[ITrie]]): IntMap[ITrie] = meetAllTries(ms, ms.length)

  /** the same over the FIRST `n` entries of `ms` — see the two-argument `joinAllTries` above for why the
   *  recursion passes a length instead of copying. */
  def meetAllTries(ms: Array[IntMap[ITrie]], n: Int): IntMap[ITrie] =
    enter()
    val live = new Array[IntMap[ITrie]](n)
    scratch(n)
    val k = collectLive(ms, n, live, stopOnNil = true)   // expected O(k), see collectLive
    var i = 0
    if k < 0 then { dropped(); IntMap.Nil }
    else if k == 0 then IntMap.Nil
    else if k == 1 then { took(); live(0) }
    else if k == 2 then intersectTries(live(0), live(1))
    else
      val rep = repKey(live(0))
      var acc = 0
      i = 0
      while i < k do { acc |= (repKey(live(i)) ^ rep) | maskOf(live(i)); i += 1 }
      probes(k)                                        // the branching-bit scan
      val br = java.lang.Integer.highestOneBit(acc)
      if br == 0 then
        // every live operand is a Tip on the SAME key: one n-ary meet of the values
        val vs = new Array[ITrie](k)
        scratch(k)
        i = 0
        while i < k do { vs(i) = (live(i): @unchecked) match { case IntMap.Tip(_, v) => v }; i += 1 }
        probes(k)
        val r = ITrie.meetAll(ArraySeq.unsafeWrapArray(vs))
        if r.isEmpty then IntMap.Nil
        else
          var res: IntMap[ITrie] = null
          i = 0
          while i < k && (res eq null) do { if r eq vs(i) then res = live(i); i += 1 }
          probes(i)
          if res ne null then res else IntMap.Tip(rep, r)
      else
        val ls = new Array[IntMap[ITrie]](k)
        val rs = new Array[IntMap[ITrie]](k)
        scratch(2 * k)
        var nl = 0
        var nr = 0
        var forcedL = false
        var forcedR = false
        i = 0
        while i < k do
          live(i) match
            case IntMap.Bin(_, mm, l0, r0) if mm == br =>
              ls(nl) = l0; nl += 1; rs(nr) = r0; nr += 1
            case t =>
              if (repKey(t) & br) == 0 then { ls(nl) = t; nl += 1; forcedL = true }
              else { rs(nr) = t; nr += 1; forcedR = true }
          i += 1
        probes(k)                                      // the split
        if forcedL && forcedR then { dropped(); dropped(); IntMap.Nil }   // disjoint key regions
        else if forcedL then { dropped(); meetAllTries(ls, nl) }
        else if forcedR then { dropped(); meetAllTries(rs, nr) }
        else
          val l = meetAllTries(ls, nl)
          val r = meetAllTries(rs, nr)
          var res: IntMap[ITrie] = null
          i = 0
          while i < k && (res eq null) do
            live(i) match
              case IntMap.Bin(_, mm, l0, r0) if mm == br && (l eq l0) && (r eq r0) => res = live(i)
              case _ => ()
            i += 1
          probes(i)
          if res ne null then res
          else if l eq IntMap.Nil then r
          else if r eq IntMap.Nil then l
          else IntMap.Bin(prefixOf(rep, br), br, l, r)

  // ---- restriction: keys of `x` that also appear in `prefixes`, recursively restricted; drop empties.
  //      (called only when `prefixes` is NOT terminal — the terminal "keep the whole subtree" case is
  //      handled by ITrie.restrictionR before descent, and IS the constant-time accept.) ------------

  def restrictTries(x: IntMap[ITrie], p: IntMap[ITrie]): IntMap[ITrie] =
    enter()
    x match
      case IntMap.Nil => dropped(); IntMap.Nil
      case IntMap.Tip(k1, v1) => p match
        case IntMap.Nil => dropped(); IntMap.Nil
        case IntMap.Tip(k2, w2) =>
          entry()
          if k1 != k2 then { dropped(); dropped(); IntMap.Nil }
          else
            val r = ITrie.restriction(v1, w2)
            if r.isEmpty then IntMap.Nil else if r eq v1 then x else if r eq w2 then p else IntMap.Tip(k1, r)
        case _ =>
          entry()
          p.get(k1) match
            case Some(w) =>
              val r = ITrie.restriction(v1, w)
              if r.isEmpty then IntMap.Nil else if r eq v1 then x else IntMap.Tip(k1, r)
            case None => dropped(); IntMap.Nil
      case IntMap.Bin(p1, m1, l1, r1) => p match
        case IntMap.Nil => dropped(); IntMap.Nil
        case IntMap.Tip(k2, w2) =>
          entry()
          x.get(k2) match
            case Some(v) =>
              val r = ITrie.restriction(v, w2)
              if r.isEmpty then IntMap.Nil else if r eq w2 then p else IntMap.Tip(k2, r)
            case None => dropped(); IntMap.Nil
        case IntMap.Bin(p2, m2, l2, r2) =>
          if shorter(m1, m2) then
            if !hasMatch(p2, p1, m1) then { dropped(); IntMap.Nil }
            else if zero(p2, m1) then { dropped(); restrictTries(l1, p) } else { dropped(); restrictTries(r1, p) }
          else if shorter(m2, m1) then
            if !hasMatch(p1, p2, m2) then { dropped(); IntMap.Nil }
            else if zero(p1, m2) then { dropped(); restrictTries(x, l2) } else { dropped(); restrictTries(x, r2) }
          else if p1 == p2 then
            binP(x, p, p1, m1, l1, r1, l2, r2, restrictTries(l1, l2), restrictTries(r1, r2))
          else { dropped(); dropped(); IntMap.Nil }

  // ---- difference: keys of `a`, minus (per matching key) what `b` removes; drop empties --------

  def diffTries(a: IntMap[ITrie], b: IntMap[ITrie]): IntMap[ITrie] =
    enter()
    if a eq b then IntMap.Nil
    else a match
      case IntMap.Nil => IntMap.Nil
      case IntMap.Tip(k1, v1) => b match
        case IntMap.Nil => took(); a
        case _ =>
          entry()
          b.get(k1) match
            case Some(w) =>
              val r = ITrie.subtraction(v1, w)
              if r.isEmpty then IntMap.Nil else if r eq v1 then a else IntMap.Tip(k1, r)
            case None => took(); a
      case IntMap.Bin(p1, m1, l1, r1) => b match
        case IntMap.Nil => took(); a
        case IntMap.Tip(k2, w2) =>
          entry()
          a.get(k2) match
            case Some(v) =>
              val r = ITrie.subtraction(v, w2)
              if r.isEmpty then a - k2 else if r eq v then a else a.updated(k2, r)
            case None => took(); a
        case IntMap.Bin(p2, m2, l2, r2) =>
          if shorter(m1, m2) then
            if !hasMatch(p2, p1, m1) then { took(); a }
            else if zero(p2, m1) then binD(a, p1, m1, l1, r1, diffTries(l1, b), r1)
            else binD(a, p1, m1, l1, r1, l1, diffTries(r1, b))
          else if shorter(m2, m1) then
            if !hasMatch(p1, p2, m2) then { took(); a }
            else if zero(p1, m2) then { dropped(); diffTries(a, l2) } else { dropped(); diffTries(a, r2) }
          else if p1 == p2 then binD(a, p1, m1, l1, r1, diffTries(l1, l2), diffTries(r1, r2))
          else { took(); a }

  // ---- raffination: the FUSED `x ∖ (x <| y)` ------------------
  //      Structurally difference, but the per-key combiner is `ITrie.raffination` rather than
  //      `ITrie.subtraction`, so `x` is walked ONCE.  Called only when `y` is not terminal (an
  //      `ε ∈ y` annihilates all of `x`, decided in ITrie.raffinationR before descent).

  def raffTries(x: IntMap[ITrie], y: IntMap[ITrie]): IntMap[ITrie] =
    enter()
    if x eq y then IntMap.Nil
    else x match
      case IntMap.Nil => IntMap.Nil
      case IntMap.Tip(k1, v1) => y match
        case IntMap.Nil => took(); x
        case _ =>
          entry()
          y.get(k1) match
            case Some(w) =>
              val r = ITrie.raffination(v1, w)
              if r.isEmpty then IntMap.Nil else if r eq v1 then x else IntMap.Tip(k1, r)
            case None => took(); x
      case IntMap.Bin(p1, m1, l1, r1) => y match
        case IntMap.Nil => took(); x
        case IntMap.Tip(k2, w2) =>
          entry()
          x.get(k2) match
            case Some(v) =>
              val r = ITrie.raffination(v, w2)
              if r.isEmpty then x - k2 else if r eq v then x else x.updated(k2, r)
            case None => took(); x
        case IntMap.Bin(p2, m2, l2, r2) =>
          if shorter(m1, m2) then
            if !hasMatch(p2, p1, m1) then { took(); x }
            else if zero(p2, m1) then binD(x, p1, m1, l1, r1, raffTries(l1, y), r1)
            else binD(x, p1, m1, l1, r1, l1, raffTries(r1, y))
          else if shorter(m2, m1) then
            if !hasMatch(p1, p2, m2) then { took(); x }
            else if zero(p1, m2) then { dropped(); raffTries(x, l2) } else { dropped(); raffTries(x, r2) }
          else if p1 == p2 then binD(x, p1, m1, l1, r1, raffTries(l1, l2), raffTries(r1, r2))
          else { took(); x }
