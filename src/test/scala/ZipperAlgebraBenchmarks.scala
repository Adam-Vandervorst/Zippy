package morkl

import morkl.Syntax.{*, given}

import java.nio.file.{Files, Paths}
import scala.collection.immutable.IntMap
import scala.collection.mutable

object ZipperAlgebraBenchmarks:
  import Space.*

  private val BucketCount = 1500
  private val SubtreePaths = 16
  private val BorderRange = 512
  private val EqualityPathLimit = 250_000
  private val TimingSamples = 7
  private val TimingTargetBatchNanos = 10_000_000L
  private val TimingMaximumBatchRuns = 4096

  private case class Scenario(label: String,
                              targetSharedPct: Int,
                              sharedBuckets: Int,
                              a: TrieSpace,
                              b: TrieSpace,
                              cOverlap: TrieSpace,
                              prefixes: TrieSpace,
                              exact: TrieSpace,
                              productExact: TrieSpace,
                              productPrefixSelector: TrieSpace,
                              wrappedA: TrieSpace,
                              wrapPrefix: List[Int],
                              actualSharedPct: Double)

  private case class BenchCase(group: String,
                               name: String,
                               expr: Space,
                               runs: Int = 1,
                               note: String = "")

  private case class Row(share: String,
                         group: String,
                         name: String,
                         resultPaths: Int,
                         resultNodes: Int,
                         trieMs: Double,
                         zipperMs: Double,
                         ratio: Double,
                         note: String)

  private def item(name: String): Int =
    TrieSpace.interner.intern(PathItem(name))

  private def path(ids: List[Int]): Path =
    Path.Constant(TrieSpace.decode(ids))

  private val commonRoot = item("zipper.algebra.common")
  private val commonLeaves = Vector.tabulate(4)(i => item(s"zipper.algebra.common.$i"))

  private def subtree(tag: String): (TrieSpace, Vector[List[Int]]) =
    val common = commonLeaves.map(leaf => List(commonRoot, leaf))
    val unique =
      for
        group <- 0 until 3
        leaf <- 0 until 4
      yield List(item(s"$tag.g$group"), item(s"$tag.l$leaf"))
    val paths = (common ++ unique).toVector
    TrieSpace.fromEncodedPaths(paths) -> paths

  private def singletonTrie(p: List[Int]): TrieSpace =
    TrieSpace.empty.insertItems(p)

  private def scenario(targetSharedPct: Int): Scenario =
    val sharedBuckets = ((BucketCount.toDouble * targetSharedPct / 100.0).round.toInt).max(1).min(BucketCount)
    val bucketIds = Vector.tabulate(BucketCount)(i => item(f"zipper.algebra.bucket.$i%05d"))
    val sharedSubtrees = Vector.tabulate(sharedBuckets)(i => subtree(s"zipper.algebra.shared.$targetSharedPct.$i"))

    val aChildren = Vector.newBuilder[(Int, TrieSpace)]
    val bChildren = Vector.newBuilder[(Int, TrieSpace)]
    val cChildren = Vector.newBuilder[(Int, TrieSpace)]
    val aSamplePaths = Vector.newBuilder[List[Int]]
    val bSamplePaths = Vector.newBuilder[List[Int]]

    var i = 0
    while i < BucketCount do
      val bucket = bucketIds(i)
      val (aChild, aPaths, bChild, bPaths, cChild) =
        if i < sharedBuckets then
          val (child, paths) = sharedSubtrees(i)
          (child, paths, child, paths, Some(child))
        else
          val (ac, ap) = subtree(s"zipper.algebra.a.$targetSharedPct.$i")
          val (bc, bp) = subtree(s"zipper.algebra.b.$targetSharedPct.$i")
          (ac, ap, bc, bp, None)

      aChildren += bucket -> aChild
      bChildren += bucket -> bChild
      cChild.foreach(child => cChildren += bucket -> child)
      aSamplePaths += bucket :: aPaths.head
      bSamplePaths += bucket :: bPaths.head
      i += 1

    val a = TrieSpace.node(terminal = false, IntMap.from(aChildren.result()))
    val b = TrieSpace.node(terminal = false, IntMap.from(bChildren.result()))
    val cOverlap = TrieSpace.node(terminal = false, IntMap.from(cChildren.result()))

    val prefixBuckets =
      (0 until BucketCount by (BucketCount / 96).max(1)).take(96).map(bucketIds).toVector
    val prefixes = TrieSpace.fromEncodedPaths(prefixBuckets.map(List(_)))

    val sharedProbeIndex = (sharedBuckets / 2).min(sharedBuckets - 1)
    val exactPath = aSamplePaths.result()(sharedProbeIndex)
    val productPath = exactPath ++ bSamplePaths.result()(sharedProbeIndex)
    val wrapPrefix = List(item(s"zipper.algebra.wrap.$targetSharedPct"))

    val subtreeNodes = sharedSubtrees.head._1.nodeCount
    val physicallySharedNodes = sharedBuckets * subtreeNodes
    val comparableNodes = a.nodeCount.min(b.nodeCount).max(1)
    val actualSharedPct = physicallySharedNodes.toDouble * 100.0 / comparableNodes.toDouble

    Scenario(
      label = s"$targetSharedPct%",
      targetSharedPct = targetSharedPct,
      sharedBuckets = sharedBuckets,
      a = a,
      b = b,
      cOverlap = cOverlap,
      prefixes = prefixes,
      exact = singletonTrie(exactPath),
      productExact = singletonTrie(productPath),
      productPrefixSelector = singletonTrie(exactPath),
      wrappedA = a.wrapItems(wrapPrefix),
      wrapPrefix = wrapPrefix,
      actualSharedPct = actualSharedPct
    )

  private def context(s: Scenario): (TrieSpaceContextMap, ZipperSpaceContextMap) =
    val trie = TrieSpaceContextMap(Map(
      SpaceMention("a") -> s.a,
      SpaceMention("b") -> s.b,
      SpaceMention("cOverlap") -> s.cOverlap,
      SpaceMention("prefixes") -> s.prefixes,
      SpaceMention("exact") -> s.exact,
      SpaceMention("productExact") -> s.productExact,
      SpaceMention("productPrefix") -> s.productPrefixSelector,
      SpaceMention("wrappedA") -> s.wrappedA
    ))
    trie -> ZipperSpaceContext.fromTrie(trie)

  private def cases(s: Scenario): Vector[BenchCase] =
    val wrapPath = path(s.wrapPrefix)
    Vector(
      BenchCase("binary", "union", S"a" \/ S"b", note = "merge two aligned huge tries"),
      BenchCase("binary", "intersection", S"a" /\ S"b", note = "walk only common child keys"),
      BenchCase("binary", "subtraction", S"a" \ S"b", note = "left-guided traversal"),
      BenchCase("binary", "restriction", S"a" <| S"prefixes", note = "top-level prefix filter"),
      BenchCase("binary", "raffination", S"a" \| S"prefixes", note = "complement of the prefix filter"),
      BenchCase("binary", "composition", S"a" x S"b", note = "no selective consumer; full product is materialized"),
      BenchCase("n-ary", "three-way intersection", (S"a" /\ S"b") /\ S"cOverlap", note = "evalZ flattens nested intersections and starts from the sparse overlap operand"),
      BenchCase("unary", "wrap", Space.Wrap(S"a", wrapPath), note = "virtual prefix node"),
      BenchCase("unary", "unwrap", Space.Unwrap(S"wrappedA", wrapPath), note = "descend through virtual prefix"),
      BenchCase("unary", "tails-union", Space.TailsUnion(S"a"), note = "join every first-level tail"),
      BenchCase("unary", "tails-intersection", Space.TailsIntersection(S"a"), note = "meet every first-level tail"),
      BenchCase("unary", "prefix-closure", Space.PrefixClosure(S"a"), note = "all non-empty prefixes"),
      BenchCase("unary", "suffix-closure", Space.SuffixClosure(S"a"), note = "all non-empty suffixes"),
      BenchCase("unary", "tails-closure", Space.TailsClosure(S"a"), note = "epsilon plus suffix closure"),
      BenchCase("range", s"first($BorderRange)", Space.Range(S"a", 0, BorderRange), note = "ordered border slice"),
      BenchCase("range", s"last($BorderRange)", Space.Range(S"a", -BorderRange, 0), note = "ordered border slice"),
      BenchCase("combination", "union then exact intersection", (S"a" \/ S"b") /\ S"exact", note = "selective consumer over a virtual union"),
      BenchCase("combination", "diff then restriction", (S"a" \ S"b") <| S"prefixes", note = "left-guided diff under prefix filter"),
      BenchCase("combination", "product exact intersection", (S"a" x S"b") /\ S"productExact", note = "selector should avoid the full product"),
      BenchCase("combination", "product prefix restriction", (S"a" x S"b") <| S"productPrefix", note = "one product row selected by prefix"),
      BenchCase("combination", "tails of restricted union", Space.TailsUnion((S"a" \/ S"b") <| S"prefixes"), note = "join tails after a logical prefix filter"),
      BenchCase("combination", "range of union", Space.Range(S"a" \/ S"b", 0, BorderRange), note = "border slice over a virtual union")
    )

  /** Warm, adaptively batch, and report the median per-invocation time.  The
    * calibration target keeps timer/scheduler noise from dominating cheap
    * virtual operations, while the hard batch cap and seven samples bound the
    * cost of the full checked matrix.
    */
  private def adaptiveMedianTimed[A](minimumBatchRuns: Int)(f: => A): (A, Double) =
    require(TimingSamples > 0 && TimingSamples % 2 == 1)

    def batch(runs: Int): (A, Long) =
      val start = System.nanoTime()
      var last: A = f
      var index = 1
      while index < runs do
        last = f
        index += 1
      last -> (System.nanoTime() - start)

    var last: A = f // untimed warmup after the independent correctness check
    var batchRuns = minimumBatchRuns.max(1).min(TimingMaximumBatchRuns)
    var calibration = batch(batchRuns)
    last = calibration._1
    while calibration._2 < TimingTargetBatchNanos && batchRuns < TimingMaximumBatchRuns do
      batchRuns = (batchRuns * 2).min(TimingMaximumBatchRuns)
      calibration = batch(batchRuns)
      last = calibration._1

    val samples = Vector.tabulate(TimingSamples) { _ =>
      val measured = batch(batchRuns)
      last = measured._1
      measured._2.toDouble / 1_000_000.0 / batchRuns.toDouble
    }.sorted
    last -> samples(TimingSamples / 2)

  private def sampleEquivalent(trie: TrieSpace, zipper: TrieSpace, name: String): Unit =
    assert(trie.pathCount == zipper.pathCount, s"$name path count mismatch: ${trie.pathCount} vs ${zipper.pathCount}")
    if trie.pathCount <= EqualityPathLimit then
      assert(trie == zipper, s"$name evalTrie/evalZ mismatch")
    else
      val samples =
        (trie.first(12).encodedPaths ++ trie.last(12).encodedPaths ++
          zipper.first(12).encodedPaths ++ zipper.last(12).encodedPaths).distinct
      samples.foreach { p =>
        assert(trie.containsItems(p) == zipper.containsItems(p), s"$name sampled membership mismatch at ${TrieSpace.decode(p).show}")
      }

  private def row(s: Scenario, c: BenchCase): Row =
    Console.err.println(s"[zipper-algebra] share=${s.label} ${c.group}/${c.name}")
    given PathContext = PathContext.emptyMap
    val (tc, zc) = context(s)

    val trieCheck = evalTrie(c.expr)(using summon[PathContext], tc, PartialFunction.empty)
    val zipperCheck = evalZ(c.expr)(using summon[PathContext], zc, PartialFunction.empty)
    sampleEquivalent(trieCheck, zipperCheck, s"${s.label} ${c.group}/${c.name}")

    val (_, trieMs) = adaptiveMedianTimed(c.runs)(
      evalTrie(c.expr)(using summon[PathContext], tc, PartialFunction.empty).pathCount)
    val (zipperResultPaths, zipperMs) = adaptiveMedianTimed(c.runs)(
      evalZ(c.expr)(using summon[PathContext], zc, PartialFunction.empty).pathCount)
    assert(zipperResultPaths == trieCheck.pathCount)

    Row(
      share = s.label,
      group = c.group,
      name = c.name,
      resultPaths = trieCheck.pathCount,
      resultNodes = trieCheck.nodeCount,
      trieMs = trieMs,
      zipperMs = zipperMs,
      ratio = trieMs / zipperMs,
      note = c.note
    )

  private def scenarioSummary(scenarios: Vector[Scenario]): String =
    val body = scenarios.map { s =>
      f"| ${s.label} | ${s.sharedBuckets}%,d / $BucketCount%,d | ${s.actualSharedPct}%.2f%% | ${s.a.pathCount}%,d | ${s.a.nodeCount}%,d | ${s.cOverlap.pathCount}%,d | ${s.prefixes.pathCount}%,d |"
    }.mkString("\n")
    Vector(
      "| target shared nodes | shared top-level subtries | measured shared nodes / operand nodes | `a`/`b` paths | `a`/`b` trie nodes | sparse third paths | prefix paths |",
      "|---:|---:|---:|---:|---:|---:|---:|",
      body
    ).mkString("\n")

  def markdown(): String =
    val scenarios = Vector(1, 50, 90).map(scenario)
    val rows = scenarios.flatMap(s => cases(s).map(row(s, _)))
    val table = rows.map { r =>
      f"| ${r.share} | ${r.group} | ${r.name} | ${r.resultPaths}%,d | ${r.resultNodes}%,d | ${r.trieMs}%.3f | ${r.zipperMs}%.3f | ${r.ratio}%.2f x | ${r.note} |"
    }.mkString("\n")

    Vector(
      "# Zipper Algebra Sharing Benchmarks",
      "",
      "This report isolates direct zipper evaluation over physically large tries. Each scenario builds two full operands `a` and `b` with the same top-level keys, plus a sparse third operand `cOverlap` containing only the buckets that are physically shared by all three. For the requested sharing level, the corresponding child subtries are the same JVM objects in all overlapping operands; the rest of `a` and `b` have the same outer shape but distinct unique leaves. Each child subtrie also has a small common tail vocabulary so `tailsIntersection` and ordinary intersections have non-empty work to do outside the physically shared portion.",
      "",
      s"Each operand has $BucketCount top-level buckets and $SubtreePaths paths per bucket. Timings compare `evalTrie(expr).pathCount` to `evalZ(expr).pathCount` after an untimed correctness check and warmup. Each backend is adaptively batched by doubling from one invocation until a batch reaches 10 ms or 4,096 invocations, then the table reports the median per-invocation time from seven batches. This bounds total measurement work while preventing one noisy invocation from defining a row. Very large results are checked by path count plus border membership samples instead of decoding every path.",
      "",
      scenarioSummary(scenarios),
      "",
      "| share | group | operation | result paths | result trie nodes | evalTrie ms | evalZ ms | evalTrie / evalZ | note |",
      "|---:|---|---|---:|---:|---:|---:|---:|---|",
      table,
      "",
      "Ratios above `1.00 x` mean the zipper evaluator is faster. Direct `composition` intentionally has no selective consumer, so it is a useful overhead baseline rather than the expected zipper win. Selective product rows exercise composition without forcing the full product before the final materialization boundary."
    ).mkString("\n")

  private case class IterRangeTailMicroRow(heads: Int,
                                          tailFanout: Int,
                                          resultPaths: Int,
                                          oldMs: Double,
                                          newMs: Double):
    def speedup: Double = oldMs / newMs

  private def iterRangeTailTrie(heads: Int, tailFanout: Int): TrieSpace =
    val paths =
      Vector.tabulate(heads, tailFanout) { (head, tail) =>
        List(
          item(f"zipper.iter.range.head.$head%05d"),
          item(f"zipper.iter.range.tail.$head%05d.$tail%03d")
        )
      }.flatten
    TrieSpace.fromEncodedPaths(paths)

  private def oldRangeTailPathCount(src: SpaceZipper, start: Int, end: Int): Int =
    val branchKeys = src.childKeys.iterator.filter(src.hasChild).toVector
    def branch(head: Int): SpaceZipper =
      SpaceZipper.range(src.child(head), start, end)

    val terminal = branchKeys.exists(head => branch(head).terminal)
    val keys = mutable.LinkedHashSet.empty[Int]
    branchKeys.foreach { head =>
      keys ++= branch(head).childKeys.iterator
    }

    val children = keys.iterator.map { item =>
      SpaceZipper.joinAll(branchKeys.iterator.map(head => branch(head).child(item)))
    }.filterNot(_.isEmpty)

    (if terminal then 1 else 0) + children.map(_.pathCount).sum

  private def newRangeTailPathCount(src: SpaceZipper, start: Int, end: Int): Int =
    SpaceZipper
      .iteration(
        src,
        (_head, tail) => SpaceZipper.range(tail, start, end),
        Some(SpaceZipper.IterTemplateTag.RangeTail(start, end))
      )
      .pathCount

  /** Retain the historical mean protocol for the separate old-vs-new
    * RangeTail microbenchmark. The checked algebra matrix above is the scope
    * of the adaptive median methodology.
    */
  private def microTimed[A](runs: Int)(f: => A): (A, Double) =
    var last: A = f
    val actualRuns = runs.max(1)
    val start = System.nanoTime()
    var index = 0
    while index < actualRuns do
      last = f
      index += 1
    last -> ((System.nanoTime() - start).toDouble / 1_000_000.0 / actualRuns.toDouble)

  private def iterRangeTailMicroRow(heads: Int, tailFanout: Int): IterRangeTailMicroRow =
    Console.err.println(s"[iter-range-tail-micro] heads=$heads tailFanout=$tailFanout")
    val src = SpaceZipper.traversal(iterRangeTailTrie(heads, tailFanout))
    val expectedPaths = heads * (tailFanout - 1)
    assert(newRangeTailPathCount(src, 0, -1) == expectedPaths)
    assert(oldRangeTailPathCount(src, 0, -1) == expectedPaths)

    val runs = if heads >= 150 then 2 else 4
    val (_, oldMs) = microTimed(runs)(oldRangeTailPathCount(src, 0, -1))
    val (_, newMs) = microTimed(runs)(newRangeTailPathCount(src, 0, -1))
    IterRangeTailMicroRow(heads, tailFanout, expectedPaths, oldMs, newMs)

  def iterRangeTailMicroMarkdown(): String =
    val rows = Vector(
      iterRangeTailMicroRow(heads = 32, tailFanout = 12),
      iterRangeTailMicroRow(heads = 96, tailFanout = 16),
      iterRangeTailMicroRow(heads = 192, tailFanout = 16)
    )
    val body = rows.map { r =>
      f"| ${r.heads}%,d | ${r.tailFanout}%,d | ${r.resultPaths}%,d | ${r.oldMs}%.3f | ${r.newMs}%.3f | ${r.speedup}%.2f x |"
    }.mkString("\n")

    Vector(
      "# Iter Range-Tail Zipper Microbenchmark",
      "",
      "This isolates `SpaceZipper.Iteration(..., RangeTail(0, -1))`, the path used by range-tail iteration over child zippers. The old model first collected all output keys, then recomputed each key by scanning every source head again. The current implementation accumulates per-key children in the first branch traversal and joins them once.",
      "",
      "| source heads | tail fanout | result paths | old emulation ms | current ms | old / current |",
      "|---:|---:|---:|---:|---:|---:|",
      body
    ).mkString("\n")

@main def zipperAlgebraBenchmarkReport(): Unit =
  val report = ZipperAlgebraBenchmarks.markdown()
  Files.writeString(Paths.get("docs/ZIPPER_ALGEBRA_BENCHMARKS.md"), report + "\n")
  println(report)

@main def zipperIterRangeTailMicroReport(): Unit =
  val report = ZipperAlgebraBenchmarks.iterRangeTailMicroMarkdown()
  Files.writeString(Paths.get("docs/ZIPPER_ITER_RANGE_MICRO.md"), report + "\n")
  println(report)
