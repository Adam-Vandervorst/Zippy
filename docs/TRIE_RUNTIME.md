# Trie Runtime For MORKL Spaces

`SpaceValue(Set[PathValue])` remains the reference semantics. It is simple,
generic, and excellent for tests, but most MORKL operators are naturally trie
operators. The optimized runtime in `src/main/scala/TrieSpace.scala` adds an
ordered immutable trie keyed by `PathItem`, conversions to and from
`SpaceValue`, a zipper-like cursor, and a direct `evalTrie` evaluator.

## Ordering

`PathItemOrder` gives every `PathItem` a deterministic order.  `PathItem` is
now an opaque alias over `String`, so the order is the unit path-set order:

1. compare item strings lexicographically;
2. compare paths item-by-item;
3. put a strict prefix before its extension.

This keeps trie traversal deterministic and makes ordered `Range` agree with
the reference evaluator's sorted path order.

## Native Operations

The runtime implements the native space operations directly on the trie:

- `union` / `joinAll`;
- `intersect` / `meetAll`;
- `diff`;
- `restrictBy`;
- `raffinate`;
- `concat`;
- `wrap` / `unwrap`;
- `tailsUnion`;
- `tailsIntersection`;
- ordered `Range` / first / last slices;
- first-symbol `Iteration`;
- ordered `Fold`.

Grounded host callbacks (`GroundedPS`, `GroundedSS`, `GroundedPP`, `GroundedSP`)
remain semantic boundaries. The trie evaluator converts the focused trie back to
`SpaceValue` before calling host Scala code, then re-trieifies the result.
Benchmarks show this boundary clearly: native path-algebra programs speed up;
grounded-heavy programs can slow down.

## Algebraic Results And Structural Reuse

Every Boolean trie operation computes an `AlgebraicResult` recursively, not
only at the root. `Identity` contains a bit mask naming every argument equal to
the result, `Bespoke` carries a newly built trie, and `Empty` records why the
result vanished. The ordinary `union`, `intersect`, `diff`, and `restrictBy`
methods unwrap this result while returning an input object directly whenever an
identity bit is present.

The exhaustive binary cases are:

- Union is a left, right, or both identity; bespoke; or empty because both
  arguments were empty.
- Intersection is a left, right, or both identity; bespoke; empty because an
  argument was empty; or empty because two non-empty arguments were disjoint.
- Subtraction is a left identity when the right side is empty or merely
  disjoint; bespoke after removing a proper non-empty overlap; empty because
  the left side was empty; or empty because the right side covered it. A
  subtraction cannot equal a non-empty right argument: membership in the right
  side is exactly what subtraction excludes.
- Restriction additionally returns `allPrefixesMatched`. A left identity means
  no source path was dropped. A right-only identity means the kept paths equal
  the prefixes and some source paths were dropped. A bespoke result with every
  prefix matched is a superset in the prefix order (every right path has an
  equal or longer kept left path); a bespoke result with that flag false has
  unused prefixes as well as dropped source paths. Empty results distinguish
  both-empty, left-empty, right-empty, and non-empty/no-match inputs.

This metadata is computed inside `TrieIntMapOps`, alongside the existing
Patricia `Tip`/`Bin` descent. A parent node combines child identity masks and
terminal bits, so a containment result can reuse the complete smaller or larger
argument without an equality re-traversal or a generic key-set scan.

Every persistent Patricia node also has a weak identity-keyed aggregate
summary. More importantly, `TrieIntMapOps.updated`, `removed`, algebraic
`Tip`/`Bin` builders, and shape-preserving value maps propagate the summary
while allocating the Patricia spine. One operation-local identity table holds
intermediate summaries. At the operation boundary, summaries for persistent
Patricia branches are promoted to the weak cross-operation cache; dead versions
remain only weakly reachable, and maps of at most eight entries are recomputed
directly as a bounded O(1) scan. This matters for incremental union: the next
update can recover every unchanged sibling summary in O(1) instead of rescanning
the accumulator. Algebra therefore hands
`TrieSpace.nodeFromChildren` an already summarized child map. Rewrapping a wide
structurally shared result is O(1); it does not scan the result width or retain
all temporary maps.

Patricia visits are measured separately from semantic trie-node visits. This is
necessary because width alone is not a complexity law. For two W-wide maps,
the current exact union gates include identity (zero Patricia visits),
root-disjoint (one), quarter-interwoven (`W/2 + 1`), and fully interwoven
(`2W - 1`). All four allocate at most one `TrieSpace` parent. The work follows
the actually touched Patricia branches, with no width-based surrogate.

## Join-All And Meet-All

`joinAll` identity-deduplicates operands, then reduces distinct tries in a
balanced union tree. Sparse/disjoint Patricia branches are grafted whole,
whereas genuinely interwoven branches pay for their touched structure. K
references to one trie cost O(K) identity checks and no trie descent; they do
not become K traversals of the referenced depth.

`meetAll` is the non-trivial operation. A naive implementation would enumerate
paths from one trie and check membership in all others, which is acceptable as a
reference but loses the trie structure. The native implementation:

1. materializes the operand list once;
2. chooses the root with the smallest child/node/path profile as the driver;
3. recurses only on child keys present in every operand;
4. sets the terminal bit only when every operand is terminal at that focus;
5. prunes empty children.

That makes `TailsIntersection` cheap for trie-shaped universal queries: it
becomes `meetAll(children.values)` rather than `groupMap(...).reduce(_ intersect
_)` over materialized suffix sets.

## Persistent Construction

Single-path insertion is a one-branch persistent update. Each parent derives
`pathCount`, `nodeCount`, and `childCount` from the replaced child's old and new
aggregates and uses the constant-time `nodeKnown` constructor. It never rescans
the completed sibling map. Consequently a flat `k`-head relation no longer pays
the previous quadratic aggregate-maintenance cost.

Bulk `fromPaths`/`fromEncodedPaths` construction uses a mutable builder followed
by one immutable freeze. Only final trie/Patricia nodes are allocated and
summarized; transient persistent versions are not produced. Incremental
`insertItems` is iterative over the path and rebuilds its saved frames
bottom-up, avoiding recursion depth and retaining O(D) path work.

The scanning `node` constructor remains for genuinely bulk results whose full
child map is new. Algebraic `binaryValue` only selects provenance and does not
rebuild; concrete zipper insertion routes through the same delta update.
`TrieConstructionAsymptoticTest` certifies these claims with exact
scan/allocation counters, while
`trieConstructionAsymptoticBenchmark` records wall-clock scaling.

Composition preserves the left child-map topology. It transforms child values
in place structurally, constructs one descendant parent, and unions the right
operand only at a left node which is both terminal and branching. The common
prefix-free case therefore visits the left trie once, shares the complete right
operand, and allocates only rebuilt internal left nodes.

## Closure, Cursor, And Range Layers

A sole path's suffix language is built as a minimal acyclic suffix automaton.
The suffix-link accepting chain recognizes exactly the non-empty suffixes, and
the automaton DAG is used directly as a `TrieSpace`. Repeated, periodic, and
non-periodic paths all construct in O(D) time and allocations. General
multi-path closure uses identity-deduplicated balanced unions; the zipper layer
caches one reachable-graph closure summary containing every head frontier and
the all-tail frontier.

Read cursors retain their current focus and ancestor stack, so descending D
items is O(D). Zipper frames retain the original parent aggregates and rebuild
with one child delta per ancestor. Ordered sibling arrays and indices are
created once per frame and reused for O(1) adjacent movement.

Ordered range nodes cache children and cumulative path ranks. Concrete slices
binary-search the first overlapping rank. Virtual ranges extend a shared rank
frontier monotonically, while last/drop-last projections do the analogous work
from the right. Independently queried children no longer restart at a range
edge.

Virtual `PatchChild` is a one-key overlay until enumeration is requested; a
concrete parent/replacement pair updates the underlying `IntMap` and aggregate
counts immediately. Path concatenation is flattened into one iterative builder,
iterator contexts use persistent-map updates, and binder-dependency and
left-associated-intersection flattening are cached/iterative.

## PathMap Influence

The supplied `PathMap-master.zip` is a Rust pathmap implementation with DAG
sharing, read/write zippers, prefix/product/overlay zippers, and algebraic trie
operations. This Scala runtime does not copy the Rust implementation or FFI into
it. Instead it mirrors the relevant API ideas in a small form suitable for this
Scala codebase:

- `TrieSpace.Cursor` is a read zipper over a `TrieSpace` root and prefix focus.
- `Cursor.down`, `up`, `descend`, and `subtree` are enough to express focused
  prefix descent without reparsing path sets.
- `wrap` corresponds to PathMap's `PrefixZipper` idea.
- `concat` corresponds to a materialized `ProductZipper` result.
- `union` is the materialized form of an overlay/join zipper.

The next serious backend step is to compile `RecursiveOpGraph` nodes into
zipper loops rather than materializing every intermediate `TrieSpace`. The
current module takes the first step with `execTrie`, a `RecursiveOpGraph`
executor whose space stack slots are `TrieSpace` values. It runs supported graph
nodes with native trie operations and handles iteration subgraphs by iterating
over child subtries directly.

## Correctness

`TrieSpaceTest` compares trie operations and `evalTrie` against the reference
`eval` on:

- round-trip conversion, including epsilon;
- set and prefix operators;
- `TailsIntersection` / meet-all;
- cursor descent;
- arbitrary binary interval cover generation;
- Aunt query;
- recursive semi-naive Datalog;
- grounded Game of Life;
- process-supercompiled residual programs.
- `RecursiveOpGraph` execution over `TrieSpace`, including Aunt query,
  transformation, closures, and range graph nodes.

The benchmark harness also checks equality before timing every row.

## Runtime Evidence

See `TRIE_BENCHMARKS.md`. The headline result is mixed but informative:

- large prefix-heavy and recursive path-algebra workloads improve strongly;
- small residual programs can be slower because the reference set is already
  tiny;
- grounded-heavy workloads still pay conversion costs and need native kernels or
  zipper-level graph execution to improve.
