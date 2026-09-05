# The operational resource semantics

This document fixes **the unit, the inclusion rule and the sharing convention**
of each of `Work`, `Alloc`, `Touch` and `Rounds`, and the one semantics every backend and the
counted oracle are held to.  The semantics itself is executable — `EventSemantics` in
[SpatialSemantics.scala](../src/main/scala/SpatialSemantics.scala) — and it is held to the
instrumented executors by [SpatialSemanticsCheck](../src/test/scala/SpatialSemanticsCheck.scala):
same event **multiset**, every constructor, every backend, over empty, singleton, aliased,
disjoint, deeply shared, recursive and n-ary operands, the fuzzer corpus and the six cornerstones.

## 1. Three layers

| layer | object | what it fixes |
|---|---|---|
| event algebra | `EventKind` | the backend-independent kinds: `NodeVisit`, `OperandProbe`, `Alloc`, `RetainedShare`, `KeyComparison`, `Materialize`, `Round`, `Handoff`; every `EffortEvent` has exactly one kind |
| backend profile | `SemanticsProfile` | which concrete event a kind is emitted as by which executable, the representation the rules are stated over, and the one platform parameter |
| event semantics | `EventSemantics.{reference,trie,graph,zipper}` | for every certified `Space` constructor and every backend, the events of one execution as a function of the operands' concrete structure |

A backend difference is a **different profile** — a different dispatch event, an entry event, a
representation — never a different semantics.  The three trie-shaped backends share one set of
trie rules (`TrieSpec`); the graph and zipper rules add only their own dispatch, frames and cursor
reads on top of it.

## 2. Units and inclusion

| component | unit | includes (kinds) | events |
|---|---|---|---|
| `Work` | one elementary step of the executable itself | `NodeVisit` (dispatches, cursor reads, algebra entries), `OperandProbe`, `KeyComparison`, `Materialize` | `AstDispatch`, `PathDispatch`, `TrieDispatch`, `TriePathDispatch`, `GraphNodeDispatch`, `ZipperBuild`, `TrieOpEntry`, `ZipperCursorRead`, `ZipperMaterializeNode`, `NaryOperandProbe`, `PathItemComparison` |
| `Alloc` | one fresh object: a `PathValue`, an `ITrie` node, a frame, one reference slot of n-ary scratch | `Alloc` | `FreshPath`, `FreshTrieNode`, `FreshNode`, `GraphFrameAllocation`, `NaryScratchSlot` |
| `Touch` | one node examined **inside** the trie algebra | `NodeVisit` restricted to the descent | `TrieNodeVisit`, `PatriciaVisit` |
| `Rounds` | one dynamic frame | `Round` | `LoopBodyEntry`, `FixpointRound` (the terminating round included), `CallEntry` |

`Explain` events (`AlgebraEmpty`, `AlgebraIdentityLeft/Right`, `AlgebraBespoke`,
`SubtrieAcceptedByPointer`, `SubtrieRejectedByPointer`, `ReusedSpace`, `ReusedSubtrie`,
`PatriciaEntry`, `EqualityFrontierVisit`, `ZipperFallbackToEvalI`) are **counted and specified** but
summed into no component: they explain which work was avoided or handed off.  `EventKind.inclusion`
is the machine-readable form of this table and `SpatialSemanticsCheck` checks that every event's kind
is in its component's inclusion set.

**Why `Touch` is not all of `NodeVisit`.**  `Touch` is the executor-independent descent cost of the
representation — what a fused cursor would also pay if it descended — while dispatches and cursor
reads are the executable's own overhead.  Keeping them apart is what lets `execZ` be cheaper in
`Touch` and dearer in `Work` on the same value, which the counted runs show.

## 3. The sharing convention

`Alloc` counts **fresh** objects.  A node is fresh when a rule builds it (the semantics' `fresh`,
IntTrie.scala's one allocation site `node`) and not fresh when the result **is** an operand object
or a sub-object of one.  The result of every ring operation is therefore relative to its operands —
`Empty`, the left operand by pointer, the right operand by pointer, or a fresh node — and the
`RetainedShare` events count exactly those decisions:

* `AlgebraIdentityLeft/Right` + `SubtrieAcceptedByPointer` — the whole result is an operand;
* `SubtrieAcceptedByPointer` alone — a branch present on one side only was attached unvisited, or a
  single live operand was returned (`k == 1`), or a `Range` child lies entirely inside the window;
* `SubtrieRejectedByPointer` — a branch was discarded without descent (a Patricia prefix mismatch, a
  missing key in a meet, a `Range` child outside the window);
* `ReusedSubtrie` — the two operands **are the same object** (`a eq b`): decided at the top, no
  descent; `ReusedSpace` is the zipper-level twin.

Aliasing is observable and part of the semantics: the same object handed in twice to an n-ary
operation is **one** operand (identity deduplication, one probe per position, no second traversal).

## 4. The n-ary operand discipline

Every n-ary operation — `joinAll`/`meetAll`, hence `Iteration`, `TailsUnion`, `TailsIntersection`,
and the Patricia `joinAllTries`/`meetAllTries` beneath them — is specified over its **ordered live
frontier**: the operands in the order the executable sees them (a child map's key order), an
operand **retired** when it is empty (`dropEmpty` on a join, `stopOnNil` annihilating a meet at the
first empty operand: the probe count is how far the scan got), **revisited** when the split passes
it down unchanged (a map whose own branching bit is below the split bit is re-listed at the next
level and probed again there), **aliased** when two positions hold one object (deduplicated: a
linear identity scan up to 24 distinct operands, an identity hash map past it — both counted as
`NaryOperandProbe`, the map's table as `NaryScratchSlot`), and **reused** when the result is an
operand (the result-identity search costs one probe per operand examined).  Each of those is a rule
with its own event, not a fallback model.

## 5. Per-constructor rules (the executable form is authoritative)

Reference (`eval`, sets of paths): one `AstDispatch` per `Space` node visited — a loop body once per
head group, a fixpoint body once per round, a callee body per call, and the synthetic nodes `Wrap`
and `Raffination` desugar to; one `PathDispatch` per `Path` subterm; one `FreshPath` per path
**built** (`Singleton`, `Composition` products, `Unwrap` and `TailsUnion` tails, two per headed path
in a group split); a stored literal is returned, not built.  `Restriction`'s prefix test costs one
`PathItemComparison` per item compared, in the operands' iteration order (§6).  A partial `Range`
sorts: the platform sort (§6).  `Iteration`/`Fold`: one `LoopBodyEntry` per group; `Fixpoint`: one
`FixpointRound` per round, the terminating round included; `Call`: one `CallEntry`, and the
stabilised-argument shortcut re-evaluates the arguments under the callee environment (those
evaluations are counted).

Trie (`evalI`): one `TrieDispatch` per node, one `TriePathDispatch` per path subterm; a warm
literal is a lookup, a cold one is `fromSpaceValue` (a left fold of unions of singletons); every
ring operation costs one `TrieNodeVisit` at each node it examines plus the Patricia merge of the
two child maps (`PatriciaVisit` per recursive descent entry, `PatriciaEntry` per single-key
operation), with the identity and empty short circuits above; `Iteration` is a `joinAll` over the
per-head bodies, `TailsUnion`/`TailsIntersection` a `joinAll`/`meetAll` over the child subtries;
`Range` reads the cached terminal count (a walk, one visit per uncached node, on first use) and
slices by order statistics (children inside the window accepted, outside rejected, partial ones
descended); `Fixpoint` compares iterates on the equality frontier (`EqualityFrontierVisit`).

Graph (`execT`): one `GraphNodeDispatch` per executed slot, one `TrieOpEntry` per space slot, one
`GraphFrameAllocation` per scope entered (a loop's frame is allocated once for all its children), an
empty **left** operand short-circuits a binary slot without entering the algebra, and the trie rules
otherwise.

Zipper (`execZ`): one `ZipperBuild` per `Space` node lifted into a cursor; one `ZipperCursorRead`
per `terminal`/`children`/`descend` query, cascading through every virtual layer at the focus with
the executor's short-circuit order (`||`/`&&`); `ZipperMaterializeNode` + `FreshNode` per forced
non-literal node, none for a literal returned by pointer; `ReusedSpace` when a smart constructor
sees the same space twice; every control-flow constructor is one `ZipperFallbackToEvalI` plus
`evalI`'s own events; `Range` materialises its operand then slices (`TrieOpEntry`); the lazily
forced chains (`TailsUnion`, `TailsIntersection`, a deferred descent) read their source once.

## 6. What is a parameter, what is outside

* **The platform sort.**  `Range` on the reference backend sorts with the library sort; its
  comparison count depends on the platform's algorithm and the operand's iteration order, not on the
  language.  `EventSemantics.platformSortComparisons` computes it by running the same library sort
  with a counting comparator and is declared a `SemanticsProfile.platform` parameter.
* **Set iteration order.**  The reference backend's `Restriction` and `Range` read their operands in
  `Set` iteration order.  The semantics builds its sets with the same operations as `eval` and so
  sees the same order; the order is a property of the representation, recorded here, not modelled.
* **Cache state.**  A literal's cost and a `Range`'s count walk depend on whether the object is
  already cached (`iLiteralIsCached`, `ITrie.countIfKnown`).  The semantics reads that state and
  never changes it; the cache state is part of the machine state a run starts from.
* **Outside the counted unit** (unchanged from `OracleGap.declared`): `IntMap` node allocation
  inside the standard library, `Interner` probes per item, the un-interned key sort inside
  `ITrie.ordered`, the `Set` internals behind `eval`.  Each is bounded by a counted quantity there
  and is not a term of any rule here.
* **Grounded host functions** are applied, not specified.

## 7. What consumes this

* `SpatialSemanticsCheck` — differential conformance between the rules and counted executions.
* The abstract cost transfers bound the **structural quantities these rules count** —
  paired prefix frontiers, live operand counts, Patricia shapes, forced cursor nodes — and nothing
  else; a cost constant that is not the coefficient of a rule here is not admissible there.
