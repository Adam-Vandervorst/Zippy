# Zippy Operational Traps

Derived from the append-only `build.log`; each row is a recurring failure mode, not merely history.

| Trap | Avoidance |
| --- | --- |
| `sbt` is absent; Scala CLI can miss `build.sbt` test libraries. | Use the documented Scala CLI command with Scala 3.8.1, source 3.3, MUnit, and collection-contrib. |
| Optional `lot.metta`, NOAA NetCDF, carac, and `fred.rle` data may be absent. | Use committed `noaa_slice.txt` and deterministic parsers/fallback fixtures; label fallback results. |
| Empty paths are values, but iteration has no head for them. | Preserve epsilon in codecs/literals/range; skip it only where head iteration requires a nonempty path. |
| Range’s `end = 0` sentinel and negative/border slices are easy to normalize incorrectly. | Centralize bounds in `RangeBounds`; regression-test full, empty, first/last, negative, and border-child cases. |
| `TailsIntersection` is undefined for no headed inputs if implemented with raw `reduce`. | Return empty for empty/headless sources and test the universal-query convention. |
| A rewrite may move a branch across `Iteration` while capturing `symbol` or `rest`. | Use binder-aware free-variable analysis; test substitution, alpha-equivalence, and empty-source behavior. |
| Recursive zipper evaluation can materialize a whole trie or loop through self-union. | Keep product/selectors virtual; lower only proved union-saturating recursion, and reject unsupported recursion explicitly. |
| Structural equality in `HashSet[AnyRef]` recursively hashes huge case-class tries. | Use `IdentityHashMap`/identity dedup for shared trie/zipper DAGs; cache child counts and schedule meets by the smallest key set. |
| Eager union/diff before prefix restriction destroys selectivity. | Push restriction through union/difference where sound; assert both denotation and virtual zipper shape. |
| Generic closure/range rules can explore every child or saturate egglog. | Use demand-driven frontier/border observations, cache closure frontiers, and isolate expensive focused witnesses. |
| Large Scala interpolated egg witness blocks can trigger compiler `StackOverflowError`. | Keep the shared prelude small; put new focused witnesses in separate source/artifact files. |
| Broad egglog/prover runs can time out or exhaust memory. | Start with focused artifacts, bounded alphabets/depths, per-file timeouts, small solver-worker counts, and JVM memory caps; never call a skipped gate passing. |
| Warm-up-sensitive backend benchmarks produce misleading speedups. | Warm all candidates, correctness-check first, publish per-workload results, and retain the reference default unless a heuristic is justified. |
| Constant-folding with a faster backend can regress some workloads. | Track backend-specific counters/timings; select per shape or keep reference evaluation as the default. |
| Exact serialized graph text changes under legitimate optimization. | Assert semantics and stable structural properties, not incidental node spelling/layout. |
| Proof manifests may say zero `UNPROVED` while bounded rows remain debt. | Report `PASS_WITH_PROOF_DEBT` accurately; distinguish unbounded, bounded, and manifest-only runs. |
| The valued path-map track does not inherit unit path-set laws automatically. | Keep it sidecarred; require explicit merge/meet lattice laws before importing optimizer rewrites. |

Before changing execution or proofs: run focused denotation tests, preserve fallback notes, regenerate only through the owning generator, then choose a bounded/full verification gate consistent with available memory.
