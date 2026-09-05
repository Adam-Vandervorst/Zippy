# Resource bounds by abstract interpretation (tasks.md A4–A6)

The cost analysis is `CostSem` / `GraphSem` in
[SpatialCostSemantics.scala](../src/main/scala/SpatialCostSemantics.scala): an abstract
interpretation of the counted event semantics of [SPATIAL_SEMANTICS.md](SPATIAL_SEMANTICS.md) (A1)
over the two-tier correlated domain of [SPATIAL_DOMAIN.md](SPATIAL_DOMAIN.md) (A3), with fixpoints
and recursive components read through the stratified IR of `DeltaIR.scala` (A2).  Its product entry
points are `SpatialPipeline.costOfOptimized` / `compareBackends` / `LoweredRoutine.cost`.  There is no
second cost model: the pre-A4 formulae in `SpatialCost.scala` are legacy, read by no gate suite and no
pipeline entry point.

## 1. What a result is

A `CostReport` carries, per backend (`reference`, `trie`, `zipper`, `graph`):

- `bounds: EventBounds` — an interval `[lo, hi]` per `EffortEvent`, so every component
  (`Work`, `Alloc`, `Rounds`, `Touch`) is the sum of its events' intervals; `hi` may be `inf`;
- `value: Abs` — the abstract value of the term in the A3 domain;
- `derivation: Derivation` — the DAG: one node per rule applied, with its facts, backend parameter,
  widening event, resulting bounds and children; `render()` is deterministic (two analyses of one
  program render identically);
- `domain: DomainCert` — every widening the domain applied, named;
- `notes`, `summaries` (A5 reuse counts), `dependencies` / `certified` / `certifiedModulo` (A6).

Nothing is evaluated: a `GroundedSS` that throws when run is priced as `⊤`, never detonated
(`SpatialCostCheck` "NO EVALUATION").

## 2. The rules, and where lower and upper endpoints come from

Every constructor of the certified language has one rule per backend, written after the executor's
own code path.  **Lower endpoints come from must facts, upper endpoints from may facts**
(`proofs/lean/Zippy/Spatial.lean#Zippy.Spatial.Ivl.must_may`):

| tier | lower endpoint (`Walk(share = true)`) | upper endpoint (`Walk(share = false)`) |
|---|---|---|
| exact operands | the algebra's recursion under MAXIMAL sharing: equal children are one object, equal child maps one Patricia map, so every `eq` short circuit fires | the same recursion under NO sharing: every pair of common keys is descended, every result node is rebuilt |
| summarized operands | `SpatialFrontier`'s must side, only for two distinct declared inputs | the frontier's may side and the Patricia envelope |

The Patricia merge is priced by the envelope `[1, 2k−1]` visits for `k` keys, which holds for every
interner id assignment (`proofs/spatial/REGISTRY.tsv` A6-PATRICIA); the exact visit count depends on
the process and is not predicted.  Other rules the acceptance suites forced into the model, each a
sharing or memoisation effect of the executors: the shared `ITrie.empty` constant's count is
memoised; a terminal-only node is *not* the shared `epsilon`; a declared input's count is memoised by
the warm run but a binder's tails object is rebuilt per run; the graph executor's empty-left short
circuit makes a may-empty left operand contribute no certain event.

**n-ary operations** (`TailsUnion`, `TailsIntersection`, the loop accumulation) are priced from the
ordered live frontier: distinct live operands after identity deduplication, the per-level Patricia
envelope, and one more `joinAll`/`meetAll` per common prefix below the roots.

**Loops** (`Iteration`): on an exact source one body per head with the head's tails a distinct
object; on a summarized source the body once under the *weakened* fibre of the prefix (sound for both
endpoints, linear in the nesting depth) times the fan-out, the value inferred through the certified
`Iteration` transfer.  puzzle15's sixteen projections are priced from per-cell fibres, with no
`Shape.top` (`SpatialCostCheck` "FIBRES").

**Fixpoints**: exact iteration round for round while the iterates are exact; past that the first
round is certain, later rounds are bounded by the accumulator's growth, and the widening is named.
A body not positive in its recursion variable is `⊤` (the IR's variance analysis is the premise).

**Calls** (A5): a non-recursive callee is answered by its *parametric summary* at the caller's
abstract arguments — computed once per (canonical routine identity, abstract input) and reused, the
result's relation to the arguments (by pointer to one of them, or fresh) carried across the call so
correlations compose; the body is never inlined as an analysis step.  A positive passthrough
recursive component (mutual recursion) is answered by the IR's simultaneous system, iterated as one
abstract least post-fixpoint and priced as the IR solver's rounds (`DeltaIR.Exec.solve`, naive
schedule, terminating round included).  A self-call of the shape `l ∪ r(args')` follows the
executors' stabilised-argument rule to its stationary point.  Anything else recursive is `⊤`, said.

## 3. The gate at milestone M1

Soundness is the gate: every counted execution inside its interval, every endpoint finite and below
`ProductRequirement.Astronomical` (10^12).  Checked by:

| suite | what |
|---|---|
| `SpatialCostCheck` | exhaustive small-model containment: every binary constructor over every pair of 64 values × 4 backends (399 360 rows), every unary/positional/loop constructor (11 264), summarized declarations (36 096), the randomized hunt (106 programs, exact and summarized), the two permanent zipper regressions, per-cell fibres, deterministic derivations, no evaluation |
| `SpatialEventsCheck` | the fuzzer corpus (181 programs, 4 backends) and the six cornerstones on `Routine.optimized`'s body, cold vs warm literals |
| `SpatialScaleCheck` | 15 generator families over a 9-rung geometric ladder to 16 384, on the optimized form |
| `SpatialPipelineCheck` | the pipeline's entry points: cornerstones finite and below the ceiling, deterministic certificates, declared inputs tighten, restriction/intersection/union slopes, the equal-but-distinct restriction allocating nothing |
| `CrossFunctionCostCheck` (A5) | changing path arguments, summary reuse, correlated results through a call, range of a call result, calls below binders, mutual recursion against the IR solver's counted rounds, cornerstone call chains |

Width against the product tiers is *reported* per (backend, component) — "wide intervals are
allowed at this milestone but are reported as not useful" — with no ledger of excused rows.
Measured on the ladders (2026-09-05): 1680 tier rows, 76 `NOT USEFUL`, all on `absorption` and
`rest-chain/nest`, where the exact tier's budget (`DomainBudget.enumerate = 512`) summarises inputs
beyond 512 paths and the interval widens.

## 4. Certification (A6)

`proofs/spatial/REGISTRY.tsv` names every transfer rule and what discharges it: Lean
(`proofs/lean/Zippy/Spatial.lean`: interval arithmetic and order, the must/may rule, range
normalisation, the widening contract, the finite-model principle), the independent checker
(`proofs/spatial/check_transfers.py`: every exact-tier value transfer re-derived over the whole small
universe, the pricing rows' containment re-checked), the differential suites (conditional on the
trusted boundary **T9**: the counted executors *are* the event semantics), and three stated premises.
`CostReport.certified` is true only when every rule a derivation used is `PROVED` or a stated premise
in `proofs/spatial/STATUS.tsv`; `scripts/proof_closure.py --check` refuses an `OPEN` row.  The
written argument connecting the checker's finite universe to the general rules is
[proofs/spatial/README.md](../proofs/spatial/README.md).
