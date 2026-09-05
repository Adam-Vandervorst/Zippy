# Zippy Architecture Atlas

**An index of where functionality lives.** One row per component: name, file, and what it does.
Component names are the symbols to grep for; line numbers are deliberately omitted because they rot.

Theory and operator semantics: [ALGEBRA.md](ALGEBRA.md). Supercompiler design:
[SUPERCOMPILER.md](SUPERCOMPILER.md). Run recipes and CI checkers: [README.md](../README.md).
Trusted base (every assumption a `PROVED` verdict rests on): [TRUSTED.md](TRUSTED.md).
Invariants: [design_plan.md](design_plan.md). Analysis designs:
[design_size_constraints.md](design_size_constraints.md),
[design_spatial_lattice.md](design_spatial_lattice.md).

```
Surface DSL (Syntax, itypes/otypes)                                                     §1
        │  builds
Core AST + values (Space / Path; SpaceValue / PathValue; Routine)                     §2
        │
        ├── eval ................................. reference semantics (the ORACLE)     §3
        ├── transpile → RecursiveOpGraph → exec (SpaceValue) / execT (ITrie)            §4
        ├── evalT (TreeMap Trie) / evalI (interned ITrie)                               §5
        └── transpileZ → SpaceZipper → execZ (fused cursor)                             §6

Optimizer     Routine.optimized (Lower fixpoint) ; optimize = push_out + optimize_sharing   §7
Recursion     lowerCalls → asFixpoint / lowerMutualSCC → Fixpoint subgraphs                 §8
Analysis      size / length / spatial type / recursion / cost                               §9
Supercompiler SC.drive (reduce/unfold/fold/whistle/generalize) → Residual → op-graphs      §10
Verification  EquivPipeline / AgnosticPipeline / SmtDiff → egg + SMT certificates           §11
Corpus/fuzz   Fuzzer → SpaceFuzzer → corpus_1000 → differential suites                  §12–13
```

Every executor is validated against `eval`; every optimizer rewrite must preserve `eval`; every
equivalence certificate is gated by `eval` before a prover runs.

---

## 1. Surface DSL & type inference

| Component | File | What |
|---|---|---|
| `Syntax` | `MORKL.scala` | The construction surface: String→Path conversions, operators (`\/` union, `/\` intersection, `\` subtraction, `<\|` restriction, `\\|` raffination, `x` composition), `iter`/`iterk`/`fold`/`head`/`on_empty`, `:=` (routine), interpolators `S`/`P`/`R`/`ss`/`sP`, `mod(...)` (routine table). |
| `itypes` | `MORKL.scala` | Input-type inference: the set of input path-shapes a Space consumes, as `$`-prefixed type variables. `Fixpoint` unimplemented. |
| `otypes` | `MORKL.scala` | Output-type inference; dual of `itypes` (opposite treatment of `Wrap`/`Unwrap`). |

## 2. Core AST & values

### 2.1 Vocabulary and ASTs

| Component | File | What |
|---|---|---|
| `PathItem` | `MORKL.scala` | `type PathItem = String` — one trie edge. |
| `PathRef` / `SpaceMention` / `RoutinePtr` | `MORKL.scala` | Named path / space / routine variables. `PathRef.lengthHint` and `SpaceMention.sizeHint` carry declared bounds (`known(...)`). |
| `Path` | `MORKL.scala` | Path-expression enum: `Deref`, `Constant`, `Concat`, `GroundedPP`/`GroundedSP`; `factors`/`fromFactors`. |
| `PathValue` | `MORKL.scala` | Concrete path `List[PathItem]`; `prefixes`, `mostSpecific`. |
| `Space` | `MORKL.scala` | The space-algebra AST: `Empty`, `Literal`, `Singleton`, `Mention`, `Call`, `Union`/`Intersection`/`Subtraction`/`Restriction`/`Raffination`/`Composition`, `Wrap`/`Unwrap`/`TailsUnion`/`TailsIntersection`, `Iteration`, `Fold`, `Fixpoint`, `Range`, `GroundedPS`/`GroundedSS`. |
| `SpaceValue` | `MORKL.scala` | `Set[PathValue]` — the value of a Space. |
| `Routine` | `MORKL.scala` | `Routine(name, refs, mentions, body)`, the compilation unit. `optimized` = spatial hook + `Lower` fixpoint over inlined callees; `optimizedPlain` = the same without the spatial hook. |

### 2.2 Environments, ordering, serialization

| Component | File | What |
|---|---|---|
| `PathContext` / `SpaceContext` families | `MORKL.scala` | Persistent binder environments (base / `Overlay` / `Map` / fuzz `mixed`) that make `eval` total. |
| `pathValueOrdering` | `MORKL.scala` | Canonical trie order (String order per item, shorter-is-less on a shared prefix). |
| `RangeBounds` / `sliceRange` | `MORKL.scala` | Window normalization to a clamped half-open `[lo,hi)` and the ordered slice `Range` denotes. |
| `LiteralCodec` / `LiteralStore` | `MORKL.scala` | Lossless textual codec for op-graph literal constants; in-process by-reference literal interner. |
| `Tuning` | `MORKL.scala` | Load-time ablation toggles (`literalByRef`, `patriciaOps`). |

## 3. Reference evaluator

| Component | File | What |
|---|---|---|
| `eval` | `MORKL.scala` | The denotational reference over `Set[PathValue]` — total, and the oracle every other component is checked against. `recs` (spaces) / `recp` (paths); Calls resolve through the routine table with a tail-recursion fixpoint guard. |

## 4. Operation-graph backend

| Component | File | What |
|---|---|---|
| `Node` / `RecursiveOpGraph` | `MORKL.scala` | Flat instruction and the nested scope container (root node, parent chain, child subgraphs); `store`/`lookup`/`find`. |
| `transpile` | `MORKL.scala` | Space/Path AST → op-graph. Prologue `ExtractPathRef`/`ExtractSpaceMention` slots per input; `Iteration`/`Fixpoint` become child subgraphs. |
| `exec` | `MORKL.scala` | `SpaceValue` stack-machine executor; mirrors `eval.recs` per op with empty-set short circuits. |
| `execT` | `GraphExec.scala` | The same graph executed over interned `ITrie`s. Iteration reads each source child as an already-grouped (head, tail) pair. |
| `untranspile` | `MORKL.scala` | Op-graph → AST (round-trip oracle). `Call` not implemented. |
| `runGraph` / `runGraphT` | `GraphExec.scala` | Entry points binding named inputs by name, then `exec` / `execT`. |
| `graphviz` / `graphviz_table` / `mermaid` | `MORKL.scala` | Debug renderers for a graph's scope tree. |

## 5. Trie backends

### 5.1 TreeMap `Trie`

| Component | File | What |
|---|---|---|
| `Trie` | `Trie.scala` | Persistent trie over `TreeMap[PathItem,Trie]`, canonical (no empty subtries) so `==` is set equality and `eq` is a valid sharing signal. `empty`/`epsilon`/`singleton`/`suffixClosure`/`fromSpaceValue`/`toPaths`/`pathsInOrder`; `size` caches the per-node terminal count and `range` is an order-statistic slice over it (whole-subtrie accept/reject by pointer). |
| `Trie.AlgebraicResult` + `*R` ring ops | `Trie.scala` | Per-node outcome `Empty \| Identity(mask) \| Bespoke`; `unionR`/`intersectionR`/`subtractionR`/`restrictionR`/`raffinationR`/`compositionR`. Whole-subtree accept/reject by pointer; `a eq b` short circuit. The more complete book-keeper of the two implementations (it can report the `BOTH` bit across distinct objects). |
| `Trie` n-ary & prefix ops | `Trie.scala` | `joinAll`/`meetAll` (simultaneous merges), `wrap`/`unwrap`/`tailsUnion`/`tailsIntersection`/`head`. |
| `Zipper` (read zipper) | `Trie.scala` | Focus + breadcrumb walk primitive over a `Trie`; lossless `descend`/`ascend`. |
| `pathItemsT` | `Trie.scala` | `Path` AST → `List[PathItem]` inside `evalT`'s contexts. |
| `literalTrie` | `Trie.scala` | Identity-keyed memo of `SpaceValue → Trie`. |
| `evalT` | `Trie.scala` | Recursive evaluator over `Trie`; case-for-case with `eval`. |

### 5.2 Interned `ITrie`

| Component | File | What |
|---|---|---|
| `Interner` | `IntTrie.scala` | Process-global bidirectional `PathItem ↔ Int`; un-interning only at value boundaries. |
| `ITrie` + `ITrie.AlgebraicResult` | `IntTrie.scala` | Persistent trie keyed by interned ints over `IntMap` (Patricia). Every ring op returns an `AlgebraicResult`, so whole subtries are accepted/rejected by pointer and identity propagates to the root. `raffination` is one fused pass; `range` is an order-statistic slice over cached terminal counts; `equalT` walks only the equality frontier; n-ary `joinAll`/`meetAll`. |
| `evalI` | `IntTrie.scala` | Evaluator over `ITrie` — the executable `Backend.Trie` names. `pathItemsI` resolves paths; `iLiteral`/`iLiteralStr`/`internConstStr` cache literal and constant decoding. |
| `IntTrieOps` | `IntTrieOps.scala` | Single-descent Patricia merges of the child maps (`unionTries`/`intersectTries`/`diffTries`/`restrictTries`). Lives in `package scala.collection.immutable` to see `IntMap`'s internals. **Returns the argument map object when a merge changes nothing** — the mechanism that lets identity propagate. |

## 6. Zipper backend & egg

| Component | File | What |
|---|---|---|
| `SpaceZipper` | `Zipper.scala` | Lazy fused cursor: virtual `Union`/`Intersection`/`Subtraction`/`Composition`/`Prefix`/`RestrictionNode`/`TailsUnion`/`TailsIntersection` nodes over `Lit` tries, navigated per layer (`terminal`/`children`/`descend`), collapsed by one DFS `materialize`. Identity laws fire on `sameSpace` pointer identity only. |
| `transpileZ` | `Zipper.scala` | Space → fused cursor; local set algebra becomes virtual nodes, control flow (`Iteration`/`Fold`/`Fixpoint`/`Call`/grounded) delegates to `evalI` and is re-lifted. |
| `execZ` | `Zipper.scala` | `materialize(transpileZ(s))`. |
| `ZipperEgg` | `ZipperEgg.scala` | Renders a cursor into the egglog movement (`Z`) and implementation (`Tr`) vocabularies and builds coincidence-check programs certifying the virtual cursor denotes what `execZ` computed. |

## 7. Optimizer

### 7.1 Op-graph passes

| Component | File | What |
|---|---|---|
| `optimize` | `MORKL.scala` | Alternates `push_out` and `optimize_sharing` to a `structuralHash` fixpoint under a `Deadline`. |
| `push_out` | `MORKL.scala` | Loop-invariant code motion for nodes and whole subgraphs, plus union/composition splits with headed-guard synthesis. One split per invocation. |
| `optimize_sharing` | `MORKL.scala` | Global CSE by structural value numbering over nodes and subgraphs, α-invariant loop merging; each scope's result slot is pinned. |

### 7.2 Support

| Component | File | What |
|---|---|---|
| `structuralHash` / `wellFormed` / `optimizedAway` | `MORKL.scala` | Fixpoint fingerprint; coordinate checker; closed-constant detector. |
| `Deadline` / `Profiler` | `MORKL.scala` | Compile budget passes poll, and per-pass time/size accounting. |
| `nodeCount` / `loopNodes` | `MORKL.scala` | Structural size measures (`loopNodes` is `push_out`'s headline metric). |
| `all_forever` | `MORKL.scala` | Apply a rewrite list until structurally stable or out of budget. |
| `inlineCalls` | `MORKL.scala` | Splice non-recursive Calls to a fixed point. |
| `collect` / `subs` | `MORKL.scala` | The generic fold and pre/post substitution every law and lowering pass is built on. |
| `Reflect` | `MORKL.scala` | Space AST → `SpaceValue` (code as data); no production callers. |

### 7.3 `Lower` rewrite laws

All in `MORKL.scala`, `object Lower`; certificates live in `proofs/laws/`.

| Law | What |
|---|---|
| `AlgebraicIdentities` | ~30 syntactic identities: Empty absorption/units, idempotence, ε-concat units. |
| `LiteralSpaceOps` / `ConstantOps` | Constant-fold an op whose operands are all literals (`ConstantOps` is the broader `try eval` form). |
| `SizeEmpty` | Collapse to `Empty` whenever `sizeBounds.hi == 0`. |
| `IterUnion_Indep` | The product-buster: hoist a loop-invariant union branch out of an iteration, gated by `provablyHeaded` else guarded. |
| `IterComposition_Indep` | Hoist a loop-invariant composition factor (no guard needed). |
| `EpsGuard_Wrap` | Commute a ⊆{ε} guard into a `Wrap`. |
| `WrapMerge` | Merge equal-prefix wraps; annihilate incomparable-prefix meets/differences. |
| `IterWitness_TransposeSemiJoin` | Narrow a k-nested single-item iteration by a materialized transpose index of an invariant witness. |
| `IterWitness_HeadNarrow` | Narrow every level of a rest-chained nest by `Restriction(src, Head(...))`. |
| `UnwrapPush` / `RestrictionPush` / `RaffinationPush` | Push `Unwrap` / `Restriction` / `Raffination` through the set ops. |
| `RaffRestrictAlgebra` / `RestrictRaffWrapBoth` | Collapse the raffination/restriction partition; descend both below a common wrap prefix. |
| `CompWrapAssoc` / `CompAssocRight` / `CompLitWraps` | Composition normalization: slide a left wrap out, right-associate, trade a small left literal for a union of wraps. |
| `IterSetOpMerge` | Merge two same-source iterations under a set op (∩/\ only under the `keyedBy` guard). |
| `TailsUnion_Iteration` / `Iter_Tails` | Lower `TailsUnion` to an `Iteration` and back. |
| `IterateLiteral_Union` / `IterateSingleton_Deref` | Unroll iteration over a literal (one copy per **distinct head**) or a single-item singleton. |
| `Literal_ConstantsUnion` / `Concat_Path` / `SingletonConstPrefix_Wrap` | Literal explosion, constant-path fusion, singleton prefix splitting. |
| Unwrap algebra (`Unwrap_Merge`, `Unwrap_Wrap`, `UnwrapConcat_Unwraps`) | Split concat-prefix unwraps, merge adjacent constant unwraps, cancel an unwrap against a wrap. |
| `UnionChain_TailsU` | Re-express a ≥4-ary union chain as a `TailsUnion`. **Off by default.** |
| Misc singleton / iteration / range laws | `SingletonConst_Literal`, `SingletonSpaceOp_PathOp`, `SingletonComposition_Wrap`, `SingletonRestriction_Unwrap`, `ConcatSingleton_Iter`, `Wrap_Iter`, `Iter_Ident`, `TailsUnion_Singleton`, `Range_Singleton`, `IterCompRight_Hoist`. |
| `inline` | Beta-reduce a `Space.Call` against a routine table. |
| `nonEmptyGuard` / `headedGuard` | One-path guard factories producing a ⊆{ε} space; `headedGuard` is what `IterUnion_Indep` plants. |
| `provablyNonEmpty` / `provablyHeaded` / `provablyEpsSubset` | The one-sided certainty predicates the gated laws consult (defined by `sizeBounds`). |

## 8. Recursion lowering

All in `MORKL.scala`.

| Component | What |
|---|---|
| `lowerCalls` | The driver: `asFixpoint` per routine, `lowerMutualSCC` per SCC, inline the now-acyclic remainder, return `(topBody, residual)`. Un-lowerable recursion survives as residual Call routines. |
| `asFixpoint` | Union-saturating self-recursion with an identity base → `Space.Fixpoint`. |
| `asFixpointGeneral` | `BASE ∪ r(T(mention))` → a two-tagged-state `Fixpoint`, gated by a structural monotonicity check. |
| `lowerMutualPassthrough` | A passthrough mutual SCC → one tagged `Fixpoint`, projected back per routine by `Unwrap`. |
| `lowerMutualByElimination` | A 2-routine arg-changing SCC by Gaussian elimination into a self-recursion. |
| `lowerMutualSCC` | Dispatcher: passthrough first, then elimination, else honest residual. |

## 9. Static analysis

| Analysis | Tier-1 (compositional) | Tier-2 (z3) | Answer |
|---|---|---|---|
| Space size `\|eval(s)\|` | `Lower.sizeBounds` (`MORKL.scala`) | `SizeZ3` (`SizeConstraints.scala`) | `SizeBounds(lo, loHeaded, hi)` |
| Path length | `Lower.lenBounds` (`MORKL.scala`) | `LenZ3` (`LengthConstraints.scala`) | `LenBounds(lo, hi)`; `lo > hi` = provably empty |
| Counts per length | `SpatialTypes.infer` | — (meets the two above) | `SpaceType(byLen, rest, restLens)` |
| Shape × counts | `SpatialTyping.infer` | — | `SpatialType(Shape, SpaceType)` + `Vector[Fact]` |
| Call depth | `SpatialRecursion` | — | `DepthBound` + `BoundedRecursion` residual |
| Cost | `CostSem.analyze` / `CostSem.analyzeGraph` (`SpatialCostSemantics.scala`) | — | `CostReport`: per-event interval bounds (`EventBounds`) with a derivation DAG, per `Backend` |

Analyses read **annotated types only** — no evaluation output feeds a bound.

| Component | File | What |
|---|---|---|
| `Lower.sizeBounds` / `SizeBounds` | `MORKL.scala` | Per-constructor cardinality transfers over saturating intervals, interprocedural through the routine table; `hi == 0` is the empty space. |
| `Lower.lenBounds` / `pathLenBounds` | `MORKL.scala` | The same shape for path lengths; `Fixpoint` iterates with a post-fixpoint check. |
| `SizeZ3` | `SizeConstraints.scala` | Hash-cons every subterm, assert the tier-1 baseline plus the saturated ⊑ relation and per-constructor cardinality laws, and read the root interval off a z3 `Optimize` box. `Status` records `Solved`/`ScopeLimited`/`NoSolver`/`SolverFailed`; the answer never widens the baseline. Helpers: `alphaRename`, `scopesProblem`, `encode`, `encodeText`, `runZ3`, `parseObjectives`. |
| `LenZ3` | `LengthConstraints.scala` | The length analogue, over disjunctive `define-fun` length predicates. |
| `Ivl` / `SpaceType` / `SpatialEnv` / `SpatialTypes` | `SpatialTypes.scala` | The length-indexed count domain (a count interval per length plus one spill bucket) and its transfers; `disjoin` keeps tracked classes and the spill disjoint. Projections are the size and length analyses. |
| `Presence` / `Shape` | `SpatialShape.scala` | The bounded abstract trie: ε presence (`No`/`May`/`Must`), a tracked head map, an untracked-head count, and an `otherTail` summary, capped by `MaxDepth`/`MaxHeads`. Owns `contains`/`leq`/`leqStrong`/`meet`/`lub`/`joinAlternatives`/`widen`/`unionTransfer`. The per-operator may/must table is in the file header. |
| `SpatialType` / `Fact` / `SpatialTyping` | `SpatialTypeSystem.scala` | The reduced product (shape × counts + explicit `bottom`) with its 8-rule bidirectional reducer, `accepts`, `leq`, `pathsAtDepth`, `prefixesAt`; `SpatialTyping.infer` is the one-pass abstract interpreter, with Kleene iteration at `Fixpoint`. |
| `SpatialConfig` / `NodeId` / `NodeAnalysis` / `SpatialAnalysis` | `SpatialAnalysis.scala` | The decorated traversal: one pass producing a per-position `NodeAnalysis` (type, facts, provenance) keyed by `NodeId`, so downstream consumers share one result instead of re-inferring. |
| `SpatialFacts` | `SpatialFacts.scala` | The derived facts backends act on: depth degrees `E_d`/`K_d`, `PrefixProfile`, `trieNodes`, fibre pigeonhole envelopes, `RestChain`/`ChainBound` (the rest-chain frame law `Σ_d K_d`), specialization candidates, and the `ItemPattern`/`PathPattern` strata. |
| `SpatialFrontier` | `SpatialFrontier.scala` | The relational fact of one binary node: the active prefix frontier `Q`/`A`/`J`, the algebraic result case, per-depth paired counts, terminal-prefix accepts, Patricia visits and a rebuilt-node bound (`FrontierSummary`, `FrontierSyms`, `FrontierSource`). |
| `SpatialDemand` | `SpatialDemand.scala` | The zipper's demand analysis: a `ZIR` of the fused cursor, demanded-prefix `Layers`, `Pairing`, and a `DemandSummary` of forced non-`Lit` cursor nodes — the allocation parameter a per-operator sum gets wrong. |
| `ProofTrace.Node` / `Dag` / `Builder` / `Checker` | `ProofTrace.scala` | typed, compositional proof traces — law instances at positions with their exact matcher, unfold (O6a), fold (O12b), generalization, positional replacement, backend refinement, optimiser no-ops, transitive composition; hash-consed DAG, deterministic rendering (`proofs/pipeline/traces/*.trace.tsv`), and the in-process replay checker.  `SC.State` records one per residual node when `Config.trace` is on; `scripts/check_traces.py` is the independent structural reader. |
| `Alternatives` (`Alternative`, `Frontier`, `Builder`, `explore`) | `Alternatives.scala` | residual alternatives as explicit nodes — residual, typed proof trace, spatial input assumptions, per-backend resource certificate, provenance; produced by driving one configuration under several law tables (fusion / sharing / prefix-restriction / range families off) and unroll depths, evaluation-free (the GROUND laws are removed); hash-consed by alpha-canonical residual under equal assumptions, subsumption, a widening budget with every pruned alternative recorded; deterministic TSV and trace serialization. |
| `Pareto` (`Objective`, `Candidate`, `Selection`, `decide`, `replay`) | `Pareto.scala` | selection from the certified frontier — admission (certified spatial derivation AND closed trace), constraints proved by the upper bound, dominance over interval-valued work/alloc/rounds/touch (never with an infinite upper bound; the reference's touch is unknown), incomparable survivors kept, the declared tie rule; the certificate is a pure function of the candidate rows and `scripts/check_selection.py` re-derives it independently. |
| `TraceClosure` | `TraceClosure.scala` | the in-process dependency closure of a proof trace: laws to `proofs/STATUS.tsv` through `proofs/laws/REGISTRY.tsv`, unfold/fold/generalization to the O6a/O12a/O12b registry rows, refinement nodes to their artifact's status; CLOSED / CONDITIONAL T… / OPEN. |
| `Decisions` (`Case`, `Outcome`, `run`, `document`) | `Decisions.scala` | a decision case = program + symbolic precondition + objective; alternatives are explored and selected, then run on every executor with counted events beside the intervals; two scalar predictors (rewrite count, output cardinality) are evaluated on the same frontier; renders `proofs/decisions/DECISIONS.tsv` rows and `docs/DECISIONS.md`. |
| `Mutation` | `Mutation.scala` | five switches that each remove one property of the resource analysis (drop-alias, reverse-range, erase-calls, optimistic-lower, no-widening-record), consulted at exactly one site each; never set outside `MutationGates`. |
| `EventKind` / `SemanticsProfile` / `EventSemantics` / `SpatialEvents` | `SpatialSemantics.scala` | the backend-parameterised event algebra and the compositional event semantics of every certified constructor (reference / trie / graph / zipper as parameters); `SpatialEvents.counted` is the counted interpreter the semantics is checked against (`SpatialSemanticsCheck`). |
| `Variance` / `DepGraph` / `EqSystem` / `Lowered` / `Delta` / `Exec` | `DeltaIR.scala` | the stratified delta-fixpoint IR — variance analysis, positive SCCs as simultaneous least-post-fixpoint systems, strata, the differential (semi-naive) schedule with the checked step equation, replayable Lean-backed premises (`proofs/lean/Zippy/Strata.lean`, `Delta.lean`). |
| `XTrie` / `XChoice` / `XSumm` / `Abs` / `Domain` / `DomainFacts` | `SpatialDomain.scala` | the two-tier correlated spatial domain — hash-consed exact tries with alternatives, summaries via the certified `SpatialTyping` transfers, alias channel, per-analysis arena, named widenings (`docs/SPATIAL_DOMAIN.md`). |
| `EventBounds` / `Derivation` / `CostReport` / `CostSem` / `GraphSem` | `SpatialCostSemantics.scala` | resource bounds by abstract interpretation of the event semantics over the correlated domain — lower bounds from must facts, upper from may facts, exact walks mirroring the trie algebra and zipper cursors, the ordered live frontier for n-ary operations, fixpoints and stationary-argument recursion, and a deterministic derivation DAG per interval. The product entry points (`SpatialPipeline.costOfOptimized`, `compareBackends`, `LoweredRoutine.cost`) read this. |
| `Sym` / `Cost` / `CostInterval` / `Meas` / `Rel` / `CostModel` | `SpatialCost.scala` | Legacy expected-cost model, retained only for the non-gate suites that still read it (`SpatialAcceptance`, `BackendProfileCheck`, `SpatialDemandCheck`, `SpatialCertBudgetCheck`); no gate suite or pipeline entry point prices with it any more. Also still hosts `Backend`, `ExecutionPhase`, `CostForm`. | The symbolic cost algebra (`1 < log n < n < n log n < n² < 2ⁿ`) and the backend instances (`ReferenceCost`, `TrieCostModel`, `GraphCost`, `ZipperCost`, plus the diagnostic `NaiveTrieCostModel`), each transfer returning a lower/upper `CostInterval` over `work`/`alloc`/`rounds`/`touch`. `analyze` is the entry point; `FrontierCensus` publishes how much of a program was frontier-driven. |
| `EffortEvent` / `Events` / `EffortSink` / `Effort` / `Calibration` | `SpatialEvents.scala` | The counted-execution oracle: the closed event vocabulary (each event mapped to exactly one component), the inline `effort(...)` hooks in the executors, `EffortSink.count(body): (A, Events)`, and the cold/warm `ExecutionPhase` split. Zero cost when disarmed. |
| `SpatialRecursion` | `SpatialRecursion.scala` | Interprocedural summaries, the decreasing measure, `maxCallDepth`, and residualisation for calls that cannot be bounded. |
| `SpatialCheck` / `SpatialChannels` / `SpatialSignature` | `SpatialCheck.scala` | The consumer-facing typechecker: `Proved`/`Refuted(witness)`/`Unknown` per channel, witness search over a finite universe, `SpecializedRoutine(precondition, residual)`, and a diagnosis naming the blamed channel. |
| `SpatialLaws` / `SpatialBoundLaw` / `LawEvidence` | `SpatialLaws.scala` | Semantic laws as analysis inputs, each carrying provenance and an evidence policy separating assumed from proved; `refine` applies them to a position's bound. |
| `SpatialGamma` | `SpatialGamma.scala` | The concretization γ used by the law and acceptance suites to test soundness against `eval`. |
| `SpatialAnnotations` / `RoutineAnalysis` / `SpatialPipeline` / `SpatialHook` | `SpatialPipeline.scala` | The ordinary entry point: annotate a routine, analyze it once, expose `backendCost`/`compareBackends` (an interval COMPARISON — automatic backend selection is a non-goal)/`Rewrite`s, and `SpatialHook.rewrite` — the spatial rewrite `Routine.optimized` runs before the `Lower` rules. |

## 10. Supercompiler

All in `Supercompiler.scala`.

| Component | What |
|---|---|
| `Matching` | Term-algebra utilities: free variables, capture-avoiding substitution, `canon`, α-renaming, `instanceOf` (the fold), `embeds` (the whistle), `msg` (generalization). |
| `SC` | `sourceLaws` (~35 meaning-preserving `Lower` rules, excluding Call inlining), `reduce`, `Config`, `validate`, `run`/`supercompile`. |
| `SC.State` | The driving engine: alternate reduce/unfold, then fold / whistle / generalize per Call. |
| `Residual` | Driven top Space plus generated routines; `evaluate` checks it against `eval`. |
| `SCStats` / `SCReport` / `SupercompiledProgram` | Size and driver metrics, the auditable per-run account with phase timing, and the packaged result (residual + report + graphs). |
| `Supercompiler` | The facade: drive, lower to op-graphs, account backend support, time every phase. `compileCall`/`compileRoutine`/`specialize`. |

## 11. Equivalence pipeline & tooling

| Component | File | What |
|---|---|---|
| `EquivPipeline` | `EquivPipeline.scala` | `expand` (trusted stage-0 control-flow expansion, gated by `eval`) plus the renderers into the egg vocabularies and SMT membership equivalence. |
| `AgnosticPipeline` | `EquivPipeline.scala` | The data-agnostic certificates: inputs stay uninterpreted, `unrollControl` k-unrolls fixpoints and cuts residual self-calls to a fresh free input. |
| `SmtDiff` | `EquivPipeline.scala` | Decomposes whole-program equivalence into optimizer-rewritten subterm pairs, classified law-justified (replayed against the certified corpus) or residual obligation. AC-aware. |
| `lawCertificates` | `EquivPipeline.scala` | Law name → certificate file, mirroring `proofs/laws/REGISTRY.tsv`. |
| `EquivPipelineTest` | `src/test/scala/EquivPipelineTest.scala` | Runs all three stages on the SEVEN cornerstones (`puzzle3-full` is the one whose recursion is an unbounded `Space.Fixpoint`), writes `proofs/pipeline/*.smt2` + its own `proofs/pipeline/STATUS.tsv` and `zipper-egg-tests/pipeline/*.egg`, verifies with egglog + z3 + Vampire. A cell neither prover discharges becomes a `PROVER-BUDGET-EXCEEDED` record with its attempt log and stops counting as REAL. |

| Script | What |
|---|---|
| `scripts/gen_law_obligations.py` | Generates `proofs/laws/law_*.smt2` + `REGISTRY.tsv` from the shared FO prelude. |
| `scripts/mine_laws.py` | Throws z3 + Vampire at candidate laws; records verdicts in `MINED.tsv`. |
| `scripts/gen_spatial_obligations.py`, `gen_spatial_semantic_obligations.py` | Generate the spatial-lattice and spatial-semantic obligation corpora (`proofs/spatial/`, `proofs/spatial-semantic/`). |
| `proofs/run.sh` | Discharges every obligation with **both** provers, writes `proofs/STATUS.tsv`; a countermodel or unexpected OPEN exits non-zero. |
| `scripts/check_obligations.py`, `check_laws.py`, `audit_pipeline_markers.py` | CI gates: every egglog rule carries live proof evidence; every `SC.sourceLaws` entry has a PROVED certificate; no vacuous pipeline artifact. |
| `scripts/check_locality.sh`, `lint_zipper_egg.py` | The syntactic guarantees behind the O(d) movement claim (no materialization, one step per layer). |
| `scripts/make_bridge.py`, `gen_bridge_tests.py` | Build the spec↔impl bridge prelude and the randomized 3-way coincidence tests. |
| `scripts/extract_formal_preludes.py`, `extract_noaa_slice.py` | Extract the rule-only egg preludes; extract the NOAA temperature fixture. |

## 12. Fuzzer & corpus

| Component | File | What |
|---|---|---|
| `Fuzzer` | `Fuzzer.scala` | The `Dist[T]` sampling combinator library (`Uniform`/`Categorical`/`Dep`/`Repeated`/…). |
| `Loc` | `Fuzzer.scala` | A lazy structural description of a path set answering `is_path`/`branches`, with combinators mirroring the algebra and `instantiate` to a concrete value. |
| `SpaceFuzzer` | `Fuzzer.scala` | Generates dependent `(argument, program, result)` triples — the argument space is sampled first and the program is drawn over it. |

## 13. Test suites

### 13.1 Differential & law gates

| Suite | What |
|---|---|
| `CorpusValidation` | The definitive gate: `eval == evalI == evalT == exec == execT == execT(opt) == execZ` over 1000 programs × 1000 input environments. |
| `CorpusLawValidation` | `SC.reduce` preserves `eval` across the corpus — catches a wrong law both backends share. |
| `AlgebraicLaws` | Metamorphic gate on the ~45 set-algebra laws themselves under `eval`. |
| `OptimizerProperties` (`PropertyTest.scala`) | Randomized: transpile/optimize preserve `eval`; `Fixpoint` matches an independent closure. |
| `ProductUnionCheck` | The Space and op-graph optimizers both push a nested product into a union, and the guards are semantically necessary. |

### 13.2 Per-backend gates

| Suite | What |
|---|---|
| `TrieTest` | `Trie`/`evalT` behaviour against `eval`. |
| `OptimalTrieCheck` | `ITrie.AlgebraicResult` soundness at every node on random and correlated operands, completeness of the LEFT identity bit, the pinned `BOTH`-bit under-report, and the asymptotic gates (identity restriction, full `Range`, `joinAll`, `meetAll`, fused raffination, `equalT`) with before/after slopes. |
| `ZipperTest` / `ZipperEggTest` | Cursor algebra and movement/impl coincidence programs. |
| `GraphExecT` (`GraphExecTest.scala`) | Op-graph executor and coordinate well-formedness. |

### 13.3 Supercompiler suites

`SCMatching`, `SCDriver`, `SCGeneralization` (`SupercompilerTest.scala`); `SCHardening`, `SCFacade`
(`HardeningTest.scala`); `SCDegeneracies` (`SCDegeneracies.scala`).

### 13.4 Size / length analysis suites

`SizeBoundsCheck`, `SizeZ3Check`, `LenBoundsCheck` (soundness and tightness of the two tiers);
`SizeBoundsReport`, `SizeZ3Report`, `SizeZ3Drilldown` (distributions and per-program drilldown).

### 13.5 Spatial analysis suites

| Suite | What |
|---|---|
| `SpatialTypeCheck` | Per-length soundness of `SpatialTypes.infer` on closed corpus instances, both projections inside the z3 bounds. |
| `SpillSoundness` | The spill/tracked disjointness repair and the class/`MaxLen` caps, per constructor. |
| `SpatialShapeCheck` | The shape domain and the reduced product, with a delta-debugger reporting minimal witnesses. |
| `SpatialSoundnessHunt` | The adversarial net: sweeps over all constructors with nested binders, an interprocedural table, and non-exact declared inputs. |
| `CornerstoneTypes` | Declared-type inference on the cornerstone programs. |
| `SpatialLawCheck` / `SpatialLawsCheck` | The γ layer (extensivity, adjunction, simulation squares, measured incompleteness) and law hygiene (a law can never widen; assumed evidence stays out of certificates). |
| `SpatialAnalysisCheck` | The decorated traversal: root agreement, scaling, reducer termination/idempotence, positional identity. |
| `SpatialFactsCheck` | `E_d`/`K_d`, fibre envelopes, `trieNodes` against `ITrie.prefixCount`, the rest-chain bound as `Σ K_i`. |
| `SpatialFrontierCheck` | The frontier summary against hand-derived `Q`/`A`/`J`, and its exactness over geometric ladders. |
| `SpatialDemandCheck` | The forced-cursor-node count against the four counterexamples to the per-operator sum. |
| `SpatialSemanticsCheck` | Differential agreement of the event semantics with the counted executions of all four backends on every constructor (1148 cases), the corpus, and the cornerstones. |
| `DeltaIRCheck` | Variance table, accepted/rejected/unsupported components, naive vs delta round-for-round, the step equation, and replayable premises. |
| `SpatialDomainCheck` | γ∘α, join/meet/leq soundness on the finite universe, exactness of every operation, survival past the shape caps, named widenings, and invariance under prior analyses. |
| `ProofTraceCheck` | Every residual node's trace replays to its body; nine mutations (matcher, side condition, endpoint, dependency, cycle, identity without a no-op, marker as obligation) fail the checker. |
| `AlternativesCheck` | One fixture, seven alternatives with pairwise different certified cost and zero executor events during exploration; traces replay; certificates contain every executor's counted run; hash-consing, subsumption, widening and determinism; the GROUND law set equals the registry's. |
| `ParetoCheck` | Fusion / sharing / prefix-range / call-composition / recursion fixtures under six objectives — deterministic, every removal replayed in-process and by `check_selection.py`, the objective changes the choice, dominance never wins with an infinite bound, uncertified or open-closure candidates are NOT-ADMITTED, three forgeries fail both replays. |
| `DecisionsCheck` | Eight cases in five families — every selected alternative certified and closed, every counted run inside its certificate, at least one DIFFERENTIATED case per family, no CONTRADICTED case; writes decision artifacts through `ArtifactSink` and replays them with `check_selection.py`. |
| `MutationGates` | For each mutation, one assertion passes without it and fails with it; the two script-level mutations (injected open entry, forged coverage) re-run; an adversarial family (depth × width × aliasing × prefix overlap, fixed seed) keeps every counted run inside its certificate. |
| `Puzzle15Check` | The puzzle15 stress theorem — invariants of the MORKL encoding checked against `Zippy.Puzzle15` (Lean) and the reference BFS; one expansion priced under two value and two symbolic declarations on four backends; counted runs inside, result sizes under the proved `4·|frontier|`, committed thresholds (`proofs/puzzle15/THRESHOLDS.tsv`), and a certificate-justified backend choice; writes `proofs/puzzle15/` through `ArtifactSink`. |
| `CrossFunctionCostCheck` | Calls answered by parametric summaries (changing path arguments, reuse, correlated results, range of a call, calls below binders) and mutual recursion priced as the IR's simultaneous system against the solver's counted rounds. |
| `SpatialTransferDump` | Writes the independent checker's inputs (`proofs/spatial/out/`): every exact-tier transfer over the small universe and the pricing's containment rows. |
| `SpatialCostCheck` | Exhaustive small-model containment for every constructor on all four backends, summarized declarations, the randomized hunt, the two permanent zipper regressions, per-cell fibres, deterministic derivations, and no evaluation. |
| `SpatialEventsCheck` | The event vocabulary (every event has an emitter and exactly one component), hand-computed hook counts per executor, and calibration on the corpus and cornerstone optimized bodies, cold versus warm literals. |
| `SpatialScaleCheck` | `ProductRequirement` (the width/error/slope tiers) and correlated generator families over geometric ladders; soundness/finiteness is the gate and every tier statistic is reported per channel, with no ledger of excused rows. |
| `SpatialCheckCheck` | The three-way checker result, re-validated witnesses, and the measured incompleteness. |
| `SpatialRecursionCheck` | Depth bounds, splicing hygiene, every `NoBound` reason. |
| `SpatialElimination` | `eliminate`/`eliminateIn` fire where the syntactic law cannot, and never inside a `Call`. |
| `SpatialPipelineCheck` / `SpatialAcceptance` | The ordinary entry point end to end, and the per-cornerstone precision budget. |

### 13.6 Benchmarks and census

`TrieBench`, `GraphBench`, `ZipperScaleBench`, `RecursionLoweringBench`, `ExecutorOverheadBench`
(generate [BENCHMARKS.md](BENCHMARKS.md)); `CorpusRuntimes` (per-program timings);
`ProgramExpressivity` (generates the corpus), `ProgramStats`, `FuzzerTest`.

### 13.7 Guiding examples

| Example | Where |
|---|---|
| Aunt query | `AuntQuery` (`src/test/scala/MORKL.scala`), `ExAuntMetta` (`Examples.scala`) |
| Datalog TC (naive + semi-naive) | `ExDatalog` (`Examples.scala`), `DatalogShowTest`, `datalog-morkl.txt`. Naive ≡ semi-naive is certified round-for-round by `terminating/seminaive_correct.smt2` (O13) — GIVEN additivity of the join operator, `J(X ∪ Y) = J(X) ∪ J(Y)`. There is no semi-naive transformation in this compiler, so that side condition is on the author of the semi-naive program. |
| Game of Life | `GoL` + `ExGameOfLife` (`Examples.scala`) |
| N-queens | `NQueens` + `ExNQueens` (`Examples.scala`) |
| Sliding puzzle (8/15) | `Sliding` + `ExSlidingPuzzle` (`Examples.scala`) |
| NOAA temperature | `NOAA` + `ExNOAATemperature` (`Examples.scala`), `src/test/resources/noaa_slice.txt` |
| Unification, imperative encoding, graphs | `Unification`, `Imperative`, `Graphs`, `Routines` (`src/test/scala/MORKL.scala`) |

## 14. How a program flows

1. **Author** — `Syntax` builds a `Space` AST and a routine table (§1–2).
2. **Denote** — `eval` interprets it over `Set[PathValue]`; this is the oracle (§3).
3. **Choose an executor** — `evalT`, `evalI`, `exec`/`execT` via `transpile`, or `execZ` via
   `transpileZ` (§4–6). All are validated against `eval`.
4. **Optimize** — `Routine.optimized` runs the spatial hook then the `Lower` fixpoint; the compiled
   path runs `optimize(transpile(...))`. `lowerCalls` turns recognizable recursion into `Fixpoint`
   and leaves honest residuals (§7–8).
5. **Analyze** — size, length, spatial type, recursion depth and cost, from annotations only (§9).
6. **Supercompile** (optional) — `SC.drive` to a `Residual`, then op-graphs (§10).
7. **Verify** — `EquivPipeline`/`AgnosticPipeline`/`SmtDiff` emit egg + SMT certificates for the six
   cornerstones, discharged by egglog, z3 and Vampire (§11).
8. **Gate at scale** — the corpus suites (§12–13).

`eval` is the fixed point of trust: backends are checked against it, rewrites must preserve it,
intervals must contain it, and certificates are emitted only after a Scala gate confirms it.

## 14b. Cross-cutting infrastructure

| Component | File | What |
|---|---|---|
| `Tools` | `Tools.scala` | THE external-tool resolver: `$Z3` / `$VAMPIRE` / `$EGGLOG`, then `PATH`, then a short conventional-location list, then a NAMED error. `scripts/toolpath.sh` and `scripts/toolpath.py` are its `sh` and Python twins, reading the same variables and the same lists. No absolute tool path exists anywhere in the tree. |
| `RunEnvironment` | `RunEnvironment.scala` | Provenance for every generated number: cpu / cores / RAM / OS+kernel / JVM vendor+version / the JVM's actual flags / max heap / Scala version / git commit + dirty flag / UTC timestamp / the `Tuning` toggles. `markdown` for a table, `oneLine` for a CSV header. |
| `BenchmarkReport` | `RunEnvironment.scala` | THE writer for a generated results section: replaces the section between its markers and stamps the provenance block, instead of appending a new copy. |
| `Corpus` | `Corpus.scala` (test) | THE corpus loader, with ABSENT / STALE / UNREADABLE diagnosed separately and the regeneration command in every message. Twenty test files used to open the file themselves. |
| `scripts/check_references.py` | | CI: every markdown link and every file-shaped token in the tree must resolve. |
| `TraversalTotality` | `TraversalTotality.scala` (test) | CI: every generic term traversal (`collect`, `subs`, `freeMentions`, `freeRefs`, `SizeZ3.children`) must see a marker in EVERY subterm position of EVERY `Space` constructor. |

## 15. Artifacts & data

| Artifact | What |
|---|---|
| `corpus_1000.txt` / `.ser` | 1000 fuzzed programs (text source of truth + binary accelerator), produced by `ProgramExpressivity`. Schema drift trips the STALE guards. `corpus_runtimes.csv` is the derived timing table. |
| [BENCHMARKS.md](BENCHMARKS.md) | Steady-state timing tables per executor and domain, compile separated from run. Each section is REGENERATED IN PLACE between `<!-- BEGIN benchmark:<slug> -->` markers by `BenchmarkReport`, and carries the machine / toolchain / configuration it was produced on (`RunEnvironment`). |
| `proofs/` | The SMT-LIB obligation corpus (laws, `impl_*`, `threeway_*`, `refine_*`, `spatial/`, `spatial-semantic/`), each asserting the negated theorem. `proofs/STATUS.tsv` is the repo-wide PROVED/OPEN table; `proofs/laws/REGISTRY.tsv` + `MINED.tsv` index the law certificates. |
| `formal.egg`, `zipper-spec.egg`, `zipper-impl.egg` | The set-of-paths reference, the per-key movement calculus, and the eager `ITrie` model. `zipper-egg-tests/` holds the extracted preludes, the randomized differentials, and the observation matrix. |
| `proofs/pipeline/*.smt2`, `zipper-egg-tests/pipeline/*.egg` | Per-cornerstone equivalence artifacts emitted by `EquivPipelineTest`, audited by `audit_pipeline_markers.py` (whose `.smt2` vacuity detector is what caught the 18 degenerate instance obligations) and folded into the repo-wide table by `proofs/run.sh`. |
| `proofs/pipeline/fixpoint-gate/` | The OVER-STRONG-AXIOM gate for the first-class `Fixpoint` denotation: one TRUE fixpoint equality both provers discharge, three FALSE ones neither does. An axiomatisation strong enough to prove the false ones would make every enclosing obligation vacuous. |
| `build.log` | Append-only development journal (sessions, marker/registry counts, tightness deltas). Corrections are appended as ERRATA blocks, never edited in place. |
| `expressivity.csv`, `prog_matrix.tsv` | The expressivity census and the parent-position × child-type matrix, produced by `ProgramExpressivity` / `ProgramStats`. Both carry a `#` provenance header; `plot_expr.py`, `plot_expr2.py`, `plot_matrix.py` read them from the repo root and skip it. |
| `terminating/` | The recursion certificates. `REGISTRY.tsv` is the TOTAL map from the eleven lowering sites to their obligations (with OPEN and PROPERTY rows kept visible); `STATUS.tsv` carries both provers' verdicts. |
| `proofs/unbounded/` | TIER 3: schematic operator laws in TPTP/FOL, quantified over ALL spaces, paths and bodies — the claims tier-1 (`Lower.sizeBounds`, no object language) and tier-2 (`SizeZ3`, ground: one `(declare-const n<i> Int)` per AST node) cannot state at all. `_*.p` are axiom modules, the rest are one-theorem files, `negative/` holds FALSE controls that must not be provable. `run.sh` also runs a per-file vacuity probe and writes `STATUS.tsv`; index in `REGISTRY.tsv`; gated by `src/test/scala/UnboundedTier.scala`. Vampire only — see `run.sh`'s header for why there is no z3 twin. |
| `project/build.properties` | Pins the sbt version. Reproducing a number from `docs/BENCHMARKS.md` or `proofs/STATUS.tsv` means reproducing the toolchain, and the sbt launcher picks a version per project — leaving it unpinned makes the build a moving target the same way an unpinned prover would. |
| `build.sbt` | The build. `Test / fork := true` is load-bearing, not cosmetic — see `src/test/scala/Corpus.scala` for the classloader failure it prevents. `.jvmopts` sizes the sbt JVM itself. |
| Sibling docs | [ALGEBRA.md](ALGEBRA.md) (theory), [SUPERCOMPILER.md](SUPERCOMPILER.md), [design_plan.md](design_plan.md), [design_size_constraints.md](design_size_constraints.md), [design_spatial_lattice.md](design_spatial_lattice.md), [traps.md](traps.md), [guide.md](guide.md), [residuals.md](residuals.md), [fuzzer_zipper_draft.md](fuzzer_zipper_draft.md). |
