# Zippy Architecture Atlas

Zippy is an executable, machine-checked realization of the MORKL path-set algebra: programs are set-algebra expressions over *paths* (symbol sequences in a trie), and the repo verifies — with egglog, z3, and Vampire — that a family of increasingly-compiled executors all compute the same sets. Theory (algebra, operators, five case studies): [ALGEBRA.md](ALGEBRA.md). Positive supercompiler (driving/folding/whistle): [SUPERCOMPILER.md](SUPERCOMPILER.md). This atlas is the *code map* — every component, where it lives, and how the pieces feed each other — complementing the run recipes / CI-checker index in [README.md](../README.md), the invariants in [design_plan.md](design_plan.md), and the size-analysis redesign in [design_size_constraints.md](design_size_constraints.md).

Layers, from surface syntax down to verified artifacts:

```
Surface DSL (Syntax, itypes/otypes)
        │  builds
        ▼
Core AST + values  (Space / Path ; SpaceValue / PathValue ; Routine)
        │
        ├── eval ...................... reference denotational semantics (the ORACLE)
        │
        ├── transpile → RecursiveOpGraph → exec (SpaceValue) / execT (ITrie)   [op-graph backend]
        │
        ├── evalT (TreeMap Trie) / evalI (interned ITrie)  ................... [native trie backends]
        │
        └── transpileZ → SpaceZipper → execZ  ............................... [fused-cursor backend]

Optimizer:   Routine.optimized (Lower law fixpoint) ; optimize = push_out (LICM) + optimize_sharing (CSE)
Recursion:   lowerCalls → asFixpoint / lowerMutualSCC → Fixpoint subgraphs
Supercompiler: SC.drive (reduce/unfold/fold/whistle/generalize) → Residual → op-graphs
Size analysis: Lower.sizeBounds (tier-1) ⊇ SizeZ3.bounds (tier-2, z3 Optimize)
Verification: EquivPipeline / AgnosticPipeline / SmtDiff → egg + SMT certificates, all gated by eval
Corpus/fuzz: Fuzzer → SpaceFuzzer → corpus_1000 → differential test suites
```

Every executor is validated against `eval`; every optimizer rewrite must preserve `eval`; every equivalence certificate is gated by `eval` before a prover runs. `eval` being **total** over the language (guaranteed by the persistent binding contexts) makes it the universal reference.

---

## Table of contents

1. [Surface DSL & type language](#1-surface-dsl--type-language)
2. [Core values & AST](#2-core-values--ast)
3. [Reference evaluator (`eval`)](#3-reference-evaluator-eval)
4. [Operation-graph backend (transpile / exec / untranspile)](#4-operation-graph-backend-transpile--exec--untranspile)
5. [Trie backends (TreeMap `Trie` + `AlgebraicResult`; interned `ITrie` / `IntTrieOps`)](#5-trie-backends)
6. [Zipper executor & egg](#6-zipper-executor--egg)
7. [Optimizer (Lower laws; `push_out` LICM+splits; `optimize_sharing` CSE)](#7-optimizer)
8. [Recursion lowering (`lowerCalls` → Fixpoint)](#8-recursion-lowering)
9. [Size analysis (baseline `sizeBounds` + z3 tier)](#9-size-analysis)
10. [Supercompiler](#10-supercompiler)
11. [Equivalence / proof pipeline & tooling](#11-equivalence--proof-pipeline--tooling)
12. [Fuzzer & corpus](#12-fuzzer--corpus)
13. [Test suites (grouped)](#13-test-suites-grouped)
14. [How a program flows](#14-how-a-program-flows)
15. [Artifacts & data](#15-artifacts--data)

---

## 1. Surface DSL & type language

Construction surface for every Space/Path/Routine AST, plus the input/output type-inference passes that read those ASTs. Everything downstream (evaluators, laws, pipeline) analyzes trees produced here.

| Component | Path | Role & key defs | Interactions / invariants |
|---|---|---|---|
| **`Syntax`** | `MORKL.scala:2406-2522` | The surface DSL object — `given` String→Path conversions, operator extensions, string interpolators building all Space/Path/Routine ASTs across tests, examples, and the inference/lowering code itself. `given parse: Conversion[String,PathValue]` (dot-split), `given constant: Conversion[String,Path]`; Space ops `\/`=Union, `/\`=Intersection, `\`=Subtraction, `<|`=Restriction, `\|`=Raffination, `x`=Composition, `apply(p)`=Unwrap; `iter`/`iterk` (nested Iteration), `fold`, `head`, `on_empty`, `:=` (Routine definition); interpolators `S` (Mention), `P` (Deref), `R` (RoutinePtr), `ss`/`sP` (Singleton); `mod(rs: Routine*)` builds the `PartialFunction[RoutinePtr,Routine]` routine table. | THE construction layer — every AST `itypes`/`otypes` analyze and every `Lower` law transforms is produced here. `iter`/`iterk` uphold the head-arity invariant: each head `PathRef` is `.known(1)` and binder `Deref`s are rewritten via `subs`, so downstream guards (`headNarrowRewrite`'s `z.lengthHint==1`, `headEnc`'s `known(1)`) hold by construction. `x` on `Path` is overloaded (Concat vs Wrap), disambiguated by argument type. `mod(...)` feeds `Lower.inline`; `:=` turns a Call pattern + body into a `Routine`. Consumed broadly by `Examples.scala`, `PropertyTest.scala`, `FuzzerTest.scala`, benches, and the pipeline programs. |
| **`itypes`** | `MORKL.scala:2306-2366` | Input-type inference — recurses a Space AST to infer the set of input path-shapes it consumes, returned as a `SpaceValue` of `$`-prefixed type variables. `itypes(s): SpaceValue`, inner `recp(Path): PathValue` (Deref → `"$"+name`), `recs(Space): Set[PathValue]`. | Dual of `otypes` at `Wrap`/`Unwrap` — `Wrap(src,p)` IGNORES the prefix while `Unwrap(src,p)` COMPOSES it (inputs flow opposite to outputs). `Iteration` is load-bearing (builds `$symbol`/`$rest` vars, evals a synthesized set expression via `eval`+`Syntax`). Calls `eval` on synthesized `Union`/`Composition`/`Wrap` `Literal`s to normalize. `Fixpoint` case unimplemented (`???`). Called from tests (`src/test/scala/MORKL.scala:1219,1233`). |
| **`otypes`** | `MORKL.scala:2368-2404` | Output-type inference — dual of `itypes`; infers the set of output path-shapes a Space produces. `otypes(s): SpaceValue`, `recp`/`recs` mirroring `itypes`. | `Wrap(src,p)` PREPENDS the prefix, `Unwrap` IGNORES it; `Iteration` collapses to `recs(templates)`; `Fixpoint(init,rec,body)` = `recs(init) ∪ recs(body)` (unlike `itypes`, `otypes` DOES handle fixpoints). Called beside `itypes` in tests so the two form the input/output type pair of the same code. |

---

## 2. Core values & AST

The minimal domain vocabulary and the two ASTs (`Path` = one path, `Space` = a set of paths), plus runtime values, the binding environments that keep `eval` total, ordering/slicing, and the literal codec/interner used at the op-graph boundary.

### 2.1 Vocabulary, ASTs, and runtime values

| Component | Path | Role & key defs | Interactions / invariants |
|---|---|---|---|
| **`PathItem`** | `MORKL.scala:12` | `type PathItem = String` — one trie edge/symbol, no arity/kind. | Every path is a `List[PathItem]`; trie order = String order on items. Used by `PathValue`, `Path`, `LiteralCodec`. `SymbolConflict` exception lives adjacent (L14). |
| **`PathRef`** | `MORKL.scala:16-18` | Named path variable `PathRef(s)` with optional `lengthHint` (default -1); `known(length)` carries a size hint. | Resolved by `PathContext.resolve`; wrapped by `Path.Deref`. `_` is a sentinel throwaway: `bind` returns `this` unchanged and `grown` skips `_`, so binding to `_` discards. `transpile` emits `ExtractPathRef` keyed by `pr.s`. |
| **`PathValue`** | `MORKL.scala:54-61` | Concrete path `PathValue(items: List[PathItem])`; the trie-path runtime value. `prefixes`, `mostSpecific`, `show`. | The atom of `SpaceValue` (a `Set[PathValue]`). Ordered by `pathValueOrdering`. Boundary invariant: a `Path` always denotes exactly one `PathValue` (`eval` takes `.paths.head` for Singleton results). |
| **`Path`** | `MORKL.scala:20-52` | Path-expression enum: `Deref`, `Constant`, `Concat`, `GroundedPP`/`GroundedSP` (host fns); `factors`/`fromFactors`; `object Path: ZERO, first`. | Evaluated by `eval.recp`; transpiled to `ExtractPathRef`/`Constant`/`Concat` (Grounded* throw `NotImplementedError`); reconstructed by `untranspile`. `ZERO = Constant(PathValue(Nil))` is the empty path. `factors`/`first` feed the `Lower` optimizer. |
| **`SpaceValue`** | `MORKL.scala:186-189` | Evaluated value of a Space: `SpaceValue(paths: Set[PathValue])` — universal result type of `eval`/`exec`. | Returned by `eval`, stored in exec frame slots, interned by `LiteralStore`. Set operations implement Union/Intersection/Subtraction in both `eval` and `exec`. Value equality of the underlying Set is the fixpoint/iteration stop condition AND the CSE key. Unordered — canonical order imposed only by `sliceRange`. |
| **`Space`** | `MORKL.scala:133-183` | The central space-algebra AST: `Empty`, `Call`, `Mention`, `Singleton`, `Literal`, `Union`/`Intersection`/`Subtraction`/`Restriction`/`Raffination`/`Composition`, `Iteration`, `Fixpoint` (union-saturating least fixpoint), `Fold`, `Wrap`/`Unwrap`/`TailsUnion`/`TailsIntersection`, `GroundedPS`/`GroundedSS`, `Range`. | Consumed by `eval.recs` (reference semantics) and `transpile.recs` (op-graph lowering); reconstructed by `untranspile`. Semantic identities: `Wrap(src,p) == Composition(Singleton(p),src)`, `Raffination(x,y) == Subtraction(x,Restriction(x,y))`, `Range` == ordered trie-slice via `sliceRange`. Iteration/Fold/Tails skip headless paths and are TOTAL on empty input; Fold is a DETERMINISTIC left fold over head-groups sorted by `_._1.show`. |
| **`SpaceMention`** | `MORKL.scala:131` | Named space variable `SpaceMention(s)` — space-level analogue of `PathRef`. | Resolved by `SpaceContext.resolve`; used as `Mention`, iteration/fixpoint/fold binders, and `Routine.mentions`. `transpile` emits `ExtractSpaceMention` keyed by `sm.s`; the op-graph key is POSITIONAL by slot for CSE α-equivalence. `_` is throwaway. |
| **`RoutinePtr`** | `MORKL.scala:220` | Named handle to a `Routine`: `RoutinePtr(s)`; op-graph Call/Routine constant. | `Call` carries one; `eval` resolves via `rc: PartialFunction[RoutinePtr,Routine]`. `transpile` writes `r.name.s` into the node constant and mints derived pointers for lowered subgraphs (`_<symbol>`, `_fix`); `exec` resolves the callee by string via `index`. |
| **`Routine`** | `MORKL.scala:221-228` | Named parameterized space definition `Routine(name, refs, mentions, body)` — the compilation unit; `optimized` inlines callees then runs the `Lower` fixpoint. | The unit `eval` calls and `transpile` compiles. `optimized` first `Lower.inline`s non-self callees (self-inline guarded via `isDefinedAt=false`), then `all_forever(..., rules)` applies ~31 ordered rewrites (`ConstantOps`, `SizeEmpty`, `IterateSingleton_Deref`, … `SingletonRestriction_Unwrap`) to a fixpoint. Boundary contract: `optimized` preserves denotation (must `eval`-equal the input). |

### 2.2 Binding environments, ordering, serialization

| Component | Path | Role & key defs | Interactions / invariants |
|---|---|---|---|
| **`PathContext` family** | `MORKL.scala:68-96` | `PathRef → PathValue` environments: base + `Overlay` (lazy cons) + `Map` (flat) + `mixed(seed)` fuzzing context. `resolve`/`bind`/`grown`. | Threaded as `given pc` through `eval`. Iteration binds symbol via `grown`; Fold binds acc+symbol; Call installs a fresh `PathContextMap`. Design contract: ANY context can grow, so `eval` is TOTAL — the universal reference. `mixed(seed)` fabricates deterministic distinct values for unbound refs (fuzzer). |
| **`SpaceContext` family** | `MORKL.scala:100-129` | `SpaceMention → SpaceValue` environments: base + `Overlay` + `Map` + `constant`. | Threaded as `given sc` through `eval`. `grown` installs loop accumulators; Fixpoint rebinds `rec` to the current iterate each round and re-evals `body` until stabilisation. Carries a routine body's free space variables so `eval` is closed. |
| **`pathValueOrdering`** | `MORKL.scala:194-200` | `given Ordering[PathValue]` — canonical trie-native total order (String order on items, shorter-is-less on a shared prefix). | Single source of truth for ordered slicing: `sliceRange` sorts with it. EVERY backend slices `Range` by THIS order, so all executors agree — the cross-executor determinism invariant. NOT used for `SpaceValue` equality (that is Set equality). |
| **`RangeBounds` / `sliceRange`** | `MORKL.scala:205-218` | Fused First/Last window: `RangeBounds.normalize(size,start,end)` → clamped half-open `[lo,hi)`; `sliceRange(set,start,end)` applies it in canonical order. | Called by `eval` for `Space.Range` and by `exec`/`execT`/`transpileZ` for the "Range" node (parsing `lo,hi`). Short-circuits to the whole set for `[0,size)`. 1-based positive / from-end negative bounds. Both backends route Range through the same normalize+ordering, so `Range(x,k,k+1)` is exactly a singleton test everywhere. |
| **`LiteralCodec`** | `MORKL.scala:314-340` | Lossless textual codec for op-graph Literal/Constant strings: base64-per-item, memoized `decodeConst` cache. | `transpile.recp` emits Constant strings via `encodeConst`; `exec`/`untranspile` decode via `decodeConst`. Correctness invariant: plain `show`/`parse` round-trip is LOSSY for the empty path and dotted items, so those MUST be base64-escaped — `encodeConst` guards by testing `Syntax.parse(s)==p`. `decodeConst` is memoized because `exec` decodes per head inside iteration bodies. |
| **`Tuning`** | `MORKL.scala:353-356` | Ablation/benchmark toggles read once at class-load: `literalByRef`, `patriciaOps` (default ON). | `transpile.recs` branches on `literalByRef` (by-ref id vs serialized string for Literal nodes). `patriciaOps` gates IntMap-native ring ops (`IntTrieOps`). Read once so the branch is monomorphic after JIT; production never sets these. |
| **`LiteralStore`** | `MORKL.scala:358-373` | In-process interner carrying `Space.Literal` payloads BY REFERENCE: value-keyed `SpaceValue → "lit#<id>"`. | `transpile` stores `ref(sv)` when `literalByRef`; `exec`/`untranspile` resolve via `resolve` (`lit#` → `byId`, else legacy → `LiteralCodec.decode`). Rationale: serializing a large literal (e.g. a 16384-cell grid ≈ 226ms) and re-hashing it per CSE pass dominated compile time; by-ref gives O(1) transpile + O(1) CSE hashing while equal SpaceValues share an id so CSE still merges. |

---

## 3. Reference evaluator (`eval`)

**`eval`** — `src/main/scala/MORKL.scala:230-306`
Denotational reference interpreter `eval(s: Space)(using pc, sc, rc): SpaceValue` — the ground truth every executor is validated against. Inner `recp(x: Path): List[PathItem]` and `recs(x: Space): Set[PathValue]`; returns `SpaceValue(recs(s))`; default `given` environments make `eval(space)` callable with no environment.
- `recp` interprets Path (Deref → `pc.resolve`, Constant → items, Concat → `++`, Grounded* apply Scala fn). `recs` interprets every Space case directly on `Set[PathValue]`: set ops; Restriction = prefix filter; Composition = cartesian item-concat; Wrap via `Composition(Singleton(p),src)`; Unwrap = drop matching prefix; Tails* = head-group split; Iteration = group-by-head then eval templates with symbol/rest bound; Fixpoint = union-saturating loop until `nxt==cur`; Fold = deterministic left fold sorted by `head.show`; Raffination via Subtraction+Restriction; Range via `sliceRange`.
- **Call handling** resolves the `Routine` through `rc`, builds fresh contexts from parameter names zipped with evaluated args, and applies a TAIL-RECURSION fixpoint special-case: when the body is `Union(l, Call(same rp, same refs/mentions))` and all args are at their fixed point (`arg==eval(arg)`), it returns `eval(l)` (the base) instead of recursing — a termination guard for `r(a)=x(a) ∪ r(a)`.
- THE reference: the `PathContext` docstring declares `eval` TOTAL and "the universal reference"; `exec` comments note it "mirror[s] eval's recs exactly". `Fuzzer`, the size harnesses, and law/CSE checks all compare backend output against `eval(s)` for identical inputs; any divergence is a backend bug. Consumed by `exec` (oracle, indirectly), `Fuzzer.scala`, `SizeZ3Check`/`SizeZ3Report`, `Routine.optimized` law checks, and effectively every test suite.

---

## 4. Operation-graph backend (transpile / exec / untranspile)

`transpile` *lowers* a Space AST into a flat, coordinate-addressed `RecursiveOpGraph` of `Node`s; a stack-machine `exec` (over `SpaceValue`) or `execT` (over interned `ITrie`) walks it; `untranspile` inverts it back to AST. This is the compiled backend the optimizer (§7) rewrites and the corpus/overhead benches time.

### 4.1 IR

| Component | Path | Role & key defs | Interactions / invariants |
|---|---|---|---|
| **`Node`** | `MORKL.scala:375-377` | Flat op-graph instruction `Node[R](operation: String, constant: String, kind: "path"\|"space", inputs: Vector[R])`, parameterized by input-reference type. | Instantiated as `Node[(Int,Int)]` (coordinate = (level, index)). `operation` is the case-tag string executors switch on; `constant` carries the literal payload (Constant via `LiteralCodec`, Literal id via `LiteralStore`, Range `"lo,hi"`, routine/mention/ref name); `kind` selects the sget vs pget frame accessor; `map` remaps input coordinates (`optimize_sharing` rebuild). Invariant: input coordinates reference EARLIER-or-ancestor nodes only, never siblings. |
| **`RecursiveOpGraph`** | `MORKL.scala:378-402` | Nested op-graph container — a mutable scope with root `Node`, optional parent, and a buffer of flat `Node`s OR child subgraphs; coordinates (level, index). `store`, `lookup(pos)` (resolves across parent chain by level), `find(pred)` (search self then ancestors, visible-prefix only). | Built by `transpile` (root `Node("Routine",...)`; lowered Iteration/Fixpoint become child subgraphs retagged `Node("Iteration"\|"Fixpoint",...)`). Executed by `exec`/`execT` via `stack(stack.length-1-level)(index)`. **Structural invariant**: a scope's RESULT must be its LAST node (executors read `stack.top.last`); when the result is a non-last coordinate, `transpile` materializes a pass-through `Union(res,res)`, and `optimize_sharing` preserves it by PINNING the result node. |

### 4.2 Compiler / executors / decompiler

| Component | Path | Role & interactions |
|---|---|---|
| **`transpile`** | `MORKL.scala:404-522` | Lowers a `Routine`'s Space/Path AST into the flat/nested op-graph. First stores one `ExtractPathRef` per ref and one `ExtractSpaceMention` per mention so `recp`/`recs` resolve Deref/Mention via `g.find`. Lowers each Space case to a same-named `Node`. Iteration/Fixpoint → CHILD subgraphs via a recursive `transpile` of a synthetic `Routine`, root retagged. A raw single-mention union-saturating self-recursion `r(m)=m ∪ r(next(m))` at the body top level is rewritten to `Space.Fixpoint` before lowering (general recursion deferred to `lowerCalls`). Enforces the result-is-last invariant with a trailing pass-through `Union` when needed. Output feeds `exec`/`execT` (paired with an `index` map name→graph) and is input to `optimize`/`optimize_sharing`, `graphviz`/`mermaid`. |
| **`exec`** | `MORKL.scala:524-619` | `SpaceValue` stack-machine executor whose per-op behavior mirrors `eval.recs`, with empty-set short-circuits and reused frames. Walks `rog.nodes` writing each result into the current frame slot; addresses inputs via `sget`/`pget`. Space ops mirror `eval.recs` one-for-one but add `if a.isEmpty then empty` short-circuits. Call resolves the callee graph via `index(constant)`, allocates a child frame, recurses, reads `cstack.top.last`. Iteration/Fixpoint are child subgraphs pushing ONE reused frame (no per-iteration Array alloc); Iteration groups src by head (via `groupMap`), Fixpoint union-saturates until `nxt.paths==cur.paths`. A flat Iteration node throws `IllegalStateException`. Correctness contract: `exec` must produce the SAME `SpaceValue` as `eval`; the result read by Call is always `frame.last`. Entry point `runGraph` (§4.3). Also called directly in `test/scala/MORKL.scala`. |
| **`execT`** | `GraphExec.scala:9` | Trie-native op-graph interpreter walking a `RecursiveOpGraph` directly over interned `ITrie`/int-path values (the `ITrie` analog of `exec`). Same structure/short-circuits as `exec` but over `ITrie` ops, using cached `internConstStr`/`iLiteralStr`. **Iteration treats each child `(k,sub)` of the source trie as an already-grouped (head, tail-trie) pair — NO regrouping, unlike `exec`'s `groupMap`** — the native win, hot in deep n-queens nesting. Fixpoint faithfully mirrors `eval` (seed frame(0)=cur, union each iterate, stop on `nxt==cur`). Frame reuse in Iteration/Fixpoint avoids per-child/per-step Array alloc. Boundary invariant: mirrors `exec` exactly, so `runGraphT(g).toSpaceValue == runGraph(g)`. Entry point `runGraphT`. |
| **`untranspile`** | `MORKL.scala:622-682` | Inverse of `transpile` — reconstructs the Space/Path AST from an op-graph (round-trip / inspection oracle). Structurally parallels `exec` but writes AST nodes into frame slots. Iteration/Fixpoint push a frame, recurse, then recover the binder from `popped(0)` and body from `popped.last`, exactly inverting `transpile`'s lowering. The "Call" op is NOT implemented (throws) — reconstructs only intra-routine AST. `transpile ∘ untranspile` should recover an equivalent Space. |

### 4.3 Entry points and debug rendering

| Component | Path | Role & interactions |
|---|---|---|
| **`runGraph`** | `GraphExec.scala:103` | Entry point for `exec` (SpaceValue stack). Binds named inputs (`ExtractPathRef`→`refs(name)`, `ExtractSpaceMention`→`mentions(name)`) BY NAME (robust to optimizer reordering) into a fresh frame, calls `exec`, returns `stack.top.last`. The SpaceValue baseline: `runGraphT(g).toSpaceValue` must equal `runGraph(g)`. |
| **`runGraphT`** | `GraphExec.scala:91` | Trie-side sibling — binds `refs: Map[String,List[Int]]` / `mentions: Map[String,ITrie]` by name, runs `execT`, returns the result `ITrie`. Unbound Extract* slots stay null (caller must supply every input the graph reads). Callers convert via `.toSpaceValue` for cross-executor equality. Used by `FuzzerTest`, `RecursionLoweringBench`, `ExecutorOverheadBench`. |
| **`graphviz` / `graphviz_table` / `mermaid`** | `MORKL.scala:685-783` | Emit a `RecursiveOpGraph` as Graphviz DOT (record or clustered) or Mermaid flowchart for visual inspection of nested loop scopes. Reads coordinate refs via `g.lookup` to pick edge form; the dotted Iteration `f0`/`f1` edges visualize the loop-binder `Extract`s that `optimize_sharing`/`push_out` treat as pinned. Manual debugging only — no production/test callers. |

---

## 5. Trie backends

Two native trie evaluators that are exact-but-faster implementations of the `Set[List[PathItem]]` reference: `evalT` over a `TreeMap`-backed `Trie` (with the `AlgebraicResult` structural-sharing ring), and `evalI` over an interned `IntMap`/Patricia `ITrie`. Both mirror `eval.recs` case-for-case; the win is that Iteration reads each child sub-trie AS the tail for its head, with no flat-set regrouping.

### 5.1 TreeMap `Trie` + `AlgebraicResult`

| Component | Path | Role & key defs | Interactions / invariants |
|---|---|---|---|
| **`Trie`** | `Trie.scala` | Persistent path-trie backed by `TreeMap[PathItem,Trie]` — the trie-native representation of a MORKL space. `Trie(terminal, children)`; `empty`, `epsilon = {ε}`, `singleton`, `suffixClosure`, `range` (native ordered slice), `fromSpaceValue`/`toPaths`/`pathsInOrder`. | **Smart-construction invariant** — tries are canonical (no empty subtries), so `==` is exact set-equality and node identity (`eq`) is a valid cheap containment/sharing signal (exploited by the ring ops and by `evalT`/Fixpoint convergence). `children` in `TreeMap` String order → `pathsInOrder`/`range` walk without sorting. `epsilon` is the shared terminal leaf every singleton/wrap spine ends in. |
| **`Trie.AlgebraicResult` & set-ring ops** | `Trie.scala` | Per-node algebraic outcome `Empty \| Identity(mask) \| Bespoke(t)` plus the ring ops reporting it — the set-only analogue of pathmap's `AlgebraicResult<V>`, enabling structural sharing + early termination. `LEFT=1/RIGHT=2/BOTH=3`, `pick(r,a,b)`, `union`/`intersection`/`subtraction`/`restriction`/`raffination`/`composition` each = thin wrapper over an `*R` form that recurses on itself. | **STRUCTURAL SHARING** — when every child returns `Identity(LEFT)` and the terminal is unaffected, the node reports `Identity(LEFT)` and `pick` reuses argument `a` unchanged (zero allocation, whole subtree shared). **EARLY TERMINATION** — `a eq b` short-circuits at the top of every `*R` op (identical sub-tries, common under Fixpoint/Iteration, resolve without descent). Mask semantics: a SET bit is exactly true; soundness/completeness tested by `TrieAlgebra`; subtraction/raffination never set the RIGHT bit (non-commutative). SOLE place `AlgebraicResult` exists — `ITrie` deliberately relies instead on IntMap/Patricia `eq` short-circuits. |
| **`Trie` n-ary & prefix ops** | `Trie.scala` | `joinAll`/`meetAll` (simultaneous merges) and prefix/spine ops (`wrap`/`unwrap`/`tailsUnion`/`tailsIntersection`/`head`). | `joinAll` groups children by key across all inputs, unifying once per key (O(total nodes) vs O(k·\|result\|) pairwise); `meetAll` pivots on the SMALLEST branch. `evalT.Iteration` builds one sub-result per head child then `joinAll`s them — no flat-set regrouping. These bypass `AlgebraicResult` (build fresh nodes) but honor the canonical invariant by storing only nonEmpty children. |
| **`Zipper` (read zipper)** | `Trie.scala` | Read zipper into a `Trie` — focus node + breadcrumb trail; the imperative walk primitive. | `descend(k)` pushes a `Crumb` capturing parent terminal+children so `ascend` rebuilds the parent exactly (lossless persistent zipper). Upholds `Trie`'s canonical invariant on ascend. Best-effort primitive; not called within `evalT`/`evalI`. |
| **`pathItemsT`** | `Trie.scala` | Resolve a `Path` AST node to concrete `List[PathItem]` within `evalT`'s contexts. `GroundedSP` recurses into `evalT` then crosses to `SpaceValue`. | Consumed by `evalT` (Singleton/Wrap/Unwrap/GroundedPS/Fold/Call binding). |
| **`literalTrie` cache** | `Trie.scala:410-414` | Identity-keyed (`IdentityHashMap`) memoization of `SpaceValue Literal → Trie` so stable literal tables (n-queens add/sub/upto) convert once. Mirrors `ITrie`'s `iLiteral` cache. | Consumed by `evalT` for `Space.Literal`. |
| **`evalT`** | `Trie.scala:416` | Direct recursive evaluator of a Space over the `Trie` — native counterpart of `eval`. | Dispatches every Space case to a native `Trie` op. vs `eval`: keeps everything in the trie (Iteration reads each child sub-trie AS the tail, no regrouping); only `GroundedPS`/`GroundedSS` and `pathItemsT.GroundedSP` cross the `SpaceValue` boundary. Space mentions resolve through an immutable `Map[SpaceMention,Trie]`. Fixpoint exploits `AlgebraicResult` sharing — `nxt eq cur` is the common convergence signal, checked before structural `==`. Documented eager/no-short-circuit for a fair comparison against the dataflow op-graph executor. Compared against `eval` by the fuzzer/benches/`TrieTest`. |

### 5.2 Interned `ITrie` / `IntTrieOps`

| Component | Path | Role & key defs | Interactions / invariants |
|---|---|---|---|
| **`Interner`** | `IntTrie.scala:9` | Global O(1) bidirectional interner `PathItem ↔ Int` giving `ITrie` stable process-wide integer keys. | Global because O(1) amortized and stable per process — the same symbol maps to the same int across all `ITrie`s, so set ops compare pure ints and never touch `PathItem`. Un-interning happens ONLY at the `toSpaceValue`/`toPaths` boundary and when Iteration/Fold need a head as a `PathValue`. |
| **`ITrie`** | `IntTrie.scala:31` | Persistent path-trie keyed by interned `Int`, backed by `IntMap` (big-endian Patricia). Ring ops ride IntMap/Patricia structural merges. `union`/`intersection`/`subtraction`, `joinAll`/`meetAll`, `wrap`/`unwrap`, `composition`, `restriction`, `raffination = subtraction(x, restriction(x,y))`, `range`, `prune`. | **Two code paths per op**, selected by `Tuning.patriciaOps`: TRUE → native `IntTrieOps` Patricia merge with `a eq b` fast-path; FALSE → `IntMap.unionWith`/`intersectionWith` callbacks + `prune`. Both keep the canonical no-empty-subtrie invariant. Unlike `Trie`, does NOT use `AlgebraicResult` — sharing/early-termination comes from IntMap structure and `eq` short-circuits. `IntMap` chosen because `unionWith`/`intersectionWith` are O(n+m) structural callbacks that line up with the ring. |
| **`evalI` + `pathItemsI` + literal caches** | `IntTrie.scala:207 / 199 / 182-197` | Direct evaluator over `ITrie`, plus interned-path resolution and string-keyed literal/constant decode caches for the graph executor. | Same structure as `evalT` but every op is on `ITrie` and constants are interned once at singleton/wrap construction; NO `PathItem` touched during evaluation (except grounded host fns + Iteration/Fold heads). Fixpoint uses structural `==` convergence (no `AlgebraicResult` `eq` guarantee). The string caches (`iLiteralStr`/`internConstStr`) let the op-graph executor decode each distinct serialized constant exactly once — the reason `execT` need not be slower than `evalI`. |
| **`IntTrieOps`** | `IntTrieOps.scala` | Native single-descent Patricia merges of `IntMap[ITrie]` children maps — `unionTries`/`intersectTries`/`diffTries`/`restrictTries` with `eq` short-circuits. | Lives in `package scala.collection.immutable` specifically to see IntMap's package-private Patricia internals (`Bin`/`Tip`/`Nil`), enabling single SIMULTANEOUS descents over both tries (no per-key get+updated round-trips). EARLY TERMINATION on `a eq b` at every op. At a matched leaf delegates to the `ITrie`-level op, then `keep`/`binPrune` enforce the canonical no-empty-subtrie invariant. Called by `ITrie` ops when `Tuning.patriciaOps` is true. |

---

## 6. Zipper executor & egg

The third evaluation paradigm: a Space is lifted into a **fused cursor** (`SpaceZipper`) whose local set-algebra is navigated in O(1) per layer and materialized with a single DFS; control-flow ops route through `evalI`. `ZipperEgg` transpiles the cursor into egglog term languages so an external prover can certify the fused cursor denotes exactly what `execZ` computes.

| Component | Path | Role & key defs | Interactions / invariants |
|---|---|---|---|
| **`SpaceZipper`** | `Zipper.scala:27-140` | Lazy cursor over an interned-int trie — a virtual, fused trie of set-algebra operators navigable in O(1) per layer (`terminal`/`children`/`descend`), with a single-DFS `materialize`. `Lit(t)`, smart ctors `union`/`intersection`/`subtraction` implementing `x∪x=x`, `x∩x=x`, `x\x=∅`; virtual cursors `Union`/`Intersection`/`Subtraction`/`Composition`/`Prefix`/`RestrictionNode`/`TailsUnion`/`TailsIntersection`; `sameSpace` referential-identity short-circuit. | `descend`/`children` compose operands per the trie spec WITHOUT re-descending shared branches (`Union.children = a.children.unionWith(b.children, union)`, etc.). Identity laws enforced by `sameSpace` pointer test (never a structural walk), preserving constant-time movement. `materialize` is the single deforested DFS turning the cursor tree into one `ITrie` for `execZ`. Invariants `ZipperEgg` later certifies in egglog: absent vocab key descends to empty (`IsEmpty`); `Ascend∘Descend = id`. |
| **`transpileZ`** | `Zipper.scala:145-173` | Lift a Space program into a fused `SpaceZipper` — local set-algebra becomes virtual cursors; control-flow / positional ops delegate to `evalI` and are re-lifted. | `Union`/`Intersection`/… → the matching smart ctor; `Mention(m)` → `traversal(ic(m))` so two mentions of the same variable produce two `Lit` cursors over the SAME trie object → `sameSpace` short-circuits. `Range` → `traversal(ITrie.range(materialize(...),lo,hi))`. `Iteration` and the catch-all (Call/Fixpoint/Fold/Grounded*) → `traversal(evalI(other))` — control-flow is NOT a local trie op, so `execZ ≈ evalI` there (native Iteration fusion regressed wide sources). |
| **`execZ`** | `Zipper.scala:176-179` | Public zipper executor — `SpaceZipper.materialize(transpileZ(s))`. Takes a `Space` (not a `RecursiveOpGraph`). | Wins by fusion when an outer operator prunes inner bodies, else falls back to `evalI` parity. Benches assert `execZ(s) == evalI(s) == eval(s)` (`RecursionLoweringBench`, `ExecutorOverheadBench`, `ZipperScaleBench`). Its result trie also gates the egg proofs (`EquivPipelineTest` stage 2 checks `materialize(zProg).toSpaceValue == reference` before emitting). |
| **`ZipperEgg`** | `ZipperEgg.scala` | Transpile a `SpaceZipper` into egglog term languages (denotational movement `Z` and recursive-implementation `Tr`) and build self-contained coincidence-check programs certifying the fused zipper equals what `execZ` computed. `eggOfTrie`/`eggOf` (movement vocab), `trOfITrie`/`implOf` (impl vocab), `implCoincidenceProgram`, `coincidenceProgram`/`coincidenceProgramRaw` (movement-only certificate: `TermAt` at every member/non-member cursor path, absent-key `IsEmpty`, `Ascend∘Descend=id`, WITHOUT materialize), `keysOf`. | `(z=transpileZ(s), result=execZ/materialize(z))` → `eggOf(z)+keysOf(z)+result` feed `coincidenceProgramRaw`, which proves the VIRTUAL cursor denotes exactly `execZ`'s set purely by descent, never materializing. `implOf(z)+trOfITrie(result)` feed `implCoincidenceProgram`, certifying the Scala `ITrie`/materialize recursion and the egglog model coincide. Vocabulary invariant: child keys are the SAME interned ints the trie uses. Consumed by `EquivPipeline` (`eggOfTrie`, `trOfITrie`), `ZipperEggTest`, and `EquivPipelineTest` stage 2 (produces `zipper-egg-tests/pipeline/<name>-zipper.egg`). |

---

## 7. Optimizer

Two cooperating layers. **`Routine.optimized`** runs the source-level `Lower` law set (a large ordered list applied to a structural fixpoint by `all_forever`). **`optimize`** runs the op-graph pipeline — `push_out` (LICM + product-splitting) alternated with `optimize_sharing` (CSE) to a structural fixpoint. Every pass is semantics-preserving, so a budget-limited early stop still returns a correct graph.

### 7.1 Op-graph optimizer

| Component | Path | Role & interactions |
|---|---|---|
| **`optimize`** | `MORKL.scala:1361-1378` | Alternate `push_out` (LICM) and `optimize_sharing` (CSE) to a structural fixpoint, bounded by a `Deadline`, instrumented by a `Profiler`. Per round `push_out` runs FIRST (may perform one split, creating a parent `Union` and `Union(x,x)` pass-throughs), then `optimize_sharing` normalizes (collapsing those `Union(x,x)`, merging α-equivalent loops); the next round's `push_out` sees the freshly exposed parent `Union` and splits again. **This alternation is exactly what fully eliminates products** — each round peels one invariant subterm/inner-loop out of an enclosing loop; iteration continues until `structuralHash` is stable. Used by `Supercompiler.lower` (production backend lowering) and widely by tests/benches. |
| **`push_out`** | `MORKL.scala:870-1087` | Loop-invariant code motion over the iteration-subgraph tree for flat nodes AND whole subgraphs, plus union/composition splits with headed-guard synthesis that peel inner loops out of enclosing product loops. Re-parents each node/subgraph to its earliest legal (deepest-dependency) scope; only ONE split fires per invocation. Union split: `iter{a ∪ b_invariant}` (inside an enclosing loop) → the invariant `b` leaves the inner loop, surfacing a `Union` in the PARENT that the next round's `push_out` splits again (peeling one loop per round). Composition split: `iter{g·s} = g·iter{s}` guard-free (∅ annihilates). Boundary invariant: every move is a hoist-or-stay, never a sink (semantics-preserving). Coordinate-free (global ids) until final linearization — why re-parenting across arbitrary depth stays well-formed. `GraphExecTest:150` asserts `loopNodes(push_out(g)) < loopNodes(g)`. |
| **`optimize_sharing`** | `MORKL.scala:786-867` | Global CSE by exact structural value numbering (hash-consing) over both flat nodes and whole iteration subgraphs, with an idempotence peephole and α-invariant loop merging. Duplicate node/subgraph coordinates are redirected to the first VISIBLE occurrence (ancestor-or-earlier, never a sibling). **Boundary invariant**: the last slot of every scope (the result) is PINNED — always materialized, never redirected — so executors' `.last` output is preserved; `Extract`s are never redirected (bindings). Consumes the `Union(x,x)` pass-throughs `push_out`'s splits leave behind and collapses them (interior `Union(x,x) ⇒ x`, not applied to a scope result). α-invariance: Iteration/Fixpoint root constant (binder NAME) dropped from key, so structurally identical loops over the same source merge. VN table is global across scopes. Used by `optimize`, and as the standalone fallback in `Supercompiler.lower` when `optimize` throws. |

### 7.2 Optimizer support & source-level rewrite infrastructure

| Component | Path | Role & interactions |
|---|---|---|
| **`structuralHash` / `wellFormed` / `optimizedAway`** | `MORKL.scala:1331-1389` | Cheap structural fingerprint for fixpoint convergence (`optimize`); coordinate well-formedness checker for assertions (`GraphExecTest`); closed-constant detector (mirrored by `Supercompiler.compileTimeEvaluated`). Documented as checks, not fallbacks — passes are correct by construction. |
| **`Deadline` / `Profiler`** | `MORKL.scala:1099-1125` | Wall-clock compile budget fixpoint passes poll to stop gracefully, and a per-named-pass time+measure accountant separating compile from run cost. A single shared `Deadline` caps drive+transpile+optimize within `cfg.compileBudgetMs`; `Profiler` labels surface in `SCReport.phaseMillis`/`phaseImprovement`. Every pass being semantics-preserving makes a graceful early stop sound. |
| **`nodeCount` / `loopNodes`** | `MORKL.scala:1129-1136` | Structural size measures (total nodes; nodes resident inside loop subgraphs) feeding `Profiler.count`; `loopNodes` is `push_out`'s headline win (invariants now run once per outer entry). Distinct from `ITrie`/`Trie.nodeCount`. |
| **`all_forever`** | `MORKL.scala:1138-1141` | Apply a list of `Space=>Space` rewrites in order, repeating until structurally stable or budget expires. Uses case-class structural `==` as the fixpoint test. Caller must supply confluent/terminating rewrites. The general driver behind repeated algebraic simplification and `inlineCalls`. |
| **`inlineCalls`** | `MORKL.scala:1150-1151` | Splice every Call whose target is in `index` (args substituted for params) to a fixed point — the source-level "expand functions into the graph" step. Precondition: `index` must contain only non-(mutually-)recursive routines; self-recursion is instead lowered to `Fixpoint`. |
| **`collect` / `subs`** | `MORKL.scala:1457-1531` | Generic collecting fold and pre/post substitution over the Space/Path ADT — the substrate every `Lower` law and recursion-lowering pass is built on. `subs` recurses structurally, applying `spre`/`ppre` down (matched node replaced, not re-descended) then `spost`/`ppost` bottom-up. `collect` is read-only (guards prove a subterm loop-INVARIANT by finding no binder occurrence). `callees(s)` drives cycle detection. |

### 7.3 The `Lower` rewrite laws

All laws are `val`s built as `subs(_)(pre, post)` partial functions; the ordered list in `Routine.optimized` (L227) is the default pipeline. Many pairs are ping-pong-gated (each owns a disjoint case so they cannot oscillate). The mined laws carry `proofs/laws/law_*.smt2` certificates.

| Law | Path anchor | Role & key interaction / gate |
|---|---|---|
| **`AlgebraicIdentities`** | `MORKL.scala:1824-1855` | ~30 cheap structural identities (Empty absorption/units, idempotence, ε-concat units). O(1) syntactic layer complementing `SizeEmpty`'s analysis-level collapse. Empty Literal IS Empty; `Iteration(Empty)`/`Iteration(...,Empty) ⇒ Empty`. |
| **`ConstantOps`** | `MORKL.scala:1591-1598` | Best-effort constant folding: `try eval(op)` then replace with `Literal`. Broader/slower superset of `LiteralSpaceOps`; the `try/catch` is the totality gate (mentions/calls/grounded left alone). |
| **`LiteralSpaceOps`** | `MORKL.scala:1577-1589` | Constant-folds an op whose operands are all Literals by delegating to `eval`. Runs in `spost` (operands already folded). Wrap/Unwrap require a Constant prefix. |
| **`SizeEmpty`** | `MORKL.scala:1716-1718` | Analysis-level Empty propagation: any non-Empty space with `sizeBounds.hi==0` collapses to Empty. Subsumes chains of syntactic absorptions in ONE step. |
| **`IterUnion_Indep`** | `MORKL.scala:1759-1770` | The primary **product-buster**: hoists a loop-invariant union branch out of an iteration. Over a headless source `iter` is ∅, so a bare unguarded hoist would leak — gated by `provablyHeaded(src)` (bare) else `Composition(headedGuard(src), lhs)`. Ping-pong-gated against `IterSetOpMerge` (invariant bodies are exclusively this law's domain). Feeds `EpsGuard_Wrap → WrapMerge`. |
| **`IterComposition_Indep`** | `MORKL.scala:1775-1782` | Hoists a loop-invariant composition factor out of an iteration — sound with NO guard (composition distributes over the union of iterates). Subsumes `IterCompRight_Hoist`. |
| **`EpsGuard_Wrap`** | `MORKL.scala:1787-1789` | Commutes a ⊆{ε} guard factor into a Wrap: `g·(p×s) = p×(g·s)` when `g ⊆ {ε}`. Consumes the `headedGuard(src)·branch` factors from `IterUnion_Indep` and slides them past prefixes so `WrapMerge`/`push_out` can factor common prefixes. |
| **`IterWitness_TransposeSemiJoin`** | `MORKL.scala:2023-2025` | Makes a k-nested single-item iteration OUTPUT-SENSITIVE by narrowing its source with a materialized (k,ℓ)-transpose index of a loop-invariant witness. Unconditionally sound with NO shape assumptions (certificates `law_iter_transpose_semijoin.smt2` + `law_transpose_spec.smt2`). Ping-pong-gated by `hasGenTag(src0,"tj")`. Owns the case where an invariant statically-sized suffix follows the run. |
| **`IterWitness_HeadNarrow`** | `MORKL.scala:2103-2105` | Narrows EVERY level of a rest-chained nest by `Restriction(src_i, Head(E·z1·…))` when the innermost body is strict in `Unwrap(E, z1·…·zk)` and E genuinely varies. Sound per level (`law_iter_head_narrow.smt2`). Profitability guard `varies` (pre must contain a Deref); ping-pong-gated by `!hasGenTag(src0,"hn")`; DEFERS to the transpose law when an invariant sized suffix follows. |
| **`UnwrapPush`** | `MORKL.scala:2115-2119` | Pushes an Unwrap through union/intersection/subtraction (pointwise at `w·p`). Certificate `law_unwrap_push.smt2`. Exposes deeper Wrap/literal reductions. |
| **`WrapMerge`** | `MORKL.scala:2129-2135` | Merges equal-prefix wraps under one Wrap; annihilates incomparable-constant-prefix meets/differences. Certificates `law_wrap_merge.smt2` + `law_wrap_disjoint.smt2`. Terminal consumer of the `IterUnion_Indep → EpsGuard_Wrap` chain. |
| **`RestrictionPush`** | `MORKL.scala:2139-2144` | Pushes a Restriction through set ops and splits over a union of prefix sets. `law_restrict_push.smt2`. ∩/\ restrict only the left operand. |
| **`RaffinationPush`** | `MORKL.scala:2198-2203` | Pushes a Raffination through set ops; the prefix-union case NESTS (difference-by-prefix). `law_raff_push.smt2`. |
| **`RaffRestrictAlgebra`** | `MORKL.scala:2208-2215` | Collapses the raffination/restriction partition (opposite composition annihilates, idempotent, halves reunite to the subject). `law_raff_restrict_algebra.smt2`. Consumes pushed/split forms. |
| **`RestrictRaffWrapBoth`** | `MORKL.scala:2219-2224` | Descends a Restriction/Raffination below a COMMON wrap prefix. `law_restrict_wrap_both.smt2` + `law_raff_wrap_both.smt2`. |
| **`CompWrapAssoc`** | `MORKL.scala:2148-2150` | Slides a left Wrap out of a composition. `law_comp_wrap_assoc.smt2`. Pushes prefixes outward for `WrapMerge`. |
| **`CompAssocRight`** | `MORKL.scala:2154-2156` | Right-associates composition (strictly reduces left-spine depth, terminating). `law_comp_assoc.smt2`. Exposes left factors to `CompWrapAssoc`/`CompLitWraps`. |
| **`CompLitWraps`** | `MORKL.scala:2161-2164` | Trades a SMALL (≤4-path) left Literal in a composition for a Union of wraps. `law_comp_lit_wraps.smt2`. Bounded to avoid blowup; sorted by `show`. |
| **`IterSetOpMerge`** | `MORKL.scala:2272-2283` | Merges two SAME-SOURCE iterations under a set op: ∪ freely (bodies NOT clean), ∩/\ only under the `keyedBy` guard (keyed bodies make head-groups pairwise disjoint). `law_iter_merge.smt2`. Ping-pong-gated against `IterUnion_Indep`. |
| **`Concat_Path`** | `MORKL.scala:1600-1603` | Fuses two constant path factors (`ppost`). Canonicalizes constant prefixes so equal-prefix guards compare structurally. |
| **`SingletonConstPrefix_Wrap`** | `MORKL.scala:2176-2183` | Splits a singleton `const-prefix · deref-factors` into `Wrap(Singleton(varying), constPrefix)` (prefix hoistable). `law_wrap_set.smt2`. Ping-pong-gated against `SingletonSpaceOp_PathOp` (which MERGES fully-constant paths). |
| **`UnionChain_TailsU`** (NOT default) | `MORKL.scala:2260-2265` | Re-expresses an ≥4-ary union chain as `TailsUnion` of tagged branches for balanced merge. `law_union_chain_tailsu.smt2`. Explicitly OFF by default (per-eval tag overhead exceeds the balanced-merge gain at observed sizes). |
| **Unwrap algebra** (`Unwrap_Merge`, `Unwrap_Wrap`, `UnwrapConcat_Unwraps`) | `MORKL.scala:1791-1801, 2287-2293` | Split concat-prefix unwraps, merge adjacent constant unwraps (CONSTANT-ONLY so the splitter can't re-fire), and cancel/strip an unwrap against a just-applied wrap (incomparable ⇒ Empty). |
| **Misc singleton/iteration/range laws** | `MORKL.scala:1573-2193` | `SingletonConst_Literal`, `SingletonSpaceOp_PathOp`, `SingletonComposition_Wrap`, `SingletonRestriction_Unwrap` (uses the re-wrapping canonical form `Wrap(Unwrap(x,y),y)`), `ConcatSingleton_Iter`/`Wrap_Iter` (hoist a loop-invariant prefix, proven via `collect`), `Iter_Ident`, `Iter_Tails` (exact inverse of `TailsUnion_Iteration`), `TailsUnion_Singleton`, `Range_Singleton`, `IterCompRight_Hoist`. |
| **`TailsUnion_Iteration`** | `MORKL.scala:1534-1538` | Lowers `TailsUnion(src)` to the equivalent Iteration; inverse of `Iter_Tails`. |
| **`Literal_ConstantsUnion`** | `MORKL.scala:1540-1543` | Explodes a Literal into a Union of Singleton constants. Opposite direction of the constant-folding laws. |
| **`IterateLiteral_Union`** | `MORKL.scala:1545-1558` | Unrolls iteration over a Literal into a Union of body copies, one per DISTINCT head (rest bound to the head-group's tail-set) — mirrors `eval`'s `groupMap`. Corpus gate caught a wrong per-PATH unroll. |
| **`IterateSingleton_Deref`** | `MORKL.scala:1560-1571` | Iterating a single-item singleton: consumes the head, binds rest to the residual tail-set ({ε} for length-1, NOT ∅). |
| **`inline`** | `MORKL.scala:2295-2302` | Beta-reduces a `Space.Call` (context-parameterized on `PartialFunction[RoutinePtr,Routine]`). Feeds every other law once a call is inlined. Terminal element of the `Lower` object. |
| **`nonEmptyGuard` / `headedGuard`** | `MORKL.scala:1724-1733` | O(one path) guard factories producing a ⊆{ε} space that is {ε} iff x is non-empty / has ≥1 headed path. `headedGuard` (NOT `nonEmptyGuard`) is what `IterUnion_Indep` plants (x=={ε} runs zero iterations). Both are `provablyEpsSubset`, feeding `EpsGuard_Wrap → WrapMerge`. |
| **`provablyNonEmpty` / `provablyHeaded` / `provablyEpsSubset`** | `MORKL.scala:1710-1750` | Certainty predicates (defined by `sizeBounds`) used as one-sided law guards, keeping every gated law SOUND. `provablyHeaded` gates `IterUnion_Indep`; `provablyEpsSubset` gates `EpsGuard_Wrap`. |
| **`Reflect`** | `MORKL.scala:1392-1455` | Reify a Space AST into a `SpaceValue` (code-as-data). No callers in main/test; a metacircular bridge (program text as first-class Space data). Grounded* cases unimplemented. |

---

## 8. Recursion lowering

The source-level "link" step that turns recognizable self- and mutual-recursion into first-class `Space.Fixpoint`s so the now-acyclic routines can be inlined and transpiled Call-free. Orchestrated by `lowerCalls`, fed to `transpile` then `optimize`.

| Component | Path | Role & interactions |
|---|---|---|
| **`lowerCalls`** | `MORKL.scala:1295-1329` | The driver: rewrite recognizable self/mutual recursion to Fixpoints (`asFixpoint` per routine, then `lowerMutualSCC` per SCC), inline all now-acyclic routines into main + surviving recursive bodies, return `(topBody, residual)`. Output feeds `optimize(transpile(Routine(...topBody...)))`. Boundary invariant: genuinely un-lowerable recursion stays as residual Call routines (honest residual). |
| **`asFixpoint`** | `MORKL.scala:1162-1170` | Recognizes a union-saturating self-recursion with an IDENTITY base and rewrites to `Space.Fixpoint`, removing the self-call. Turns the datalog transitive/reachable shape into a first-class Fixpoint. The narrow exact case; runs BEFORE SCC detection so single-routine datalog loops never appear cyclic. |
| **`asFixpointGeneral`** | `MORKL.scala:1220-1264` | Lowers `BASE ∪ r(one mention transformed by T)` for arbitrary BASE/T into a two-tagged-state Fixpoint (`#arg#`/`#out#`), gated by a structural-monotonicity check (`monoIn`). Generalizes `asFixpoint`. Returns None (honest residual) on non-monotone base/T. |
| **`lowerMutualPassthrough`** | `MORKL.scala:1183-1217` | Lowers a mutually-recursive SCC of parameter-passthrough union-saturating relations to ONE tagged `Space.Fixpoint` (tag `#scc#<rp>` keeps arms separable), projecting each routine back out via Unwrap. Requires shared signature, unchanged params, structural monotonicity. |
| **`lowerMutualByElimination`** | `MORKL.scala:1269-1281` | Lowers a 2-routine arg-changing mutual SCC by Gaussian elimination (unfold one into the other → single self-recursion → `asFixpointGeneral`). Handles the arg-changing 2-cycles `lowerMutualPassthrough` rejects. |
| **`lowerMutualSCC`** | `MORKL.scala:1285-1286` | Thin dispatcher: `lowerMutualPassthrough` first, else `lowerMutualByElimination`; None ⇒ honest residual. |

---

## 9. Static analysis (size, path length, spatial types)

Three analyses over one design: a compositional tier-1 interval, a z3 tier that refines it, and
above both a length-indexed count domain whose two projections *are* the size and length analyses.
Above *that* sits the spatial type system proper (§9.6–§9.9): a reduced product of a bounded abstract
trie with the histogram, plus interprocedural recursion measures, a symbolic cost algebra, and the
γ/law layer that ties all of it to `eval`.

| Analysis | Tier-1 (compositional) | Tier-2 (z3) | Answer |
|---|---|---|---|
| **Space size** `\|eval(s)\|` | `Lower.sizeBounds` (§9.1) | `SizeZ3` (§9.2) | `SizeBounds(lo, loHeaded, hi)` |
| **Path length** `∀p ∈ eval(s). \|p\|` | `Lower.lenBounds` (§9.3) | `LenZ3` (§9.4) | `LenBounds(lo, hi)`; `lo > hi` = provably empty |
| **Spatial type** counts PER length | `SpatialTypes.infer` (§9.5) | — (meets the two above) | `SpaceType(byLen, rest, restLens)` |
| **Spatial type** shape × counts | `SpatialTyping.infer` (§9.6) | — | `SpatialType(Shape, SpaceType)` + `Vector[Fact]` |
| **Call-depth bound** | `SpatialRecursion` (§9.7) | — | `DepthBound` + `BoundedRecursion` residual |
| **Cost** (work/alloc/rounds) | `SpatialCost.analyze` (§9.8) | — | `Cost` over `Sym`, per backend |

A two-tier abstract interpretation of a Space's cardinality. **Tier-1** (`Lower.sizeBounds`) is a compositional interval abstraction `lo ≤ |eval(s)| ≤ hi` plus `loHeaded`, computed by per-constructor cardinality laws. **Tier-2** (`SizeZ3`) translates a term's per-node cardinality facts plus the saturated subset relation into a LINEAR z3 optimization problem, reading the root's interval off the objectives — tighter-everywhere / unsound-nowhere by construction (it asserts every tier-1 interval, so any sat optimum is equal-or-tighter). Design in [design_size_constraints.md](design_size_constraints.md), motivated by the tightness numbers in `build.log`.

### 9.1 Tier-1 baseline

**`Lower.sizeBounds` + `SizeBounds`** — `src/main/scala/MORKL.scala:1638-1706`
Compositional interval abstraction `SizeBounds(lo, loHeaded, hi)` via per-constructor transfer functions (each an exact set-cardinality law), with saturating arithmetic `satAdd`/`satMul`/`relu`. Transfers: union `[max(lo), l+r]`; intersection `[0, min hi]`; subtraction `[relu(lo_l-hi_r), hi_l]`; composition `[max(lo) if both≥1 else 0, hi_l·hi_r]` (concat injective for a fixed side, so `max` not `lo·lo`); iteration `[lo_body if loHeaded_src≥1 else 0, hi_src·hi_body]`; fixpoint `[lo_init, ∞)`. **Rest-mention environment refinement**: an iteration/fold binds `rest` to `SizeBounds(0,0,sb.hi)` (rest is ONE head-group of src). Unknowns (Mention/Call/Grounded) widen to `[0,∞)` — exactly what tier-2 narrows. `hi==0` IS the empty space (drives `SizeEmpty`). Consumed by `provablyNonEmpty`/`provablyHeaded` (now DEFINED by it), `IterUnion_Indep`, and by `SizeZ3` as per-node seeds + `K()` coefficients.

**`provablyNonEmpty` / `provablyHeaded` / `provablyEpsSubset`** — `src/main/scala/MORKL.scala:1710-1750` — see §7.3 (law guards).

### 9.2 Tier-2 (z3 Optimize)

**`SizeZ3` (object)** — `src/main/scala/SizeConstraints.scala:24`
Umbrella object; refines the tier-1 interval by encoding cardinality facts + the saturated ⊑ relation into a linear z3 problem. **Two-tier invariant**: every node's tier-1 baseline is asserted (`n≥lo`, `n≤hi`, `hd≥loHeaded`), so any sat optimum can only be equal-or-tighter. Fallback: on any failure path the untouched baseline is returned. The extra precision comes from facts the compositional baseline cannot see (the saturated subset lattice + inclusion-exclusion/partition equalities across siblings). The comment block enforces a linearity discipline (multiplicative bounds use baseline constant endpoints as coefficients, never variable*variable).

| Sub-component | Path | Role & interaction |
|---|---|---|
| **`Status` (enum)** | `SizeConstraints.scala:31` | Provenance tag: `Solved` / `ScopeLimited(reason)` / `NoSolver` / `SolverFailed(detail)`. Only `Solved` means a z3-tightened interval; every other case means the returned interval IS the baseline (reported, not hidden). `SizeZ3Report` buckets programs by it. |
| **`available` (probe)** | `SizeConstraints.scala:38` | Lazily-probed `z3 -version` check. Short-circuits `boundsWithStatus` to `NoSolver` when false; tests `assume` on it. |
| **`bounds` / `boundsWithStatus`** | `SizeConstraints.scala:44-46` | Public entry: baseline → (if solvable) α-rename → scope-check → encode → run z3 → parse → intersect with baseline. **Tightening join** clamps the z3 answer inside the baseline and enforces `0≤loHeaded≤lo≤hi`, so the result never widens. Consumed by `SizeZ3Check`, `SizeZ3Report`, `SizeZ3Drilldown`. |
| **`alphaRename`** | `SizeConstraints.scala:71` | Post-order rename of every binder to a unique fresh name so value-level hash-consing is scope-safe (reused binder names don't block encoding). Post-order guarantees no capture. |
| **`scopesProblem`** | `SizeConstraints.scala:111` | Gatekeeper: `Some(reason)` if hash-consing could conflate distinct bindings (duplicate binder names over different subtrees, out-of-scope/`_` references), else `None`. Ensures each hash-consed node stands for exactly one binding (adversarial min/max soundness). |
| **`children`** | `SizeConstraints.scala:145` | Structural sub-space accessor (drops binder metadata) for generic recursion; used by `scopesProblem`, `encode`'s post-order id closure. |
| ~~`groundFold`~~ | *removed* | A closed-subterm `eval` seed once supplied exact sizes here (and in `LenZ3`/`SpatialTypes`). **Removed on principle**: an abstract interpretation must propagate annotated types, never consult evaluation output — a bound obtained by running the program is an evaluation result, not an inferred one. All three analyses are now evaluation-free; tightness on closed terms comes from the transfers and the solver, and on open terms from declared input types. |
| **`encode` (core encoder)** | `SizeConstraints.scala:195` | Heart of tier-2: hash-cons every distinct subterm to a node with vars `n` (size) and `e ∈ {0,1}` (is-ε); assert baseline/ground seeds, the saturated ⊑ relation (transitivity + Intersection GLB / Union LUB / wrap-congruence rules), per-constructor cardinality laws (disjoint-cylinder exact sums, inclusion-exclusion via `meetOf`, partition equalities, LINEAR dual uppers for composition/iteration using `K(c)=baseline.hi` as the only multiplicative coefficient), and box-mode objectives (`minimize n_r`, `maximize n_r`, `minimize hdroot`). |
| **`encodeText`** | `SizeConstraints.scala:165` | Diagnostics accessor (`encode(s).text`); only consumer is `SizeZ3Drilldown`. |
| **`runZ3`** | `SizeConstraints.scala:357` | Writes SMT to a temp file, runs `z3 -T:<timeout>`, captures combined output, deletes the file. |
| **`parseObjectives`** | `SizeConstraints.scala:369` | Parses z3 box-mode output into `(minN, maxN, minHd)` (None = unbounded `oo`); any unexpected shape → None → baseline. Feeds the tightening join. |

### 9.3 Path-length tier-1

**`Lower.lenBounds` + `LenBounds`** — `src/main/scala/MORKL.scala`
Compositional interval `∀p ∈ eval(s): lo ≤ |p| ≤ hi` over every construct. The statement is
∀-quantified, so it is vacuously true of the empty space and `lo > hi` becomes a *composable*
provably-empty marker (`LenBounds.empty`, certified as the lattice ⊥ — see
[design_spatial_lattice.md](design_spatial_lattice.md)). Transfers: union hull; intersection
`max`/`min` (a crossing marks length-disjointness); composition/wrap add; unwrap/tails shift down;
restriction's lower bound comes from the prefix operand; iteration/fold take the body's bounds with
`rest ↦ tail lengths`. `pathLenBounds`/`pathItemLen` honour any `PathRef.lengthHint`.

### 9.4 Path-length tier-2

**`LenZ3`** — `src/main/scala/LengthConstraints.scala`
Per hash-consed node: `lo`/`hi`/`emp` variables plus a `define-fun` length **predicate** that keeps
the DISJUNCTIVE length set the interval hull loses (literals emit exact length sets, meets conjoin
child predicates, wrap/unwrap/tails shift them). Objectives run under `¬emp_root` because the bounds
are ∀-quantified over paths; `unsat` ⇒ provably empty ⇒ baseline. Predicates are macros, so nodes
over an expansion cap degrade to interval predicates (DAG sharing would otherwise blow up).
Reuses `SizeZ3`'s `alphaRename`/`scopesProblem`/`children`/`runZ3`/`Status`.

### 9.5 Spatial types (the unifying tier)

**`SpaceType` / `SpatialTypes` / `SpatialEnv` / `Ivl`** — `src/main/scala/SpatialTypes.scala`
Abstracts a Space as a **length-indexed count domain** — a count interval per path length, plus one
spill bucket — mapping an input environment (`SpaceMention → SpaceType`, `PathRef → LenBounds`,
routine table) to an output type. Its two projections are the analyses above: summing the classes
gives a size bound, the support hull gives a length bound, and `bestSize`/`bestLen` meet those with
the z3 tiers. Per-length counts express what neither can alone: a restriction annihilates classes
shorter than its shortest prefix, wrap shifts classes bijectively, raffination keeps short classes
exactly. A **relational layer** (`subsumes`, `partitionOf`) applies the certified subsumption /
partition / self-restriction laws so `x ∪ (x ∩ y)` is not double counted. `Fixpoint` uses Kleene
iteration with widening plus an upper-envelope post-fixpoint check.

**Status and scope of THIS component (deliberately stated).** Taken alone `SpaceType` is a
cardinality-and-length pass, *not* a shape domain and *not* a cost model: it tracks how many paths of
each length a term can denote, and can distinguish nothing else — two paths of the same length are
indistinguishable, so heads, prefixes, tags and values are invisible (`Unwrap(Literal({b}), "a")` is
`∅` but this component only says `{len 0: [0,1]}`). Bounds are concrete `Long`s, so there are no size
variables, cost expressions, recurrences or asymptotic orders. §9.6 adds the shape component that
supplies the missing structure, §9.8 the symbolic cost algebra; `SpaceType` remains the component that
still says something past the trie's depth/width caps, which is why the product keeps both.
**Consumer.** `eliminate`/`eliminateIn` are the one consumer: given a function and *abstract
annotations for its inputs*, they return a residual body plus the named facts that justify it,
deleting any subterm whose inferred type is `⊥`. That removes the whole computation feeding it, and
the ordinary `Lower` laws then propagate `Empty` upward. It is strictly stronger than the syntactic
`Lower.SizeEmpty` law (which only sees `sizeBounds.hi == 0`): the spatial tier also proves emptiness
from length-disjointness, restriction annihilation, and input annotations — on the 1000-program
corpus it fires on 133 programs and removes 2308 AST nodes with no annotations at all. The residual
agrees with the original on every input *satisfying* the annotations; with an empty environment that
is unconditional, with annotations it is a specialisation. It is **not** wired into the default
optimizer pipeline — a caller opts in — and the optimizer's own guards still call `Lower.sizeBounds`. The
caps (`MaxClasses = 24`, `MaxLen = 8192`) make precision input-size dependent by construction, and
once a type spills, `SpatialTypes.widen` folds any tracked class the spill range covers *into* the
spill — the invariant `at`/`size` depend on (see `SpillSoundness`, which exists because violating it
produced genuinely unsound per-length upper bounds, not merely loose ones).
The lattice/law corpus in [`proofs/spatial/`](../proofs/spatial) certifies the *algebra the transfers
assume*, not this implementation — see [design_spatial_lattice.md](design_spatial_lattice.md) for
the model-vs-code gaps.
Supersedes the partial `otypes`/`itypes` experiment (`MORKL.scala:2393/2455`, `???` at
TailsUnion/Fixpoint), which is left in place unused.

### 9.6 The spatial type system: shape × counts, reduced

**`Shape` / `Presence`** — `src/main/scala/SpatialShape.scala`
A **bounded abstract trie**, the component the histogram cannot express (`{a.0,a.1,a.2,a.3}` and
`{a.0,b.0,c.0,d.0}` are the same histogram but have 1 vs 4 head groups, and head grouping *is* the
semantics of `Iteration`). Carrier: `eps: Presence` (No/May/Must), `heads: SortedMap[PathItem, Shape]`,
`others: Ivl` (count of UNTRACKED heads — `others.hi == 0` is the closed-head-set case that licenses
exact head counts and absent-prefix proofs), and `otherTail: Option[Shape]` summarising the untracked
heads **per head**, not as their union. Finite by `MaxDepth = 4` levels (`capDepth`) and
`MaxHeads = 12` tracked keys per level (`mk` spills the excess into `others`/`otherTail`); both only
loosen. γ is the conjunction of those four channels and is written twice on purpose —
`Shape.contains` (self-contained, so the domain's own gate needs no other file) and
`SpatialGamma.gammaShape` — with an executable agreement test between the copies.

Transfers: `union`, `inter`, `sub`, `restrict`, raffination (as `x ∖ (x <| y)`), `wrap`/`wrapUnknown`,
`unwrap`/`unwrapUnknown`, `tailsUnion`, `tailsInter`, `comp`, `range`, plus `Iteration`/`Fold` analysed
**per head group** (the head symbol bound to that item, `rest` to that head's tail-set, one extra
weakened arm for the untracked groups) and `Fixpoint`/`Call` in `SpatialTyping`. Only these degrade to
⊤: `GroundedPS`/`GroundedSS`, a `Call` whose routine is absent or already on the stack, an `Unwrap` by
an unbounded-length path, a `Mention` with no declared type, a `Fixpoint` with no certified
post-fixpoint, and anything past the node budget. A written-before-the-code **per-operator may/must
table** heads the file: MUST is restored channel by channel with the argument that licenses it, and
each deliberately may-only entry says why. **Two orders, not one, and they are different operations:**
`Shape.union` is the transfer for `A ∪ B` (it keeps the left operand's MUST because `A ∪ B ⊇ A`, and it
ADDS the untracked counts) while `Shape.lub` is the lattice join (`γ(a) ∪ γ(b) ⊆ γ(lub a b)` — MAX of
the counts, no lower bound, ε demoted to May unless both agree). `Shape.leq` is the γ_may order;
`weaken` drops every MUST at every depth; `openCounts` is what survives an *unbounded union* of members
of one γ (ε-absence and closedness are union-closed, counts are not); `widenShape` is the Kleene
widening.

**`SpatialType` / `Fact` / `SpatialTyping`** — `src/main/scala/SpatialTypeSystem.scala`
`SpatialType = (Shape, SpaceType)` as a **reduced product**. `size`/`len`/`headCount` meet both
components, and the shape's head count bounds an iteration's group count. Measured on the review's own
nested rest-chained iteration: histogram alone `[0, 1024]`, `SpatialTypes.sizeOf` `[0, 1024]`, reduced
product `[4, 4]` against an actual size of 4.

**`reduce` is now genuinely bidirectional (review.md 5).** It was one rule (the shape's total capping
each class); it is now **eight named rules** iterated to a fixed point under `SpatialConfig.reduceRounds`:

| direction | rules | what they do |
|---|---|---|
| histogram → shape | `H1` `H2` `H3` `H4` | per-depth counts bound a fibre's untracked-head room (`H1`); zero/positive support at a depth forces `eps` to `No`/`Must` (`H2`); "nothing longer than `L`" prunes the untracked branches too, **materialising** an `otherTail` where there was none (`H3`); non-empty with a unique possible location forces that location (`H4`) |
| shape → histogram | `S1` `S2` `S3` `S4` | the shape's implied total caps each class (`S1`); classes outside the shape's length hull die (`S2`); a shape-forced class gets a lower bound (`S3`); an empty meet on the shared count/length hull is a **contradiction** (`S4`) |

A contradiction does **not** widen — it collapses to the explicit `SpatialType.bottom`, whose γ is
empty (it rejects even `∅`), which is what lets a caller tell "the value is the empty space" from
"your annotations are unsatisfiable". Executable-checked: the reducer reaches its fixed point in
**≤ 1 round** on 225 generated types (cap 4) and is idempotent on all of them; over 225 types × 128
values it tightened 71 types and **lost 0 γ-members**; `meet` over 48² pairs × 128 values produced
**0 false ⊥**. Both directions are exercised end to end — see §9.10 for the per-node claim and §9.7
for the `peel` case where the shape half recovers a length bound the histogram half abandons.

`Fact` is the **validated-proposition** API an optimizer should consume — `DefinitelyEmpty`,
`DefinitelyNonEmpty`, `MinimumCardinality`, `MaximumCardinality`, `AllPathsHaveAtLeast`,
`MaximumPathLength`, `ExactHeadSet`, `HeadSetWithin`, `MinimumHeadCount`, `MaximumHeadCount`,
`PrefixAbsent` — each bundling the conjunction its meaning needs, because the empty space's `len.lo`
is `INF` and a client reading it raw would "prove" three extractable items from nothing.
`PrefixAbsent` **is now emitted** (it was a public constructor `Fact.from` never produced — the
review's "dead promise"): 390 of 400 decorated corpus instances carry one.

**The naming trap is closed (review.md 1).** Full γ-membership is `accepts` (alias `gammaMember`); the
weak envelope is `withinEnvelope`; `satisfies` is **deleted**, not deprecated, because a deprecated
alias leaves the trap reachable. The envelope's gap is real and still measured — 237 non-members
admitted over 38,400 pairs — but **no dispatcher is built on it any more**:
`SpecializedRoutine.applicableTo`, `BoundedRecursion.applicableTo` and
`SpatialPipeline.GuardedRoutine.applicableTo` all decide with full γ, and `SpatialLawCheck` asserts
that the dispatcher rejects the exact witness the envelope admits.

`SpatialTyping.fixpoint` deserves its own note because it is where the two orders matter: the concrete
operator binds the recursive mention to the LAST iterate and returns the UNION of all of them, so the
chain ascends with `lub` over MAY-ONLY iterates (may-only is what makes `γ_may = γ`, so `leq` is the
right certificate *and* the body is analysed by transfers in the strong reading they are sound for) and
the accumulation is bounded by `openCounts` of the certified candidate.

### 9.7 Bounded recursion: summaries, a measure, a depth bound, a residual

**`SpatialRecursion`** — `src/main/scala/SpatialRecursion.scala`
Four pieces. (1) **Summaries** memoised by `Key(RoutinePtr, Args)` where `Args` carries the abstract
mention types and, per path parameter, either a constant value or a length interval; solved by a real
**worklist** (join, widen after 3 updates, ⊤ after 8, ⊤ past a key budget). The schedule is a
heuristic; what licenses the answer is the explicit **post-fixed-point certification** — re-deriving
every key's body under the final table must yield a type `⊑` the stored one. A table that fails to
certify is reported (`Summaries.certified = false`) and never used. Routine bodies are abstracted by
rewriting each `Call` into a placeholder mention bound to that call's summary and then calling
`SpatialTyping.infer` once, so no transfer logic is duplicated. (2) A **decreasing measure**
`μ(t) = t.len.hi` with two required checks: **M1** a *structural* witness that the recursive argument
drops ≥1 item (tails/unwrap-by-≥1/rest-mention of a loop over a syntactic subset), **M2** a *numeric*
drop `μ(a_{k+1}) ≤ μ(a_k) − 1` along the unrolled chain. (3) The **bound**: `maxCallDepth = k`, the
first level whose summary is provably empty. (4) **Residualisation** of levels `0…k−1` with every
spliced binder alpha-renamed fresh (so an argument mentioning a loop binder cannot be captured), the
level-`k` call replaced by `Empty`, wrapped in `BoundedRecursion` which carries its precondition as
data and answers `applicableTo`. Review.md's exact request lands: `maxLen 4` + one item per call ⇒
`maxCallDepth 4`, μ chain `4→3→2→1→0`, level-4 summary ⊥, Call-free residual, 17 nodes / 4 levels.
`DepthBound.NoBound` names its reason rather than silently returning ⊤.

**What the bidirectional reducer bought here.** `peel(m, p0) = heads(m) ∪ peel(p0, Unwrap(m, p0))`
with `p0` declared to carry **between one and three** items used to come back `NoBound`: the
histogram's variable-length `Unwrap` arm gives up (it still does — `SpatialTypes.infer` alone returns
`μ = ∞`), so M2 could not be shown. It is now **Bounded** at `maxCallDepth 4`, and the proof runs
entirely through the product: `lengthAnnotation(1,4)`'s histogram materialises a depth-≤4 trie out of
`Shape.top` (rule `H3`), `Shape.unwrapUnknown` shifts that trie down by `|p0|.lo = 1` levels — sound
because `Unwrap(s,p)` with `|p| = j` is a subset of the level-`j` tail-sets, i.e. `tailsUnion` iterated
`j` times, unioned over `j ∈ |p0|` — and the product's `len` meet reads the bound back off the shape.
The drop is always the **lower** end of `|p0|`, never the upper: `|p0| ∈ [2,3]` gives μ chain `4→2→0`
and depth 2. Checked three ways: the μ chain is asserted exactly, `eval` agrees with the residual on
7,500 inputs drawn from inside the precondition across five `|p0|` intervals (0 disagreements), and
`|p0| ∈ [0,3]` — a prefix that may be **empty**, so nothing decreases — still returns `NoBound` with
the M1 reason. The depth cap is not being misread as a length claim: `Shape.top.lens.hi = ∞` and ⊤
admits a path three times deeper than `MaxDepth`, both asserted.

### 9.8 Symbolic cost (cardinality is not cost)

**`Sym` / `BigO` / `Amount` / `Cost` / `Meas` / `CostModel` / `SetCost` / `TrieCost` / `Recurrence` /
`SpatialCost`** — `src/main/scala/SpatialCost.scala`
`Sym = Const | Var | Add | Mul | Pow | Max | Log | Inf`, normalised through a real polynomial normal
form (monomial → coefficient, atoms being vars/logs/symbolic powers/maxes), so like terms collect and
the form is idempotent. Every `Var` ranges over reals `≥ 2`, which is what makes the **syntactic**
`dominates(a,b)` test sound (monomial matching with coefficient budgets plus a `log₂ x ≤ x` trade —
that is what derives `N² ≥ N log N`). `Inf` is a genuine top used only where a quantity is unknowable,
never as a stand-in for "large". `BigO(expFactors, degree, logs)` compared lexicographically *is*
`2^N > N² > N log N > N > log N > 1`, so the distinctions review.md 3 says collapse to one `INF`
stay separate.

The analysed answer is a `Cost(work, alloc, rounds)` **vector per node** — elementary visits, paths or
trie nodes materialised, and loop head-groups / fixpoint rounds entered — parameterised by the spatial
facts (`Meas(size, len, heads)` read off `SpatialType`, never off `eval`). `CostModel` has two
instances that consume the *same* facts and disagree, which is what makes this a cost model rather
than a second size bound: measured `unwrap` set `work=n` / trie `work=1` (zipper focus, no rebuild),
`range` set `n² log n` / trie `n`, `restriction` set `n³` / trie `n²`, `union` set `n` / trie `n²`.
`Recurrence.solve`/`close` give linear recurrences closed forms instead of saturating, and a routine
with a §9.7 depth bound gets a closed cost.

**Four backends, and intervals rather than a bare worst case (review.md 2).** `Backend` is now
`Reference | Trie | Graph | Zipper`, each naming the executable it describes (`eval`, `evalI`, `execT`,
`execZ`) — one `TrieCost` formula can no longer stand for the materially different `execT` and `execZ`.
Every model returns a `CostInterval(lo, hi)`, so the generic lower endpoint (one dispatch, zero
allocations) is replaced by exact zero/identity values wherever `Shape` proves a fast path, and cold
construction is separated from warm execution by phase rather than folded into the symbolic expression.

**What is and is not established.** The per-operator constants remain a *model* of the interpreters,
read off the source — not measured constants and not proved. Executable-checked:
normalisation/idempotence, `dominates` against numeric evaluation (114 pairs × 60 valuations),
`bigO` monotone under `dominates`, the per-operator transfers, backend disagreement (300/300 corpus
programs), and monotonicity in both the symbolic valuation and the declared input type.

The tightness question the review said was *unanswerable* is now answered, and answered unevenly — see
§9.13 for the containment/slack tables against counted runtime events. Rank correlation
(Spearman ρ = 0.927 over 16 programs) is retained only as a **secondary trend metric**; it is no
longer the empirical case for the model.

### 9.9 The semantic layer and the law corpus

**`SpatialGamma`** — `src/main/scala/SpatialGamma.scala`
Makes review.md 6's law family *statable*: `gammaSpace` (the histogram, spill aggregate included),
`gammaShape` (**strong** — Must means the member really is there, `others.lo` is a real lower bound),
`gammaShapeMay` = strong γ of a total `weakenAll` (the may-only reading `Fact`/`headCount`/
`mayHavePrefix`/`isProvablyEmpty` consume), `gamma`/`gammaMay` on the product, `alpha`, `lubSpace`,
`leqShape`, and the operator table that drives the simulation squares. Both readings are reported
separately everywhere, because a transfer sound for one and not the other is not "nearly sound".
`lubShape` delegates to `Shape.lub` — one join, deliberately, since two spellings of a join is how the
order/transfer confusion got in. Contains no call to `eval`/`evalI`/`evalT`/`exec*`: γ is a predicate
on a value the caller already holds.

**The two orders now report WHY they said no, from one implementation** (review.md 4, second half).
`SpatialGamma.leqSpace` **is** `leqSpaceMask(a, b) == 0` and `Shape.leqStrong` **is**
`leqStrongMask(a, b, 32, full = false) == 0` — the masks are attribution, not a second order, and
`LeqSpaceWhy` / `LeqShapeWhy` name the bits. That is what let the incompleteness be *measured* instead
of guessed, and the measurement **refuted the review's named cause**: of the 202 residual false negatives
on the wide random pool, **150 are true negatives** (a member of `γ(a) ∖ γ(b)` exists, just outside the
finite universe — `leq` is right and `U` is too small), **52 are product interaction** (neither component
is contained; only the conjunction is, which no componentwise order can see), and **0 are avoidable**.
The review's hypothesis — the spill-vs-tracked length partition — scored **zero**, because it was fixed:
`canonSpace` normalises both sides (folding a single-length spill window into a tracked class, clamping
the ε class to one path) and `leqSpaceMask`'s window clause decomposes `a`'s window against the part of
it `b` neither tracks nor covers, instead of demanding `b` carry a window at all. Two consequences:
`leqSpace` is now **reflexive on spill-carrying types** (it was not, which the decorated analysis' "root
is never weaker than `infer`" law needed), and on universes that DECIDE containment both orders measure
**0 false negatives**. The price is measured too: `leqSpace` 109 → 166 ns/call on a 41%-spill pool
(1.53×) and 218 → 262 ns/call with no spill (1.20×), and it is reached on only 2.2% of `SpatialType.leq`
calls because the shape order rejects first — end to end `leq` costs 55 ns/call.

**`proofs/spatial-semantic/`** (20 obligations, generated by
`scripts/gen_spatial_semantic_obligations.py`, run by `proofs/spatial-semantic/run.sh`) — all 20
currently **PROVED** (z3 `unsat` on the negated theorem; vampire also refutes 11). These are
finite-first-order fragments of the *actual* carrier, so they are a genuine step past
`proofs/spatial/`, but they are still a model: no mechanical link generates the Scala from them. Nine
are deliberate **GROUND WITNESSES** — refutations that pin what the code does *not* license:
`gsem_within_not_containment` (`SpaceType.within` is an upper envelope, not γ-containment),
`gsem_join_not_lub` (`SpatialTypes.join` is the union transfer; design_spatial_lattice.md §2 calls it a
lub), `gsem_satisfies_weaker` (the dispatcher gate admits non-members), `gsem_l2_union_maxlo_unsound`,
`gsem_othertail_perhead_union`, `gsem_l2_tailsinter_may_unsound`, `gsem_l1_restrict_openkeys_unsound`.

### 9.10 One decorated analysis (review.md 4)

**`SpatialConfig` / `NodeId` / `NodeAnalysis` / `SpatialAnalysis`** — `src/main/scala/SpatialAnalysis.scala`

The cost pass used to re-run `SpatialTypes.infer` and `SpatialTyping.infer` at every subterm through
`histAt`/`shapeAt`/`typeAt`, which is quadratic; `FactBudget = 2000` capped the duplicate work without
making the architecture compositional. There is now **one** traversal. `SpatialTyping.goShape` takes a
`private[morkl] ShapeVisitor`; with `ShapeVisitor.Off` it is byte-for-byte the query `infer` always
ran, and with the recorder installed it becomes the decorated analysis. The visitor's return value
**replaces** the node's shape, which is how the parent transfer consumes the reduced child rather than
merely producing a tighter final projection — the part review.md 5 says a root-only reduction cannot do.

```scala
final case class NodeId(position: Vector[Int])                 // child-index path; "/" is the root
final case class SpatialAnalysis(root: SpatialType, nodes: Vector[NodeAnalysis], config, notes):
  val index: Map[NodeId, NodeAnalysis]                          // O(1), no re-inference
  def at(id): Option[NodeAnalysis];  def factsAt(id): Vector[Fact];  def rootFacts
  def occurrencesOf(s: Space): Vector[NodeAnalysis];  def provablyEmpty: Vector[NodeAnalysis]
```

Each node carries its `result`, the **binder environment it was analysed in**, its `observations` (one
per cause, so a loop body seen under several head groups keeps each environment and joins the
summaries) and its facts. The histogram half is compositional: each node is rebuilt over stub mentions
bound to the children's already-computed histograms and handed to `SpatialTypes.infer` — the owner of
the count transfers — as a one-node term. The operators whose count transfer is *not* compositional
(`Iteration`, `Fold`, `Fixpoint`) plus the root get a direct histogram query under an explicit
`histQueries` budget.

**Executable-checked.** Root agreement: on 23 probe terms the decorated root is `⊑ infer` on all
(strictly tighter on 1). Cost is not quadratic: 255 / 511 / 1023 nodes take 65.7 / 104.9 / 314.0 ms —
the last doubling costs **2.99×**, where quadratic would be ~4×. On 400 corpus instances: 10,227
decorated nodes (25.6 per term), differs from `infer` on 46, **bottom on 0**, root `≤ infer` on all,
and 4,352 closed decorated occurrences agree with `eval` with **0 violations**. Two occurrences of the
same AST object get distinct positional identities, and iterator bindings survive — both asserted.

**Honest limit, now much smaller (review.md 3, second half).** Every field of `SpatialConfig` is read
by a run, and the class comment names the reader. What changed: `shapeDepth`/`shapeWidth` are consumed
per analysis by `SpatialAnalysis.narrow` (`Shape.capDepth` + a width spill into `others`/`otherTail`) on
every shape the decorated traversal records and hands to its parent, so they are a real knob; `unroll`
and `summaryKeys` reach `SpatialRecursion.Limits` and `profileDepth`/`unrollDepth`/`unrollNodes`/
`prefixLength` reach `SpatialFacts.Config` through `SpatialAnnotations.limits`/`factConfig`, which are
now **projections of `config`** rather than separate fields — so narrowing the analysis can no longer
leave the two downstream stages on their defaults by accident; and `inline` was **deleted** rather than
left as decoration (`SpatialCost.Env` takes no budget argument, so `SpatialCost.MaxInline` has no
channel). `laws`/`lawQueries` are new and drive §9.15.

The residual caveat is one-directional and stated in the code: `Shape.MaxDepth`/`MaxHeads` are `val`s
of the **carrier**, initialised from `SpatialConfig.default`, because a `Shape` built under one cap is
joined and met with one built under another. So a per-analysis `shapeDepth`/`shapeWidth` can only
**narrow**; a value at or above the carrier's cap is a no-op and the analysis says so in its `notes`.

### 9.11 Derived facts backends can act on (review.md 7)

**`SpatialFacts`** — `src/main/scala/SpatialFacts.scala`
Projections of the existing carriers — **no new abstract domain**, and no `eval`/`exec*` reference.
Two quantities drive everything, `E_d` (paths with at least `d` items, read off the histogram) and
`K_d` (distinct length-`d` prefixes, read off the trie), reduced against each other by
`0 ≤ K_d ≤ E_d` and `E_d > 0 ⇒ K_d > 0`. On top: per-depth `DepthDegree` with pigeonhole
`minFiber`/`maxFiber` envelopes, `commonPrefix` + `canExtractEveryPath` (cardinality and path length
kept apart — `MinimumCardinality(3)` says three paths exist, `AllPathsHaveAtLeast(3)` says each path
supports three extractions, and only the latter removes three existence checks), `trieNodes` as the
**exact** identity `1 + Σ_{d≥1} K_d` instead of the sharing-blind `size × len`, a `RestChain`
recognizer whose nested-iterator bound is `Σ_{i=1..d} K_i` frames and `K_d` leaf invocations rather
than `K_1·…·K_d`, and a correlated-path overlay (`ItemPattern`/`PathPattern`/`PatternStratum`) that
refines a `SpatialType` without touching `Shape`. Candidates are the review's own ADT —
`SpatialSpecialization.TrieUnroll` / `ZipperPrefocus` / `GraphConstantFold`.

Where the two components disagree, `degreeAt` returns `Either[SpatialContradiction, DepthDegree]`
rather than repairing `lo > hi` by swapping or widening: an uninhabited contract must not silently
become an inhabited one.

### 9.12 The consumer-facing typechecker (review.md 1)

**`PathType` / `SpatialSignature` / `SpatialCheck`** — `src/main/scala/SpatialCheck.scala`
`Routine` had names, parameters and a body and nothing else; there was no signature and no
`checkRoutine`. Now there is, and **three different questions are kept apart by type**:

| question | entry point | guarantee |
|---|---|---|
| does this concrete space inhabit this type? | `SpatialCheck.value` | sound **and complete** for the carrier (full γ via `SpatialTyping.accepts`) |
| is this abstract type below that one? | `SpatialCheck.types` | three-way; sound, deliberately **incomplete** |
| does this routine meet its declared contract? | `SpatialCheck.checkRoutine` | `Proved` / `Refuted(witness)` / `Unknown(reason)` |

`Proved` may use sound abstract inclusion. **`Refuted` requires an actual witness** — a value in
`γ(inferred) \ γ(expected)` is an *abstract gap*, which may be an artifact of abstraction and is not
evidence the routine can produce it. Every other failed proof is `Unknown`. Executable-checked
(`SpatialCheckCheck`, 25 tests): over 1040 signature pairs the order holds on 84, 62 pairs are
γ-contained with `γ(a) ∩ U` inhabited, and the `leq` incompleteness on that pool is **10 of 62** (16.1%)
with **none becoming a type error**; a contradictory annotation reports `Unknown — VACUOUS` and names
the fix rather than "proving" anything; and the checker runs on a term whose grounded functions throw,
so no path evaluates its subject.

**The order mirror is no longer a second implementation (repaired this round).** `SpatialChannels`
explains a verdict channel by channel, and its histogram half restated `leqSpace`'s clauses. When
`leqSpace` was *completed* for the spill-vs-tracked partition (§9.9) the mirror kept rejecting pairs the
order now proves, and `SpatialCheckCheck` 6b caught the disagreement. `histOrderFailures` now takes the
verdict from `SpatialGamma.leqSpaceMask` itself, uses the set bits to select which channels to report,
and quotes the **canonical** forms the order actually compared — so a mask of 0 returns no failures by
construction and the drift class is gone. Measured after the repair: the mirror agrees with `leq` on
**2000 of 2000** pairs (1855 of them rejected, each with at least one named channel).

**One-sided failures are marked `SUFFICIENT CONDITION ONLY`, and that is a statement about the
product.** `SpatialType.leq` is `Shape.leqStrong × leqSpace`. When one component is *proved* contained
and the other is not, the product containment can still hold — the contained component may exclude
exactly the values the other's clause objects to. `orderFailures` now says so on the failing clause.
`SpatialCheckCheck` 4a–4c pin an instance where `γ(a) = γ(b)` **outright** (both types carry the same
shape, which pins the value to `{ε, a, b}`; `a` states the count as a spill bucket of exactly 3 paths
over lengths `[0,1]`, `b` as one path of 0 items and two of 1): the histogram halves are not in the
order either way, the shape halves are equal, and the containment is visible only to the conjunction.
That is *not* repairable inside `leqSpace` — the previous occupant of these three tests (a spill window
against tracked classes) **was**, and was repaired, which is why they were re-pointed.

### 9.13 Counted execution: the missing "actual steps" oracle (review.md 2)

**`EffortEvent` / `EffortSink` / `Calibration`** — `src/main/scala/SpatialEvents.scala`, with hooks in
`MORKL.scala`, `IntTrie.scala`, `IntTrieOps.scala`, `GraphExec.scala` and `Zipper.scala` — all single
statements, no signature changes.

The effort model previously had no lower bound, no calibrated interval, and no identity of the
executable it described; its only empirical test was wall-clock **rank** on 16 separated programs. Now
**22 events** each tie to one emitting site and exactly one cost component — **19 calibrated** across
four components (`Work` 10, `Alloc` 4, `Rounds` 3, `Touch` 2) and **3 explanatory** (`ReusedSpace`,
`ReusedSubtrie`, `ZipperFallbackToEvalI`, never summed into work). A deliberate rule — asserted by a
test — is that **no event exists without an emitter**, which is the `PrefixAbsent` "dead promise"
complaint applied to this vocabulary.

**What was uncounted and now is (review.md 1).** `evalI` (`TrieDispatch`, `TriePathDispatch`, and all
three `Rounds` events), every `ITrie` node the algebra builds (`FreshTrieNode`, at the single
`ITrie.node` site), and the recursive `ITrie`/`IntTrieOps` descent — the new `Touch` component:
`TrieNodeVisit` at every recursive `ITrie`-level entry (union/inter/subtract/restrict/compose/wrap/
unwrap/joinAll/meetAll/suffixClosure/head plus the size/nodeCount/prefixCount/toPaths/range walks) and
`PatriciaVisit` at every recursive `IntTrieOps` step. The consequence that matters: the Trie backend is
now calibrated like the other three, and **no calibration row is skipped for a structural reason** —
`0 of 200` predictions were skipped as symbolic, against the review's 177/200 zipper exclusion.

Instrumentation of an executor is not analysis, so this does not touch the §0 invariant. The sink is an
armed-flag plus a `ThreadLocal[Counter]`; its disarmed cost is **measured, not asserted**.

**Calibration, measured (executable-checked, `SpatialEventsCheck`).** Containment is
`lower ≤ actual ≤ upper` per component; the tightness statistic is
`slack = (upper + 1) / (actual + 1)`, finite for every finite prediction. Every threshold below was read
off the measurement and rounded up, so they are regression gates; the gate now covers **p95 and
worst-case slack per (backend, component)**, not only containment, and a `(backend, component)` pair
with no declared gate — or a declared gate no row exercises — **fails**.

Fuzzer corpus, warm phase: **200 cases, 3000 points, 100% containment (0 outside the interval),
0 predictions skipped**.

| backend | Work p95 / worst | Alloc p95 / worst | Rounds p95 / worst | Touch p95 / worst |
|---|---|---|---|---|
| reference | 2.56 / 14.44 | 5.50 / 23.00 | 1.42 / 5.99 | — (declared oracle gap) |
| trie | 1.27 / 6.53 | 11.70 / 22.75 | 1.42 / 5.99 | 23.71 / 69.55 |
| graph | 1.90 / 7.69 | 7.57 / 16.02 | 1.42 / 5.99 | 25.29 / 69.55 |
| zipper | 11.47 / 36.07 | 17.44 / 151.00 | 1.42 / 5.99 | 26.77 / 110.33 |

Cornerstones, warm phase: **6 cases, 66 points, 100% containment, 0 skipped** — and the numbers are
much worse, which is the point of publishing them rather than a filtered subset:

| backend | Work | Alloc | Rounds | Touch |
|---|---|---|---|---|
| reference | 5,368× | 55,648× | 3,175× | — |
| trie | 3,839× | 213,465× | 3,175× | 3,962,335× |
| zipper | 3,838× | 213,465× | 3,175× | 3,962,335× |

**Where cost tightness is poor, and why.** (a) `touch` is the loosest component by two orders of
magnitude because it bounds a **worst-case Patricia descent** that pointer identity, empty operands and
prefix mismatches routinely cut to nothing, and because `collect` must cover `Fold`'s left fold of
unions, which is genuinely quadratic in the group count. (b) `zipper Alloc` worst 151× on the corpus and
213,465× on the cornerstones is not a close model. (c) The **cornerstone** figures are the review's own
5,368×/55,660×/3,201× essentially unchanged — instrumenting the delegated trie work made the numbers
*measurable* for four backends and *did not* make them tight. Anyone reading `Cost.touch` as a
predictor of runtime should read the worst column first.

**Two named exclusions from the slack gate, and only two.** `datalog-sn` (the least fixpoint of the
body's size transformer — no fixpoint over the size lattice and no finite path universe to widen into;
this needs an interprocedural size summary, not a cost constant) and `puzzle15` (16 nested `Iteration`s
past `SpatialCost.MaxDepth = 64`, and raising the cap to 512 was **tried**: the bound then saturates to
`inf` because the loop transfer multiplies per-level group counts and a 16-level product overflows the
algebra's `Long`). The test asserts the exclusion set equals the set of cornerstones that actually come
out unbounded, **in both directions**, so it cannot drift and a silently-bounded cornerstone fails.

The executors are differentially checked **while counted**: `evalI`, `execZ` and `execT` outputs are
asserted equal to `eval`'s on all 200 corpus programs and all 6 cornerstones — the regression that would
catch a hook changing semantics.

Four attribution bugs the review named are fixed and pinned: a warm `Literal` no longer charges `|v|`;
a full-window `Range` is the identity and charges no sort; the **trie** `Range` does sort and its full
window is not free; and `execT`/`execZ` are priced separately and really do differ. The identity
regression the review asked for holds: increasing input size does not increase modelled warm work for
an identity operation.

**The one remaining oracle gap, declared in the model rather than in the test.** `ReferenceCost`
declares `touchNoOracle`: `eval`'s `Set` operations delegate union/intersection/hash probing to the
Scala collection library, so these hooks cannot honestly count its internal element touches. `touch` is
therefore excluded from calibration for `reference` **and only for `reference`** — a test pins that list
to exactly one backend and names its reason, and a second test measures the claim behind it (`eval`
counted **0** trie-touch events over all 200 corpus programs and all 6 cornerstones). The measured
reference events are AST dispatches, explicit prefix comparisons, loop frames and fixpoint rounds.

### 9.14 One ordinary entry point (review.md 3)

**`SpatialAnnotations` / `SpatialPipeline` / `SpatialHook`** — `src/main/scala/SpatialPipeline.scala`
The subsystem was an island: `Routine.optimized` ran the old `Lower` rule list, and `transpile`, graph
`optimize`, `execT` and `execZ` consumed no `SpatialType`, `Fact`, `BoundedRecursion` or cost report.
There is now one flow, in the review's own shape:

```scala
def analyzeRoutine(r: Routine, ann: SpatialAnnotations): RoutineAnalysis
def optimize(r: Routine, a: RoutineAnalysis): SpatialTyping.SpecializedRoutine
def optimizeGuarded(r: Routine, a: RoutineAnalysis): GuardedRoutine   // + the checked fallback
def lower(s: SpecializedRoutine, backend: Backend): LoweredRoutine
```

`SpatialAnnotations` is the single input value (spaces, paths, path lengths, routines, plus one
`SpatialConfig` that the fact and recursion budgets are now projections of). `FactScope` separates
**unconditional** facts — safe to consume in the ordinary optimized program — from **conditional** ones,
which produce a guarded version plus a fallback whose dispatcher uses full γ. Backend lowering consumes
explicit candidates; measured on the pipeline's own comparison table, 1 of 6 probe programs is a
**spatial-only win** (`x ∖ x` folds to `Empty` where the ordinary rule list leaves 3 nodes), the graph
backend consumes a `GraphConstantFold`, and the report prints why a candidate was *declined* (e.g. a body
already a literal, where zipper pre-focus would only add work) rather than silently omitting it.

**INSTALLED, not documented (review.md 3, first half).** `Routine.optimized` used to hand `body`
straight to `Lower.inline`; the hook was described in a comment and never applied. It now runs:

```scala
def optimized(using ctx: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Routine =
  val rc = others(ctx)
  Routine(name, refs, mentions,
          all_forever(Lower.inline(using rc)(SpatialHook.rewrite(body, rc)), Lower.OrdinaryRules))
```

Three supporting extractions are behaviour-preserving: `Routine.others(ctx)` (the self-excluding routine
table, previously an inline anonymous `PartialFunction`, now shared by the inliner and the hook),
`Lower.OrdinaryRules` (the same 31 rules in the same order), and `Routine.optimizedPlain` — the pre-hook
`optimized`, verbatim — which `optimizeGuarded` uses as a guarded artifact's **fallback** so that
`GuardedRoutine.changed` keeps meaning "the spatial tier changed something".

`SpatialHook` owns the policy and the numbers. Default **ON** (`-Dmorkl.spatialHook=false` restores the
old behaviour); `SpatialConfig.cheap` (2 trie levels × 6 heads, `nodeBudget = 2000`, one reduction round,
no direct histogram queries) plus a `maxBodyNodes = 600` size belt; and it is **total** — an analysis
that raises is counted in `SpatialHook.stats.raised` and answered with the unmodified body, because a
compile-time hook may lose an optimization but may not lose a compile.

**What it costs and what it buys, both measured per call** (`SpatialPipelineCheck`):

| | number |
|---|---|
| worst absolute delta over 11 representative routines | **+26.7 ms** (n-queens `place(8)`, 137 nodes, 1106.6 → 1133.3 ms) |
| worst ratio on a call already past 1 ms | 7.5× (gol/nextStep, 2.5 → 18.9 ms) |
| worst ratio on a call already past 20 ms | **1.02×** |
| whole table | 1216 / 1159 ms = **1.049×**; 4 of 11 bodies rewritten |
| process total for the suite | 115 calls, 0 over budget, 37 changed, **0 raised**, 4966 µs/call |
| what it BUYS on 250 fuzzed corpus programs | 71 rewritten, compiled bodies **8710 → 7796 nodes** for 199 ms over 250 calls |
| soundness of the rewrite | 250 programs × 25 envs = **6250 differential checks against `eval`** |

The honest summary: it **pays on open bodies and is a small tax on closed ones** — on the closed
cornerstone routines it saves nothing at all, because `Lower.ConstantOps` is a partial evaluator and
folds those anyway (the `nodes saved` column is 0 for all nine of them).

### 9.15 Semantic laws as production inputs (review.md 2)

**`LawEvidence` / `SpatialBoundLaw` / `SpatialLaws`** — `src/main/scala/SpatialLaws.scala` (new)

Acceptance 6a–6c used to prove closure, Life-image and n-queens facts in standalone Scala and then
*hand-construct* a `SpatialType` beside the analyzer; its own comment said no `SpatialBoundLaw` existed.
`PatternImage` and `chainBound` likewise had no route through `SpatialAnnotations`, `SpatialAnalysis`,
cost or specialization. There is now a law channel, carried by `SpatialConfig.laws` — so every stage that
already takes annotations takes laws with **no new plumbing** (`ann.withLaws(l1, l2)`).

```scala
enum LawEvidence:                     case ExecutableChecked(what) | SmtProved(what) | Assumed(what)
final case class SpatialBoundLaw(name, applies: LawSite => Boolean,      // cheap, at every visit
                                       bound:   LawSite => Option[SpatialType], evidence)
enum LawOutcome:                      case Tightened | Unchanged | NoBound | Contradicted
SpatialLaws.refine(laws, site): (SpatialType, Vector[LawApplication])    // the engine
SpatialLaws.forTerm / callResult / restChain                             // 3 applicability shapes
```

**The safety argument is one line and it is structural.** A law's bound is **met** into the inferred
type, so `γ(refined) ⊆ γ(unrefined)` *by construction*: a law cannot widen no matter what it claims.
A bound that contradicts the transfers yields `Contradicted` and is **dropped**, not propagated — an
unsound law degrades precision, never soundness. Checked on 4096 random values.

**Provenance is on the node and separates the three labels**, which is the distinction this atlas keeps
everywhere: `ExecutableChecked` and `SmtProved` are `discharged`; `Assumed` is not, and
`decorated.assumedLaws` is a first-class query so a result resting on an undischarged premise can be
found rather than inferred. `lawQueries = 4000` bounds applicable-occurrence evaluations (a user law's
`bound` may run a whole chain analysis); the **root is refined regardless of the budget**, because the
traversal is post-order and the root is visited last.

**Measured: each law tightens a real Zippy routine and changes its cost or residual** (`SpatialAcceptance`
6a–6d, `SpatialLawsCheck` 11 tests).

| law | evidence | what it does to the routine |
|---|---|---|
| `DirectedTransitiveClosure(sn_tc)` | ExecutableChecked — all **512** digraphs on 3 nodes, Warshall vs an independent saturation closure | the datalog cornerstone: size `[·, ∞] → [3, 9]`, length `[·, ∞] → [2, 2]`, gains `MaximumCardinality(9)`/`MaximumPathLength(2)` and the **`TrieUnroll` candidate**; on `closure ∩ {length-3 literal}` it licenses `EliminateEmpty` — residual **6 → 1 nodes**, warm work **UNBOUNDED → 1** — and `eval` confirms the eliminated subterm really is ∅ on all 512 graphs |
| `SubsetOfImage` (radius-1 Life) | ExecutableChecked — all **512** 3×3 fields | bounds `|nextStep(field)|` at 9·\|field\| once a field type is declared; 64 law-refined analyses of the real `nextStep`, every one γ-admitting `eval`. The bound 9 is **loose but sound**: worst observed ratio 1.75 |
| `FiniteConstraintSolutions` (n-queens) | ExecutableChecked — exact counts n=1..8 (1,0,0,2,10,4,40,92), **zero Zippy events** | raises the n-queens `size.lo` off 0 to the exact solution count (the transfers never search) |
| `PatternImage` / `chainBound` | ExecutableChecked | now law **inputs**, not adjacent calculations: `chainBound` at depth 3 tightens the inner binder 64 → 16 paths, and under the cheap config tightens the root transfer's own bound 50 → 10; `|eval| = 10 = 2N` and both refined types γ-admit it |

`chainBound` at depth 2 under the default config records **`Unchanged`** — `SpatialTypes`' `Iteration`
count transfer already applies the same `Σ K_i` law. That is reported rather than hidden: a law channel
whose records were all `Tightened` would be a channel that never tells you the transfers got there first.
Order-independence of the final answer, budget honouring, one-record-per-position merging with an
occurrence count, and "facts, candidates, the residual and the residual's cost all read the refined
answer" are each separately gated.

### 9.16 Precision, latency and slack budgets instead of permissive gates (review.md 4)

The cornerstone acceptance test used to accept `a.result.shape.isTop` as a "useful" answer, so
`datalog-sn` **passed while returning no facts and a fully unbounded type**, and the nominal linearity
test asserted only that 1,023 nodes finish within 60 s while the 295-node `puzzle15` term took ~38.6 s.
Three budgets replace that.

**1. A per-cornerstone precision budget** (`SpatialAcceptance.precision`). Each of the six cornerstones
declares `required` facts (value-equal — a regression in any of them fails), `maxSize`/`lenHull`
**ceilings** (a regression fails; an *improvement* is printed and asks for the table to be updated), an
exact `spine` and the `candidates` that must still be offered. There is **no blanket ⊤ entry**: a channel
that genuinely cannot be bounded under an open annotation is listed in `expectedTop` **with its reason and
with what would close it**, and the test asserts it really *is* ⊤ — so a channel that silently becomes
bounded also **fails**, forcing the record to be updated. Three of those reasons name a semantic law, and
§9.15's tests are exactly those laws closing them. The expected-⊤ ledger is printed on every run, and the
set of exercised entries is asserted equal to the set of declared ones.

**2. An interactive latency and scaling budget** (`SpatialAcceptance` 5c). Measured warm, printed every
run, per cornerstone:

| cornerstone | `infer` ms | decorated ms | `analyzeRoutine` ms | nodes | observations | decor/infer |
|---|---|---|---|---|---|---|
| aunt | 0.0 | 0.1 | 0.2 | 20 | 20 | 11.0× (noise) |
| datalog-sn | 0.0 | 0.0 | 0.1 | 4 | 4 | 5.8× (noise) |
| gol | 9.1 | 9.4 | 9.6 | 2 | 2 | 1.03× |
| **puzzle15** | 201.1 | **1305.5** | 1341.2 | 295 | 13,725 | **6.49×** |
| temperature | 0.0 | 0.1 | 0.3 | 7 | 7 | 6.1× (noise) |
| nqueens | 10.0 | 17.1 | 28.4 | 53 | 267 | 1.71× |

`puzzle15` decorated analysis is **1.3 s against the review's 38.6 s** for the same term. Gated at 4000 ms
decorated / 5000 ms routine — deliberately ~2.5× the measured worst so a loaded machine is not flaky — and,
more importantly, by a **structural** budget that cannot be met by buying a faster machine: the decorated
traversal must stay a **constant factor** over the plain `SpatialTyping.infer` query it decorates
(ceiling 12×; before the incremental join it was 170× on `puzzle15`). Ratios below a 20 ms `infer` floor
are reported as noise rather than gated. The scaling test confirms the ratio does not grow: on balanced
union trees of 255/511/1023/2047 nodes the ratio is 1.94/1.28/1.07/1.04×, and the 1023-node tree the old
linearity test used takes **264 ms against a 1500 ms budget** (the pre-existing gate was 60,000 ms, which
is not a budget).

**3. Cost-slack ceilings** — §9.13's p95-and-worst gate per (backend, component), with the two named
unbounded cornerstones excluded by an exclusion list that is checked for exact agreement in both
directions.

**4. Avoidable checker `Unknown`s reduced to zero** — §9.9. The review asked for the 15.3% false-negative
rate to come down "chiefly where spill and tracked histogram partitions denote the same concrete lengths".
Measuring the causes refuted that framing (150/202 were not false negatives at all, 52 are product
interaction, **0 avoidable**) and the named cause scored zero because it was fixed; on universes that
decide containment both orders now measure **0 false negatives**.

### 9.17 The gates for §9.5–§9.16

All are `eval`-gated differential suites; `eval` appears in tests only, never in an analysis
(docs/design_spatial_lattice.md §0).

| Suite | Path | What it pins |
|---|---|---|
| **`SpatialTypeCheck`** | `SpatialTypeCheck.scala` | Per-length soundness of `SpatialTypes.infer` on 3000 closed corpus instances, plus both projections inside the z3 bounds. Reports the tier-1 tightening count. |
| **`SpillSoundness`** / **`ReviewFindings`** | `SpillSoundness.scala` | The spill/tracked overlap repair, the class and `MaxLen` caps holding for *every* constructor, randomized spill collisions; and the three earlier review defects. |
| **`SpatialElimination`** | `SpatialElimination.scala` | `eliminate`/`eliminateIn`: fires where the syntactic law cannot, never inside a `Call`, and 2000 corpus differential checks for unconditional rewrites. |
| **`SpatialShapeCheck`** | `SpatialShapeCheck.scala` | The shape domain and the product: the review's probes, the 1000-instance corpus γ gate, and operator matrices over flat / wide / past-`MaxDepth` / nested operands. Carries a greedy delta-debugger (`ShapeShrink`) so a violation reports a *minimal* witness. |
| **`SpatialLawCheck`** | `SpatialLawCheck.scala` | The γ layer: extensivity/reductivity/adjunction, `leq ⇒ γ`-containment with its incompleteness measured **and attributed by channel**, the two γ copies agreeing, per-operator simulation squares, transfers at abstract operands α never produces, and conditional-rewrite equivalence with a load-bearing precondition. Two order tests now DECIDE containment on universes complete for their class: `leqSpace` **0 false negatives** (420 histogram types, 8400 pairs, 512 count vectors, 1950 contained pairs) and `Shape.leqStrong` **0 false negatives** (240 shapes, 14400 pairs, 9947 contained pairs, decided on 8192 spaces). `canonSpace` γ-preservation and idempotence over 3.5 M (type, value) comparisons, and the `leqSpace` latency budget the completeness cost. |
| **`SpatialLawsCheck`** | `SpatialLawsCheck.scala` | §9.15: a law can never widen (γ on 4096 random values), an inapplicable law changes nothing at all, a weaker law records `Unchanged`, a contradictory law is **dropped** and the analysis stays consistent, provenance names the evidence and separates ASSUMED from proved, the `lawQueries` budget is honoured while the root is refined regardless, repeated observations of one position merge into one record with a count, law **order** does not change the answer, the tightest true law still γ-admits `eval`, every library law **declines** where its premise is not established, and facts/candidates/residual/residual-cost all read the refined answer. |
| **`SpatialRecursionCheck`** | `SpatialRecursionCheck.scala` | Depth bounds and residuals: the headline `maxLen 4 ⇒ depth 4`, hygiene of splicing, every `NoBound` reason, worklist/certification behaviour, and randomized gates over generated recursive routines. |
| **`SpatialCostCheck`** | `SpatialCostCheck.scala` | The `Sym` algebra, `dominates` soundness, per-operator and per-backend cost shape, recurrence closing, monotonicity, and the runtime rank-correlation sanity check. |
| **`SpatialSoundnessHunt`** | `SpatialSoundnessHunt.scala` | The **adversarial** net: 9 sweeps over all 21 constructors with nested binders, an interprocedural routine table, non-exact declared inputs and three path-ref modes, checking every projection, channel and `Fact` per case, with violations delta-debugged over *(term, environment)* pairs. Four minimal witnesses it found are pinned as named regressions. |
| **`SpatialAnalysisCheck`** | `SpatialAnalysisCheck.scala` | §9.10: decorated root `⊑ infer`, sub-quadratic scaling (2.99× per doubling), reducer termination/idempotence and its γ-gate (0 members lost, 0 false ⊥), positional identity of two equal ASTs, retained iterator bindings, and 4,352 closed decorated occurrences against `eval`. |
| **`SpatialFactsCheck`** | `SpatialFactsCheck.scala` | §9.11: `E_d`/`K_d` and the fibre envelopes against concrete fibres over a finite universe, `trieNodes` against `ITrie.prefixCount`, the rest-chain bound as `Σ K_i` (never a product), and the affine-overlay counterexample (`x` vs `x+1`: different at the same binding, **not** globally disjoint) that blocks an unsound `2N` lower bound. |
| **`SpatialCheckCheck`** | `SpatialCheckCheck.scala` | §9.12: the three-way result, every `Refuted` witness re-validated, a `leq` false negative returning `Unknown` (never `Refuted`) — now a **PRODUCT INTERACTION** instance where `γ(a) = γ(b)` outright, the previous spill-window instance having been repaired — the incompleteness measured and attributed (10 of 62), the **order mirror agreeing with `leq` on 2000 of 2000 pairs**, vacuous-annotation reporting, and the no-evaluation sentinel. |
| **`SpatialEventsCheck`** | `SpatialEventsCheck.scala` | §9.13: the closed event vocabulary (every event has an emitter and exactly one component), hand-computed hook counts per executor **including `evalI` and the `ITrie` algebra**, the four attribution fixes, the identity regression, cold/warm separation, the calibration tables with a **p95 and worst-case slack gate per (backend, component)** and a declared-gate/exercised-row cross-check in both directions, the single declared touch-oracle gap pinned to `reference` alone, and `evalI`/`execZ`/`execT` output equality with `eval` **while counted**. |
| **`SpatialPipelineCheck`** / **`SpatialAcceptance`** | `SpatialPipelineCheck.scala`, `SpatialAcceptance.scala` | §9.14, §9.15, §9.16 and the review's acceptance suite: annotation-only analysis, symbolic fibres (`2N`, not `N²`), decorated binders, multi-step Life through five calls, the six cornerstones under a **per-cornerstone precision budget** (required facts, cardinality/length ceilings, exact spine and candidates, and an explicit expected-⊤ ledger with a reason per channel — no blanket `isTop` acceptance), an **interactive latency and scaling budget**, four laws each tightening a real routine, `Routine.optimized` consuming unconditional facts, and optimization with a checked fallback. |

---

## 10. Supercompiler

A positive supercompiler that drives a configuration through bounded reduction, unfolds Calls, folds recurring configurations, whistles on growing configurations (homeomorphic embedding), and generalizes (most-specific generalization) — producing a finite `Residual` program then lowered to op-graphs. All within a shared compile budget with graceful fallback. See [SUPERCOMPILER.md](SUPERCOMPILER.md).

| Component | Path | Role & interactions |
|---|---|---|
| **`Matching`** | `Supercompiler.scala:21` | Term-algebra utilities over Space/Path — free-variable analysis, capture-avoiding substitution, bound-name canonicalization (`canon`), α-renaming, instance matching (`instanceOf`, the FOLD), homeomorphic embedding (`embeds`, the WHISTLE), most-specific generalization (`msg`, anti-unification). **Boundary invariant** — `canon()` normalizes binder names so all four matchers treat bound occurrences as constants (`==`) and free occurrences as variables; every public matcher canonicalizes first. `instanceOf` produces θ (applied exactly once, NO occurs-check) so recurrences like `acc↦acc∪δ` are representable finitely. `freeMentionsV`/`freeRefsV` define the ORDER of residual routine parameters. Consumed by `SC.State`. |
| **`SC` (core)** | `Supercompiler.scala:625` | The driver proper — `sourceLaws` (~35 named meaning-preserving `Lower` rules, EXCLUDING Call inlining so the driver controls unfolding), `reduce` (apply `simplifyRules` to a structural-`==` fixpoint, budget stops GRACEFULLY), `Config`, `validate` (rejects reserved `#`/`~` name prefixes), `run`/`supercompile`. `reduce` IS the REDUCE half of driving. `run` establishes the compile-budget contract (`State.deadline = Deadline.inMillis(cfg.compileBudgetMs)`); on expiry `CompileBudgetExceeded` produces a non-converged fallback residual that still evaluates (`materialize` supplies the reachable env). Returns `(Residual, State, conf)`; `State` counters feed `SCReport`. `sourceLaws` names are the contract `scripts/check_laws.py` enforces against `proofs/laws/REGISTRY.tsv`. |
| **`SC.State`** | `Supercompiler.scala:693` | Mutable per-run driving engine implementing the drive/unfold/fold/whistle/generalize loop that builds the process tree and residual routines. `drive` alternates REDUCE (`reduce`) and UNFOLD (bottom-up `subs` with an `spost` hook dispatching each callable Call to `scCall`). `scCall` decision order: (1) FOLD via global `instanceOf` against all `fnodes` (sound because a config denotes a pure fn of its free vars); (2) WHISTLE via innermost path ancestor that `embeds` but is not an instance; (3) `makeNode`. `makeNode` is the only producer of residual Routines — pushes the fnode BEFORE driving `unfold(c)` so recursive self-instances can FOLD back (ties the recursive knot). `unfold` inlines even self-calls (which `Routine.optimized` deliberately refuses). Caps (`maxDepth`/`maxNodes`/`maxReduce`/deadline) turn bugs/overruns into errors or graceful fallback, not hangs. |
| **`Residual`** | `Supercompiler.scala:545` | Driven top `Space` + generated `routines` map forming a closed evaluation env. `evaluate` runs `eval(top)(using pc,sc,env)` — verification that the residual computes the same SpaceValue as the source. |
| **`SCStats`** | `Supercompiler.scala:553-557` | Size/shape metrics (node/literal/mention/call counts) for a Space; `before`/`after` feed `SCReport`. |
| **`SCReport`** | `Supercompiler.scala:590-611` | Auditable account of one run: size deltas, driver counters, convergence/compile-time-eval flags, backend-compilation status, per-phase timing. `summary` classifies the run (BUDGET-EXCEEDED / OPTIMIZED AWAY / residual loop / graph-lowered / source-only). |
| **`SupercompiledProgram`** | `Supercompiler.scala:619` | Packaged result: `residual` + `report` + per-routine `graphs`. `evaluate` bridges to `eval`; `graphs` present only for backend-supported routines. |
| **`Supercompiler` (facade)** | `Supercompiler.scala:814` | Report-bearing public API: drives (`SC.run`), transpiles/optimizes the residual to op-graphs (`lower`), accounts backend support (`backendUnsupported`: Grounded*/Fold; Fixpoint IS supported), times all phases, packages a `SupercompiledProgram`. `compileCall`/`compileRoutine`/`specialize` (pre-substitutes static args for partial evaluation). `backendCompiled` true only when every residual routine lowered. |

---

## 11. Equivalence / proof pipeline & tooling

The verification core. Control-flow Spaces are expanded to ground local algebra, rendered into three certified egg vocabularies (formal set-of-paths, zipper movement, bridge trie) and into ∀-input / instance SMT files, and discharged by egglog + z3 + Vampire. `SmtDiff` decomposes whole-program equivalence into optimizer-rewritten subterm pairs, replaying the certified law corpus for justification. See [design_plan.md](design_plan.md) for the "one source of truth / checked meaning-preservation" invariants realized here.

| Component | Path | Role & interactions |
|---|---|---|
| **`EquivPipeline`** | `EquivPipeline.scala:21` | Turns a control-flow Space into ground local algebra (`expand`, the Stage-0 TRUSTED expansion whose each case IS the corresponding `exec` eval rule) and renders it into the egg vocabularies (`formalOf`, `zOf`, `trOfGraph`, `implOfSpace`, `tnodeOf`) and into SMT membership-equivalence (`Smt.den`, `smtEquivalence`). `pipeline()` GATES `expand` by `assertEquals(eval(expanded) == reference)` — expansion is the trusted boundary, the proofs certify only the residual local algebra. `foPrelude` is the FIRST-ORDER SMT prelude (Path datatype + quantified `append`/`isPrefix` axioms + two certified lemmas). `Smt.den` accepts only local-algebra Spaces (throws on Iteration/Fixpoint/Fold/Call/Range — `expand` must run first). Emitted files discharged by BOTH z3 and Vampire. Consumed by `EquivPipelineTest`; `AgnosticPipeline`/`SmtDiff` reuse `foPrelude`. |
| **`AgnosticPipeline`** | `EquivPipeline.scala:291` | Builds the primary, data-agnostic certificates — inputs stay uninterpreted so obligations quantify over ALL inputs. `unrollControl(s,k)` k-unrolls Fixpoints/recursive Calls and cuts residual self-calls to a fresh shared free input (certifies the loop RULE, not one instance's convergence); `fold`/`symbolic`; `renderZ` (movement vocab over free mentions + defunctionalized Iteration bodies); `AgSmt`/`smtAgnostic` (∀-inputs ∀-paths SMT). `unrollControl(prog,2)` vs `unrollControl(SC.reduce(prog),2)` are the pre/post-optimiser sides fed to `SmtDiff`. `renderZ` emits into `$l`/`$r` lets; Iteration bodies always rendered PLAIN so both styles' BodyK ids coincide. `fold`'s ground-subtree folding (via `evalI`) makes downstream sides identical by construction. |
| **`SmtDiff`** | `EquivPipeline.scala:656` | Decomposes whole-program ∀-equivalence into the finitely many optimiser-rewritten subterm pairs, classifies each as law-justified (replayed against the certified corpus) or residual (prover obligation), and emits the TRIVIAL / LAW-JUSTIFIED / STRUCTURAL-DIFF obligation file. `diff` is congruence-descending and **AC-aware** (union flattening + multiset cancellation of common operands) so reordered union towers don't fabricate obligations; `alphaNorm` canonicalizes binders so optimiser renamings aren't seen as differences. `justify` closes the loop from optimizer to corpus — re-runs `SC.sourceLaws`/`SC.reduce` (the SAME laws the optimiser used) on the differing subtree; a match means the pair is a ∀-certified law instance needing no per-program prover run, and `certificateOf` names the `proofs/laws/*.smt2` file(s). `refine` recursively shrinks unjustified pairs. `obligationsFile`'s marker drives `EquivPipelineTest`'s counting and whether z3+Vampire run. |
| **`lawCertificates` registry** | `EquivPipeline.scala:787` | In-code map from optimiser law name → its universal certificate (`proofs/laws/*.smt2`, or GROUND/SCHEMATIC/DEFINITIONAL classification), mirroring `proofs/laws/REGISTRY.tsv`. Provides the human-auditable link from a justified diff pair to the exact ∀-certified proof file; its keys are the contract with `SC.sourceLaws`. Authoritative source is `REGISTRY.tsv` + `proofs/STATUS.tsv`, kept in sync by `scripts/check_laws.py`. |
| **`EquivPipelineTest` (driver / emitter / verifier)** | `src/test/scala/EquivPipelineTest.scala:15` | Runs the full three-stage pipeline on the six cornerstone programs (aunt / datalog-sn / gol / puzzle15 / temperature / nqueens), wires optimizer output to the renderers, writes `proofs/pipeline/*.smt2` and `zipper-egg-tests/pipeline/*.egg`, and verifies them with egglog, z3 and Vampire. For each stage, three semantic models are cross-checked against ONE ground truth `reference=eval(prog)`: formal set-of-paths egg, movement egg, bridge trie egg, plus the SMT membership twin. Scala executor GATES bound the trusted parts before any prover runs (`eval(expand)==reference`, `materialize==reference`, `runGraphT==reference`, virtual-unroll==reference, `randomGate` agreement). Byte-equal egg sides emit an explicit IDENTICAL-LITERAL marker (never a vacuous hash-consing "equivalence"). `runSmtFile` requires BOTH z3 (`unsat`) AND Vampire (`Refutation found`). Ties the optimizer to the corpus end-to-end (`SC.reduce(prog)` is the optimised side of every leg). Requires egglog + z3 + Vampire on the machine. |

### 11.1 Verification tooling (`scripts/`, `proofs/run.sh`)

| Tool | Path | Role & interaction |
|---|---|---|
| **`gen_law_obligations.py`** | `scripts/gen_law_obligations.py` | Generates the per-law SMT-LIB certificate corpus `proofs/laws/law_*.smt2` + `proofs/laws/REGISTRY.tsv`. Its `PRELUDE` (FO append/isPrefix axioms) is the single source reused by `mine_laws.py` and the proofs obligations. Each law asserted NEGATED (z3 unsat / Vampire refutation = PROVED). |
| **`mine_laws.py`** | `scripts/mine_laws.py` | Enumerates 22 candidate reduction laws, throws z3+Vampire at each, records verdicts in `proofs/laws/MINED.tsv` (16 PROVED, 0 COUNTERMODEL, 5 UNKNOWN). PROVED+profitable candidates get promoted into `REGISTRY.tsv` and implemented in `Lower`. |
| **`proofs/run.sh`** | `proofs/run.sh` | Discharges every obligation with BOTH z3 and Vampire; writes `proofs/STATUS.tsv`. A COUNTERMODEL or unexpected OPEN exits non-zero. `refine_cli`/`refine_cls` are the two admitted-OPEN (differential-covered) obligations. |
| **`check_obligations.py`** | `scripts/check_obligations.py` | Enforces that every egglog rule in the 4 model files carries a live proof/definitional/demand annotation; cross-checks cited files against `STATUS.tsv`. Fails on unannotated rule, cited COUNTERMODEL, or uncovered cite. |
| **`check_laws.py`** | `scripts/check_laws.py` | Verifies every `SC.sourceLaws` entry has a `REGISTRY.tsv` row with a PROVED certificate and required algebra laws stay present. A law added to `Lower` without a certificate breaks CI. |
| **`audit_pipeline_markers.py`** | `scripts/audit_pipeline_markers.py` | Classifies every pipeline artifact as REAL/TRIVIAL/IDENT/LAW-JUSTIFIED/BUDGET; rejects vacuous hash-consing equivalences and fake `(assert (not true))` goals; enforces IDENTICAL-LITERAL twins carry the real certificate. |
| **`check_locality.sh`** | `scripts/check_locality.sh` | Mechanically checks the movement spec's locality: descent work is O(d) over an opaque source (via egglog `ChildOf` table size), plus invokes `lint_zipper_egg.py`. |
| **`lint_zipper_egg.py`** | `scripts/lint_zipper_egg.py` | Lints the movement spec for no-materialization (observations read, never build a trie node) and lock-step / one-step-per-layer (RHS `Sub` reuses the LHS key var). The syntactic guarantees behind the O(d) claim and Ascend-commutes. |
| **`make_bridge.py`** | `scripts/make_bridge.py` | Merges `zipper-spec.egg` + `zipper-impl.egg` into `zipper-egg-tests/bridge-prelude.egg` bridged by `Reflect: Tr → Z` (with independent `RGet`/`RKeys` so the commuting square is real, not a definition unfold). |
| **`gen_bridge_tests.py`** | `scripts/gen_bridge_tests.py` | Generates randomized 3-way (spec / impl / Python reference) coincidence tests under `zipper-egg-tests/generated/` (README cites 7,150 checks). Certifies the spec↔impl commuting square AND grounds both against an independent denotational reference. |
| **`extract_formal_preludes.py`** | `scripts/extract_formal_preludes.py` | Extracts rule-only preludes from `formal.egg`: the full reference (`formal-prelude.egg`) and a rotation-free `ElemP` variant (`formal-elem-prelude.egg`) for membership consumers. |
| **`extract_noaa_slice.py`** | `scripts/extract_noaa_slice.py` | Reproducibly extracts one NOAA gridded temperature-anomaly slice (via h5py) into `src/test/resources/noaa_slice.txt` — the data source for the temperature cornerstone. |

---

## 12. Fuzzer & corpus

A composable pseudo-random sampling DSL (`Dist`), a structural path-set description zipper (`Loc`) mirroring the Space algebra at the level of path-set descriptions, and `SpaceFuzzer` which generates diverse programs together with a DEPENDENT argument space and result. The 1000-program corpus this produces is the shared fixture behind every differential/size/benchmark suite.

| Component | Path | Role & interactions |
|---|---|---|
| **`Fuzzer` (Dist combinator library)** | `Fuzzer.scala:11-88` | A tiny composable sampling DSL — `Dist[T]` values you `sample` given a `java.util.Random`, built from `Uniform`/`Filtered`/`Mapped`/`Collected`/`Pair`/`Cond`/`Dep`/`Concentrated`/`Degenerate`/`Categorical`/`Repeated`/`Sentinel`. `Categorical.ratios` accumulates weights into a CDF (weighted choices for `SpaceFuzzer.argLoc`/node-kind selection). `Dep(dx, fdy)` is the load-bearing bind that makes the program distribution depend on the sampled argument (`SpaceFuzzer.example`). Pure, RNG-parametric substrate; no MORKL-specific logic. Design draft in [fuzzer_zipper_draft.md](fuzzer_zipper_draft.md). |
| **`Loc` (structural path-set zipper)** | `Fuzzer.scala:96-176` | A lazy structural description of a SET of paths as a zipper — at any `segment` answers `is_path` (membership) and `branches` (extending items) — whose combinators mirror the Space algebra and whose `instantiate` materialises a concrete `SpaceValue`. `Const`/`Repeat`/`Full`/`Empty`/`Trie` builders + `Union`/`Intersection`/`Subtraction`/`Restriction`/`Raffination`/`Compose`/`Dep`. `SpaceFuzzer.argLoc`/`argDist` construct these then call `.instantiate()`. Boundary invariant: every `Loc` the fuzzer uses is BOUNDED (branches must exhaust to terminate). |
| **`SpaceFuzzer`** | `Fuzzer.scala:185-314` | Generates diverse programs with a DEPENDENT argument space and result: an argument `SpaceValue` is sampled first (bounded `Loc`, materialised), then a program is drawn OVER that space, then run — a dependent `(arg, program, result)` triple. `example = Dep(argDist, arg => genProg(arg,...)...)` — the argument is sampled first and the program's literals/wrap-tags/unwrap-heads/restriction-keys are drawn from that same arg, so unwraps land and intersections overlap. A subterm POOL (scope-compatible reuse with prob `poolShare/10`) produces SHARED subterms independent draws wouldn't. Iteration binders extend the `Scope`; scope prefix-compatibility keeps pooled subterms well-scoped. `evalEx` fills `Example.result` via `eval`; the filter enforces non-empty, ≠arg, ≤400 paths, and that the program genuinely mentions `x`. Consumed by `FuzzerTest`, `ProgramExpressivity` (the 1000-program corpus generator), `CorpusValidation`, `SizeBoundsCheck`, `ZipperTest`, and the benches. |

---

## 13. Test suites (grouped)

All suites gate against `eval` (directly, or via a backend itself gated against `eval`). Suites tagged `SlowTag.Slow` (`src/test/scala/Examples.scala:10`) are opt-out via `bin/test --exclude-tags Slow`. `Loaders` (`src/test/scala/Examples.scala`) supplies portable, Option-valued dataset loaders (`repoRoot`, `note`, `mettaFamily`, `parseRLE`, `caracEdges`) with in-repo fallbacks so the suite runs in a fresh checkout.

### 13.1 Differential & law gates (the correctness backbone)

| Suite | Path | What it pins |
|---|---|---|
| **`CorpusValidation`** | `CorpusValidation.scala` | The definitive gate: `eval==evalI==evalT==exec==execT==execT(opt)==execZ` over 1000 programs × 1000 random input envs. Loads `corpus_1000.ser` (STALE-schema guard). Per (program,env) computes `ref=eval(prog)` and asserts SEVEN executors equal it, binding the same env consistently across all representations. |
| **`CorpusLawValidation`** | `CorpusLawValidation.scala` | The law-pipeline gate: `SC.reduce(prog)` preserves meaning under `eval` on many random inputs across every corpus program. A single wrong new law fails here (a backend-vs-backend differential can't catch a wrong law both backends share). |
| **`AlgebraicLaws`** | `AlgebraicLaws.scala` | Metamorphic gate on the ~45 set-algebra laws THEMSELVES under `eval` (400 seeds). Reference is `eval` alone — catches a bug in the reference interpreter OR a mistaken law. |
| **`OptimizerProperties`** | `PropertyTest.scala` | Randomized (300 programs): `transpile+execT` and `transpile+optimize+execT` preserve `eval`; interpreters agree; `Space.Fixpoint` TC matches an independent closure; a `GroundedAudit` asserts the guiding examples stay grounded-free. |
| **`ProductUnionCheck`** | `ProductUnionCheck.scala` | Cross-checks the Space optimizer (`Lower`) and the op-graph optimizer (`optimize`) against `eval` — both can push a nested product-of-iterations into a union (LICM), and the guards (`headedGuard` vs `nonEmptyGuard`) are semantically necessary on empty/eps-only edge cases. |

### 13.2 Per-backend gates

| Suite | Path | What it pins |
|---|---|---|
| **`TrieTest`** | `TrieTest.scala` | Both trie backends as exact-but-faster `Set` implementations: round-trip identity, each op == `eval`, `evalT`/`evalI` == `eval` on real programs, AND the `AlgebraicResult` **Identity-as-object (`eq`)** structural-sharing contract (load-bearing for downstream memoization). |
| **`ZipperTest`** | `ZipperTest.scala` | The `SpaceZipper` paradigm: every op matches `eval` via lift→op→materialize, zipper laws hold, `execZ` agrees with `eval`/`evalI` on whole programs (establishes `execZ` as a first-class member of the equivalence family). |
| **`ZipperEggTest`** | `ZipperEggTest.scala` | Cross-checks the Scala `SpaceZipper` against an egglog `Z`-term model — movement coincidence (descend to exactly the members) and implementation coincidence (recursive egglog set-ops compute Scala's trie). The only consumer validating the zipper against an EXTERNAL prover; degrades to Scala-only when egglog absent. Produces `zipper-egg-tests/*.egg`. |
| **`GraphExecT`** | `GraphExecTest.scala` | The op-graph backend: `execT(transpile)==eval`, and every transform (`optimize`/`push_out`/`optimize_sharing`/`inline`/`lower`) is semantics-preserving — checked by execT-agreement + `wellFormed`, not string snapshots. Pointed soundness checks: deep-nesting `push_out` regression, and non-monotone mutual recursion must NOT be lowered. |

### 13.3 Supercompiler suites

| Suite | Path | What it pins |
|---|---|---|
| **`SCMatching`** | `SupercompilerTest.scala` | Unit-pins the matching primitives: free-var analysis, capture-safe `subst`, `canon`/`alphaEqual`, `renaming`, `instanceOf` (folding), `embeds` (whistle), `msg` (anti-unifier correctness). |
| **`SCDriver`** | `SupercompilerTest.scala` | Termination AND soundness on real recursive/relational routines: the residual eval-agrees with the original program call (TC, reachable, aunt, predecessors). |
| **`SCGeneralization`** | `SupercompilerTest.scala` | The whistle is NECESSARY (without it, driving diverges to the cap); with it, a self-recursive residual, sound, and residual size DATA-INDEPENDENT. |
| **`SCHardening`** | `HardeningTest.scala` | Soundness/robustness hardening (from `critique_on_b.md`): capture-avoiding subst, reserved-name rejection, Fold/grounded matching identity, embedding heuristic, deterministic generalization. |
| **`SCFacade`** | `HardeningTest.scala` | The report-bearing facade + op-graph lowering of residuals: reports populated, residuals eval-sound, static input compile-time-evaluated/specialized, budget graceful-fallback, timing/improvement accounted. The single-program analogue of `CorpusValidation`'s exec/execT columns. |
| **`SCDegeneracies`** | `SCDegeneracies.scala` | Corpus-wide SC diagnostics + soundness (`evalI(residual)==evalI(original)` on 8 inputs × 1000 programs) and a ranked table of reducible-but-surviving residual patterns naming missing laws (the backlog signal `CorpusLawValidation` later validates). |

### 13.4 Size-analysis suites

The spatial-type suites (`SpatialTypeCheck`, `SpillSoundness`/`ReviewFindings`, `SpatialElimination`,
`SpatialShapeCheck`, `SpatialLawCheck`, `SpatialRecursionCheck`, `SpatialCostCheck`,
`SpatialSoundnessHunt`) are tabulated with the components they gate in **§9.17**.

| Suite | Path | What it pins |
|---|---|---|
| **`SizeBoundsCheck`** | `SizeBoundsCheck.scala` | Soundness of tier-1 `Lower.sizeBounds`: `lo ≤ |eval(s)| ≤ hi` and `loHeaded ≤ |headed|` on every closed corpus instance; pins the tricky transfer functions and `SizeEmpty`. |
| **`SizeZ3Check`** | `SizeZ3Check.scala` | Dominance + soundness of tier-2 `SizeZ3.bounds`: the z3 interval is contained in the baseline AND still contains every `eval` size. `assume(SizeZ3.available)`. |
| **`SizeBoundsReport`** | `SizeBoundsReport.scala` | Tightness REPORT for tier-1: asserts soundness everywhere, MEASURES tightness over suite + 5×1000 closed instances (distinguishes design-expected vacuity from failures). Feeds numbers cited in `design_size_constraints.md`. |
| **`SizeZ3Report`** | `SizeZ3Report.scala` | Full baseline-vs-z3 distribution over 1000 corpus + pooled/deep fuzzed × 100 inputs, asserting soundness+dominance and REPORTING solver scope limits (`Status`) as such. Exercises `boundsWithStatus`. |
| **`SizeZ3Drilldown`** | `SizeZ3Drilldown.scala` | Diagnostic drill-down (aunt-query, open pure GoL): program, per-node DAG with baseline intervals, lowered SMT (`encodeText`), and an A/B of what `optimized()`/z3 buys. The only consumer of `encodeText`. |

### 13.5 Benchmarks (generate `docs/BENCHMARKS.md`)

| Suite | Path | What it measures |
|---|---|---|
| **`TrieBench`** | `TrieBench.scala` | `eval` vs `evalT` vs `evalI` across all six domains + n-ary join/meet microbench; asserts agreement then APPENDS timings to `docs/BENCHMARKS.md`. |
| **`GraphBench`** | `GraphBench.scala` | Four suites: op-graph exec/execT vs evalI + compile-time accounting, subgraph-hoist A/B, SC-optimize across 6 domains, 5-stage ablation. The primary evidence generator for the op-graph optimizer; appends to `docs/BENCHMARKS.md`. |
| **`ZipperScaleBench`** | `ZipperScaleBench.scala` | `execZ` vs `evalI` at scale: constant-factor flat algebra, asymptotic selective-pruning win, 3-way fusion, native Range, O(1) identity short-circuits. Only consumer loading the external `royal92_simple.metta` fixture. |
| **`RecursionLoweringBench`** | `RecursionLoweringBench.scala` | Interpreting recursive Calls DIVERGES for mutual recursion while the lowered `Fixpoint` runs under all four executors; plus deep local-algebra fusion (`execZ` no intermediates). Evidence for `lowerCalls`. |
| **`ExecutorOverheadBench`** | `ExecutorOverheadBench.scala` | Compiled executors never meaningfully slower than the matching interpreters (`exec` vs `eval`, `execT`/`execZ` vs `evalI`) over 1000 programs × M inputs; geomean ratios. |
| **`CorpusRuntimes`** | `CorpusRuntimes.scala` | Runtime/node-size census of the saved corpus (evalI), then supercompiles the 5 slowest and re-times original vs SC'd across all five executors. Produces `corpus_runtimes.csv`. |

### 13.6 Expressivity / fuzz census / corpus generator

| Suite | Path | What it does |
|---|---|---|
| **`ProgramExpressivity`** | `ProgramExpressivity.scala` | Expressivity census (variable arg signatures + per-arg responsiveness → `/tmp/expressivity.csv`) AND the **CORPUS GENERATOR** producing the shared `corpus_1000.ser`/`.txt` (input-sensitive, multi-valued programs). Defines `FuzzRec` at top level; changing its fields invalidates the corpus (the STALE guards point back here). |
| **`ProgramStats`** | `ProgramStats.scala` | Structural (no-eval) census: parent-constructor × child-slot → child-constructor matrix over N programs → `/tmp/prog_matrix.tsv`. Only cluster consumer that never evaluates a program. |
| **`FuzzerTest` (`FuzzerDemo`)** | `FuzzerTest.scala` | Demonstrates and randomized-soundness-tests the fuzzer: `(program, arg, result)` triples differentially validated `eval == evalI == evalT == execT(optimize(transpile))`. |

### 13.7 Guiding examples & DSL usage (from `Examples.scala` / `MORKL.scala`)

The worked case studies from [ALGEBRA.md](ALGEBRA.md) — the six cornerstones the equivalence pipeline verifies. Each `Ex*` driver validates plain `eval`, the native trie evaluator, and (where relevant) the supercompiled residual against an independent Scala reference.

| Example object / driver | Path | Notes |
|---|---|---|
| **`AuntQuery`** (fixture) + **`ExAuntMetta`** | `MORKL.scala:217` / `Examples.scala:90` | Family-genealogy tree + relational queries in the DSL; golden aunt result `{Aunt.Ann.Liz, Aunt.Jim.Ann, Aunt.Pat.Liz}` reused across the atlas. `ExAuntMetta` validates the SC residual eval-agrees and specialized away the static `family` param. |
| **`Routines`** (object) | `MORKL.scala:534` | Shared library of routines-under-test (aunt, transitive closure, reachable, scc, union_iter, `fixpoint`). Central producer for the whole test/bench corpus. |
| **`Routines`** (class) + **`Graphs`** | `MORKL.scala:468 / 101` | SCC / reachability / transitive closure over `scc_context`; passes routine tables via `given rc`. |
| **`ExDatalog`** + **`DatalogShowTest`** + **`Expand`** | `Examples.scala:137` / `DatalogShowTest.scala:11 / 105` | Naive vs semi-naive Datalog TC (three-way agreement naive==semi-naive==reference==SC-residual). `Expand` pretty-prints Space back to runnable Scala; writes `datalog-morkl.txt`. |
| **`GoL`** + **`ExGameOfLife`** | `Examples.scala:222 / 277` | Pure MORKL Game of Life (arithmetic precompiled into number relations, cardinality via `Range`). `ExGameOfLife` validates blinker/random/fred.rle + two-step deforestation. |
| **`NQueens`** + **`ExNQueens`** | `Examples.scala:336 / 364` | Pure recursive n-queens (`aoe` attack relation, `place` k-nested iterations). Counts pinned to OEIS A000170 under Set eval (n=4..8), trie eval (n=9..12, Slow), and SC residual (n=8). |
| **`Sliding`** + **`ExSlidingPuzzle`** | `Examples.scala:397 / 474` | Sliding-tile state space via BFS-to-fixpoint (`explore`). Triple-agreement eval==evalT==reference; full 3×3 (181440 states) uses evalT only (Slow). |
| **`NOAA`** + **`ExNOAATemperature`** | `Examples.scala:513 / 544` | Spatial/temperature binary-trie encodings — prefix restriction is a range query. Validates bucket/spatial queries against a Scala reference, SC specialization, and a sha256 provenance check on `noaa_slice.txt`. |
| **`Unification`** (object + class) | `MORKL.scala:1111 / 647` | MeTTa-like `$var`/literal pattern combinators (`U`/`C`/`W`/`Q`/`T`/`MQT`/`MQMT`) compiling to the Space DSL; larger worked programs (division/sudoku/gol). |
| **`Imperative`** | `MORKL.scala:280` | Validates `transpile → optimize → exec` for shared routines against `eval`; pins op-graph `.show` dumps + mermaid. |
| **`MORKL2Space`** | `MORKL.scala:9` | Foundational operator suite — golden algebra checks of the core evaluator for each operator. |

---

## 14. How a program flows

A concrete trace from surface syntax to verified result:

1. **Author** — a program is written with the `Syntax` DSL (§1): `\/`/`/\`/`x`/`<|`/`.iter`/`:=` build a `Space` AST and, via `mod(...)`, a `PartialFunction[RoutinePtr,Routine]` routine table. Optional type inspection via `itypes`/`otypes`.
2. **Denote** — the reference `eval(space)` (§3) interprets the `Space`/`Path` AST directly over `Set[PathValue]`, threading the persistent `PathContext`/`SpaceContext` binders that make it TOTAL, resolving Calls through `rc` (with the tail-recursion fixpoint guard). This result is the ORACLE.
3. **Choose an executor** — the same program can run four other ways, each validated to equal `eval`:
   - **`evalT`** over the TreeMap `Trie` (§5.1), exploiting `AlgebraicResult` structural sharing + `eq` early termination;
   - **`evalI`** over the interned `ITrie` (§5.2), riding IntMap/Patricia merges;
   - **`transpile → RecursiveOpGraph → exec`** (SpaceValue) or **`execT`** (ITrie) — the compiled op-graph backend (§4), entered via `runGraph`/`runGraphT`;
   - **`transpileZ → SpaceZipper → execZ`** — the fused-cursor backend (§6), fusing local set-algebra into one materialize and routing control-flow through `evalI`.
4. **Optimize** — `Routine.optimized` (§7) runs the source-level `Lower` law fixpoint (`all_forever` over the ordered rule list). For the compiled backend, `optimize(transpile(...))` alternates `push_out` (LICM + product-splitting) and `optimize_sharing` (CSE) to a `structuralHash` fixpoint, budgeted by a shared `Deadline`, instrumented by a `Profiler`. Recursion is first handled by `lowerCalls` (§8): `asFixpoint`/`asFixpointGeneral` and `lowerMutualSCC` turn recognizable recursion into `Space.Fixpoint`, leaving honest residuals for the rest.
5. **Supercompile** (optional) — `Supercompiler.compileCall`/`specialize` (§10) drives the program (`SC.State.drive` alternating `reduce`/`unfold`, with `fold`/`whistle`/`generalize` via `Matching`), yielding a finite `Residual` then lowered to op-graphs. Static inputs are compile-time evaluated. Everything is bounded by the compile budget with graceful fallback.
6. **Size-bound** — `Lower.sizeBounds` (§9) gives the tier-1 interval `lo ≤ |eval(s)| ≤ hi`; `SizeZ3.bounds` refines it with a z3 Optimize problem that asserts the baseline (never widens) and adds the saturated ⊑ relation + inclusion-exclusion facts, returning a `Status`-tagged, dominance-guaranteed interval.
7. **Verify** — `EquivPipeline`/`AgnosticPipeline`/`SmtDiff` (§11), driven by `EquivPipelineTest`, prove the optimized/zipper/graph forms equivalent to the original for the six cornerstones: control-flow is `expand`ed (gated by `eval`), rendered into three egg vocabularies + SMT, discharged by egglog + z3 + Vampire; whole-program equivalence is decomposed by `SmtDiff` into certified-law instances (via the `lawCertificates` registry) plus residual prover obligations.
8. **Gate at scale** — the corpus (§12), generated by `ProgramExpressivity` from `SpaceFuzzer`, drives `CorpusValidation` (all seven executors agree with `eval` on 1000 programs × 1000 inputs), `CorpusLawValidation` (`SC.reduce` preserves `eval`), and the size/benchmark suites (§13) — the definitive `eval == evalI == evalT == exec == execT == execT(opt) == execZ` and law-preservation checks.

The through-line: **`eval` is the fixed point of trust.** Backends are checked against it, optimizer rewrites must preserve it, size intervals must contain it, and equivalence certificates are only emitted after a Scala gate confirms the trusted expansion still equals it.

---

## 15. Artifacts & data

Generated and tracked data products, and the docs that explain them.

**Corpus.** `corpus_1000.txt` / `corpus_1000.ser` (repo root) — 1000 fuzzed programs (pretty text + serialized `Vector[FuzzRec]`), each sensitive to every argument with ≥2 distinct outputs. The `.txt` is the reproducible source of truth (per design_plan §1.4); the `.ser` is a binary accelerator. Produced by `ProgramExpressivity`; consumed by the differential/size/overhead/runtime suites. `FuzzRec` schema drift trips the STALE guards. Derived analyses: `corpus_runtimes.csv` (`CorpusRuntimes`), `/tmp/expressivity.csv`, `/tmp/prog_matrix.tsv`.

**Benchmarks.** [BENCHMARKS.md](BENCHMARKS.md) (264 KB, largest doc) — steady-state timing tables (compile vs run separated) for `eval`/`evalT`/`evalI`, the op-graph executors, and the zipper, across the six domains. Generated by `TrieBench` and `GraphBench` (append-mode). The empirical companion to the correctness proofs (design_plan's "honest performance" standard); geomean `evalI` ≈ 16.7× vs Set, 1.6× vs `evalT`.

**Proofs.** `proofs/` — the SMT-LIB obligation corpus (rule certs, `impl_*` homomorphisms, `threeway_*` per-op theorems, `refine_*`, `lemma_append_*`), each asserting the NEGATED theorem. `proofs/run.sh` discharges them with z3+Vampire, writing `proofs/STATUS.tsv` — the repo-wide source of truth for PROVED vs OPEN (92 rows; all PROVED except the two admitted-open `refine_cli`/`refine_cls`). `proofs/laws/REGISTRY.tsv` + `MINED.tsv` index the per-law certificates (`law_*.smt2`); `check_obligations.py`/`check_laws.py` gate against these tables.

**Egg models & tests.** `formal.egg` (the core set-of-paths reference — the single semantic source of truth), `zipper-spec.egg` (the certified per-key movement/observation calculus), `zipper-impl.egg` (the eager `ITrie` implementation model), `zipper.egg` (illustrative). `zipper-egg-tests/` holds the extracted preludes (`formal-prelude.egg`, `prelude.egg`, `bridge-prelude.egg`), the randomized `generated/rand-*.egg` differentials (7,150 checks), per-program op artifacts, and the README matrix (SET-OF-PATHS / EAGER-TRIE / ZIPPER × observations).

**Per-program equivalence.** `proofs/pipeline/*.smt2` + `zipper-egg-tests/pipeline/*.egg` — auto-generated per-cornerstone (aunt / datalog-sn / gol / nqueens / puzzle15 / temperature) equivalence artifacts (`-graph`/`-space`/`-zipper`[`-agnostic`/`-impl`/`-virtual`/`-lit`] variants + markers). Emitted by `EquivPipelineTest`, audited by `audit_pipeline_markers.py`.

**Example source.** `datalog-morkl.txt` — hand-written MORKL AST source for the Datalog TC examples (naive + semi-naive), written by `DatalogShowTest`. `src/test/resources/noaa_slice.txt` — the NOAA temperature fixture (extracted by `extract_noaa_slice.py`).

**Build & journal.** [README.md](../README.md) — repo index, requirements, run recipes, CI-checker list. `build.sbt` (repo root) — sbt project (Scala 3.8.1, munit 1.2.1); `sbt test` is the top of the verification pipeline that emits the egg/smt2 artifacts. `build.log` (repo root) — append-only development journal recording sessions, marker/registry counts, and `SizeBoundsReport` tightness deltas (the 39%-vacuous-lower-bound finding that motivated [design_size_constraints.md](design_size_constraints.md)).

**Reference docs (siblings in `docs/`).** [ALGEBRA.md](ALGEBRA.md) (the functional-pearl paper: types, operators, five case studies — this repo is its executable counterpart); [SUPERCOMPILER.md](SUPERCOMPILER.md) (SC design/examples/limitations); [design_plan.md](design_plan.md) (five publication-readiness invariants, the CI differential-gate spec, "Range = ordered trie-slice only"); [design_size_constraints.md](design_size_constraints.md) (the relational size-analysis spec realized by `SizeConstraints.scala`); [residuals.md](residuals.md) (why the residuated division operators are deliberately omitted); [fuzzer_zipper_draft.md](fuzzer_zipper_draft.md) (the `Dist` combinator draft behind `Fuzzer.scala`).
