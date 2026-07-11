# MORKL Supercompiler + Runtime — Implementation Plan

The standard is publication readiness: **semantic faithfulness** (every rewrite proved and
differentially tested), **honest performance** (steady-state numbers, ablation), **reproducibility**
(portable text-first artifacts, seeded runs), and **maintainability** (one production runtime,
one source of truth for semantics).

---

## 1. Principles (invariants)

1. **One source of truth for semantics.** `formal.egg` is the specification; every Scala rewrite
   carries a matching egglog `check`. A law without a proof is a liability.
2. **Meaning-preservation is *checked*, not asserted.** A corpus-wide differential gate runs in
   CI (§6): for every program all backends agree, and for every supercompiled program
   `eval(SC(p)) == eval(p)`.
3. **Graph well-formedness after *every* optimizer pass** — no dangling coordinates, result slot
   pinned, scope identity preserved — not only after the final pass.
4. **Reproducible artifacts.** Text-first (JSONL + pretty MORKL source + seed + generator
   version); binary caches are accelerators only.
5. **Honest performance.** Steady-state timing with dispersion; per-strategy ablation;
   compile-vs-run separated; compiled-away rows reported as compile + tiny run, never as runtime
   speedups; never mix operators of different meaning in one results table.

---

## 2. `Range`: ordered trie-slice only

`Range(x, start, end)` is the trie-native **ordered slice** — `RangeBounds.normalize` plus a
border traversal that preserves trie order without rematerializing paths, with negative
indexing — and is the fused replacement for `First`/`Last`. It is the **only** `Range`.

There is **no cardinality operator** in the core language. Cardinality windows are expressed by
**counts-as-data**: a pure MORKL construction materializes a cardinality as an ordinary path,
after which ordinary slice/filter/algebra applies. Game of Life's "exactly 2/3 live neighbours"
is expressed this way — produce the neighbour count as data, then filter — and the GoL benchmark
is re-validated under this encoding. Every cardinality use is therefore ordinary algebra,
automatically covered by the existing laws and the differential gate.

---

## 3. Runtime representation

**Production value domain: a single hash-consed `TrieSpace`.** Immutable node =
`(terminal, IntMap[child], cachedCounts)` over interned `PathItem → Int`; structural sharing via
persistent `IntMap`; node canonicalization drops empty children.

**Hash-consing is global and done only at construction / file-read time.** Paths are interned
and trie nodes are canonicalized/deduplicated **as data is built or read in**, never inside the
runtime evaluation loop. Equality is then O(1) (identity) for free during evaluation — `==`/`!=`
in the fixpoint loops and CSE keying are pointer comparisons — without paying per-op interning
overhead in hot paths.

**Native-or-crash within the trie path.** Every MORKL operation is implemented **directly on
`TrieSpace`**. There is no reference-evaluator fallback inside the trie path, no public-API
compatibility layer, and no `IntTrieOps` living in `scala.collection.immutable`. If an operation
is not implemented natively it **crashes** (hard `UnsupportedOperationException`); it never
silently degrades. This makes "trie-native" a total, verifiable claim — no row quietly runs on
the reference interpreter. Faster prefix-merge implementations, when wanted, are written as
native trie ops and proved equal by the differential gate (§6); the gate is the only safety net.

**The other evaluators are kept as differential backends, not deleted.** `eval` (reference),
`evalI` (`ITrie`), `evalT` (`Trie`), `exec`, and `execTrie` remain as independent backends used
**only** to cross-check the trie path inside the §6 mesh. They are not production executors and
are never a fallback target of the trie path; they exist to catch a bug in it.

**Interner hygiene.** The global `PathItem` interner has constant-time lookup, is
**scoped/resettable** for tests that need deterministic ids, and its **cold/warm state is part of
the benchmark contract** (report whether tables were warmed; never compare a row after an
unrelated massive alphabet was interned). No `PathItem` is allocated in hot loops after
construction.

**Literal identity: per-graph constant pool.** Each graph carries its own table of literal
constants, and nodes reference them by pool-local id. Artifacts are self-contained and trivially
portable as a unit — no global hash, no cross-process id dependence, ids meaningful within their
graph — with always-inlining via the existing codec as the fallback wire format. Accepted
trade-off: no cross-graph literal sharing, so artifacts that repeat literals across many graphs
are larger; this is fine because the graph is the unit of serialization and replay. (Process-local
interner ids are ruled out — they make artifacts non-portable.)

---

## 4. Result-slot pinning and graph hygiene

A current-frame output slot is pinned with an **explicit `Alias`/`Copy` graph node** (never an
idempotent `Union(x,x)` that an optimizer could simplify away or move past the pin).
Well-formedness tests assert the result coordinate stays pinned after each of raw / CSE /
`push_out` / hoist / full `optimize`. A `graphReferenceErrors` validator runs **after every
optimizer round** (every `(level,index)` input resolves to a real node); `graphStructurallyEqual`
is the optimizer fixpoint test; a staged-equivalence test asserts all optimizer stages agree
under both `exec` and `execT`. The optimizer is untrusted until it passes fresh-seed 1000×1000
program/frame fuzzing across all backends.

---

## 5. Algebra and the supercompiler

### 5.1 `IterUnion`
Three sound rewrites ship together; a **cost model** (a node-visited estimate) chooses among them
per site:

- **Headed-guarded hoist** (default): `iter(src, l∪r) → l ∪ iter(src, r)` when `provablyHeaded(src)`
  (a conservative static "≥1 head" test). Sound and strictly cheaper — `l` is computed once with
  no re-iteration.
- **Whole-body-invariant drop** (subsumed special case): `iter(src, body) → body` when `body` is
  fully invariant and `src` is headed.
- **Distribute** (cost-gated fallback): `iter(src, l∪r) → iter(src, l) ∪ iter(src, r)`, used only
  when a branch is provably expensive *and* `src` is cheap to re-iterate.

For symbolic `src` that no static test can prove headed, the op-graph `push_out` performs sound
*dynamic* loop-invariant motion. Each rewrite carries its egglog proof: headed-hoist sound;
bare-hoist unsound over an empty source; distribute sound unconditionally.

### 5.2 Closure / `Fixpoint` / `Range` algebra, proved 1:1 in egglog
First-class `Fixpoint`, `PrefixClosure`/`SuffixClosure`/`TailsClosure`, ordered `Range`, the
residual↔closure identities, and `composeRange` are each gated on a matching egglog `check`.
The previously-asserted laws are discharged explicitly: `Range(x,a,b) ⊆ x`, the
`Restriction`/`Raffination` partition, and the `composeRange` slice arithmetic (the
open-upper-bound encoding is documented and proved).  (The residual operators referenced in
earlier drafts are omitted from the language — see residuals.md.)

### 5.3 Law set
`Literal(∅) → Empty`; `Iteration(Empty) → Empty`; `iter(_,_,t,Mention t) → TailsUnion`;
idempotence (`Union`/`Intersection`/`Restriction(x,x) → x`, `Raffination(x,x) → ∅`);
`Wrap`/`Unwrap`-ε; constant `Unwrap`-merge; `Unwrap(Wrap)` prefix cancellation; closure
idempotence; `IterateLiteral_Union` that groups literal paths **by head** (dedups shared heads);
and `ConstantOps` gated on a structural `closedEvaluable` check (no exception-as-control-flow).

### 5.4 Resolved bugs (carried regardless of surrounding code)
`IterateSingleton_Deref` (single-item source leaves tail-set `{ε}`, not `∅`),
`IterateLiteral_Union` (head/tail crash on the empty path — empty paths are skipped), and the
`IterUnion` empty-source hoist (now guarded, §5.1).

### 5.5 Recursion: mutual / SCC lowering
Build the call graph from the `Routine` set, compute its strongly-connected components (Tarjan),
and lower each recursive SCC to a **system of mutually-recursive fixpoints** `(s₁,…,s_k) =
lfp(F₁,…,F_k)`. Single self-recursion is the unary special case. Add the `Fixpoint` `msg` case
and alpha-aware `instanceOf` folding so the supercompiler folds fixpoints by structure, not by
literal variable-name coincidence.

**Lowering condition: structural monotonicity.** A recursion is lowered only when its step is
built from `⊑`-monotone constructors (`Union`, `Wrap`, the closures, `Composition` with a fixed
factor), so the ascending chain `init ⊑ step(init) ⊑ …` stabilises at the least fixpoint. This
applies to **mutual** recursion as well: the combined step of the SCC must be monotone. There is
**no iteration cap** — a cap is not the language semantics and would silently truncate a legal
program; recursions that cannot be shown monotone stay residual `Call`s.

**Open proof/analysis obligation:** formalize structural monotonicity (including the mutual-SCC
case) and the least-fixpoint-reachability argument, and analyze precisely which recursions
qualify. Semi-naïve evaluation is the runtime strategy for the lowered system (§7.2).

---

## 6. Verification — one unified gate

A single correctness harness, run in CI:

1. **Independent oracle.** Each fuzzed program is built *with* its expected `SpaceValue`, computed
   by a deliberately-naïve separate path-set implementation. This catches bugs common to all
   production backends, which N-way agreement alone cannot.
2. **N-way differential at 1000×1000 fresh-seed scale.** For every program × frame:
   `eval == oracle == evalI == evalT == raw/opt exec == raw/opt execTrie == raw/opt execT`.
   All backends (§3) participate — more independent cross-checks.
3. **SC-soundness gate.** `eval(SC(p)) == eval(p)` for every program, over a corpus that
   **includes `Call`/recursion** so the driving engine and SCC lowering (§5.5) are exercised.
4. **Staged-optimizer equivalence** (all stages agree under `exec` and `execT`),
   `optimize(optimize(x)) == optimize(x)`, and post-pass `graphReferenceErrors` (§4).
5. **egglog ↔ Scala law correspondence.** Every Scala rewrite has a `formal.egg` `check`; the law
   unit tests are derived from the spec so the two cannot drift.
6. **Metamorphic algebraic-law properties** — `Union` comm/assoc, `Wrap∘Unwrap` round-trips,
   closure idempotence, `Range` composition — asserted as explicit properties, not only as oracle
   equality, so a wrong reference/oracle is also caught.

**`eval` is the trusted reference.** It uses persistent growing-context overlays
(`PathContextOverlay`/`SpaceContextOverlay`), making it total over the language — including nested
iterations/folds/fixpoints that grow the context — so nothing falls back to `evalI` as a stand-in
reference.

**Tests adopted as the floor.** The full existing suite — `TrieSpaceTest` (4-way differential +
property + optimizer-stage-invariance + `optimize` idempotence), `ReferenceExamplesTest` (datalog,
GoL, sliding puzzle at full **4×4**, n-queens through **12×12**), and the `FullBackendVerifier` —
is taken wholesale and *extended* with the egglog-proved-law unit tests and the `Call`/recursion
corpus. Nothing is dropped.

**Fuzzer.** One generator: dependent generation (`Dist`/`Concentrated`/`Loc`, realistic argument
spaces first) folded into the free-expression generator and the 1000×1000 verifier harness. It
covers the full constructor set including **`Call`/recursion (incl. mutual), closures, and
grounded ops**. Sensitivity/interestingness rejection filters (entropy, change-rate, per-input
witnesses) keep corpus quality high. Counterexamples are **shrunk** (delta-debugging) to minimal
form. The degeneracy miner is promoted from report-only to **assertions**: a detected reducible
pattern becomes either a new egglog-proved law or a tracked exception with a written rationale.

---

## 7. Concrete builds

### 7.1 `TrieSpace` as the optimizer's value domain
The op-graph's node values **are** hash-consed, interned `TrieSpace` nodes, and `execT` is the
**production executor**:

- Every op-graph node (`Union`/`Intersection`/`Subtraction`/`Restriction`/`Raffination`/
  `Composition`/`Wrap`/`Unwrap`/`TailsUnion`/`TailsIntersection`/closures/`Range`/`Iteration`/
  `Fold`/`Fixpoint`) executes via a native `TrieSpace` method (native-or-crash, §3).
- `optimize_sharing`/CSE keys on hash-consed node identity (O(1), §3), so common subexpressions
  are shared structurally rather than by string hashing.
- The retained `eval`/`evalI`/`evalT`/`exec`/`execTrie` backends (§3) run only inside the §6 gate
  as cross-checks — never on the production path.

### 7.2 Mutual-recursion + semi-naïve fixpoint lowering
Implements §5.5:

- Compute call-graph SCCs (Tarjan); lower each recursive SCC to a mutual fixpoint system,
  discharging the structural-monotonicity obligation per component; non-qualifying components
  stay residual `Call`s (never capped).
- Evaluate the system **semi-naïvely**: maintain a per-relation *delta*; each round apply each
  `Fᵢ` only to the newly-added tuples, union into the accumulator, and stop when **all deltas are
  empty** (the ascending chain has stabilised at the least fixpoint — finite by the monotonicity
  proof, so no iteration cap). The closures (`TailsClosure`, …) are the unary special cases.
- Because the `Fixpoint`/`Iteration` nodes execute over interned tries (§7.1), deltas are cheap
  trie *diffs*, not full-set recomputation — the datalog-grade strategy.

### 7.3 Complete compile budget
A single `Deadline` threaded through the whole pipeline:

- `check(phase)` polls at **every** fixpoint driver (`reduce`, SC drive, optimize rounds,
  semi-naïve loop) **and inside every large traversal** (chunked, so one huge single rewrite
  cannot overrun before the next poll).
- On timeout, return the **best known correct residual** — the last well-formed `reduce`/optimize
  fixpoint — never a partially-rewritten or dangling-coordinate graph.
- The report separates **requested / exhausted / actual-elapsed**, per phase.

### 7.4 Publication-grade measurement (full benchmark set adopted)
- **Adopt the entire `TrieBenchmarks` workload wholesale** — aunt query, graph two-hop/mutual,
  datalog semi-naïve, Game of Life, NOAA temperature, sliding puzzle, n-queens — as the baseline.
- **Steady-state timing**: warm to convergence, ≥N reps, report **median + dispersion** (IQR or
  stddev); no single-run rows.
- **Correctness-gate-before-timing**: each row first asserts all-backend agreement, then times.
- **Per-strategy ablation table**: by-reference literals, native trie merges, hash-consing/CSE,
  graph sharing, `push_out`, subgraph hoist, SCC-fixpoint call-lowering, semi-naïve evaluation,
  and each algebraic-law bundle — which bought which speedup, and which regressed.
- **Honest compile-vs-run accounting**: a graph residualised to a literal reports compile + tiny
  run, never a runtime "speedup factor."
- **Reproducibility**: committed numbers, seeds, generator versions; explicit cold/warm interner
  policy.

