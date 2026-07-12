# A Supercompiler for MORKL

This document describes the supercompiler for the MORKL space/path algebra implemented in
[`src/main/scala/Supercompiler.scala`](src/main/scala/Supercompiler.scala), and the guiding
examples that validate it in [`src/test/scala/`](src/test/scala/).

MORKL programs compute over **spaces** — finite sets of dotted **paths** (e.g.
`parent.Tom.Bob`, `Cell.2.3`). The algebra has set operations (union `\/`, intersection
`/\`, subtraction `\`), prefix operations (composition `x`, wrap, unwrap, restriction `<|`),
trie eliminators (`iter`, tails), and named recursive **routines**. MORKL already shipped a
concrete interpreter (`eval`), a generic term rewriter (`subs`), a battery of
meaning-preserving algebraic laws (`Lower.*`, mirrored in `formal.egg`), an op-graph
back-end (`transpile`/`optimize`/`exec`), and `Routine.optimized` (inline non-self calls +
rewrite to a fixed point). That is a *partial evaluator*. It deliberately never unfolds a
recursive self-call, so it can specialize a pipeline but cannot transform recursion.

The supercompiler adds the three missing ingredients of positive supercompilation,
specialized to the set algebra:

| ingredient | meaning here |
|---|---|
| **driving** | reduce a configuration with the algebraic laws, then unfold the outermost routine call — *including self-calls* |
| **folding** | when a driven configuration is an *instance* of an ancestor, tie the knot into a residual recursive routine |
| **whistle + generalization** | when an ancestor is *homeomorphically embedded* in the current configuration but is not an instance, generalize via most-specific generalization (anti-unification) so the process tree stays finite |

The output is a `Residual(top, routines)`: a residual MORKL program that is observationally
equal to the input but specialized/fused/transformed.

## Architecture

`object Matching` — the term-algebra layer, all unit-tested (`SCMatching`):
- `freeMentions` / `freeRefs` — binder-aware free variables (Iteration/Fold introduce binders).
- `subst` — capture-avoiding simultaneous substitution (binders shadow, and alpha-rename when a replacement would be captured).
- `canon` — canonicalize bound names so matching/embedding can treat bound occurrences as
  ordinary symbols and free occurrences (a routine's parameters) as variables.
- `renaming` — bijective α-renaming of free variables.
- `instanceOf` — one-sided matching, the **fold** test.
- `embeds` — homeomorphic embedding ⊴ (coupling + diving), the **whistle**. The
  `literalsAreAtoms` flag (default on) treats any literal/constant as one atom so a growing
  *static* accumulator trips the whistle and is generalized into a loop rather than unrolled;
  grounded nodes couple only on closure identity.
- `msg` — most-specific generalization (anti-unification): a common skeleton with fresh holes.

`object SC` — the driver (`SCDriver`, `SCGeneralization`):
- `reduce` — the `Lower` laws run to a fixed point (no call inlining; the driver controls
  unfolding). This subsumes partial evaluation: closed subspaces fold to literals, data-known
  iterations unroll, prefixes hoist out of loops, etc.
- `drive` — `reduce`, then supercompile every routine-call subterm bottom-up.
- `scCall` — for one call configuration: **fold** (instance of a function node) →
  **whistle** (an embedded ancestor → `generalize`) → otherwise create a function node,
  `unfold`, and drive its body.
- Safety caps (`maxNodes`/`maxDepth`) turn a whistle bug into a clear error, not a hang.

## What it does — soundness, specialization, transformation

Every claim below is a passing test; the residual is checked to **`eval`-agree with the
original program**.

- **Soundness on recursion.** Transitive closure, 3-mention reachability, and a recursive
  predecessor query are supercompiled and the residual agrees with the original (`SCDriver`).
- **Partial evaluation.** Supercompiling a call with *static* data bakes the data into the
  residual and drops parameters: the lot.metta aunt query specializes `family` away; the NOAA
  query specializes the whole grid away.
- **Deforestation.** `nextStep ∘ nextStep` on a Game-of-Life glider is fused into a single
  residual computing two generations.
- **Recursion → loop via generalization.** This is the headline. Supercompiling the
  semi-naive transitive-closure solver against a *static graph* generalizes the growing
  accumulator into a fresh parameter, yielding a **graph-specialized recursive loop** whose
  size is *independent of the graph* (2 residual routines for a 3-edge or a 30-edge graph,
  vs. an unrolling that would grow with the diameter). `SCGeneralization` proves the whistle
  is *necessary*: with generalization disabled the symbolic frontier doubles every unfold and
  driving diverges (hits the node cap); with it enabled the residual is a sound self-recursive
  loop.

## Guiding examples (`src/test/scala/Examples.scala`)

| domain | data | what is checked |
|---|---|---|
| **Graph / Aunt** | `lot.metta` (Tolkien genealogy, 117 parent facts) | 78 aunt-pairs; SC specializes `family` away; eval-agrees |
| **Datalog / semi-naive** | carac `RecursivePath`, `Acyclic`, `TopSort` | naive == semi-naive == independent reference closure; SC → graph-specialized loop |
| **Game of Life** | `fred.rle` + random + glider | step matches reference; fred 150→138; 2-step fusion |
| **Sliding puzzle** (pure) | 2×2, 3×3, 4×4, 5×5 | PURE MORKL (swap-permutation relations, no grounded fns); 2×2 full = 4!/2 = 12, 3×3 full = 9!/2 = 181 440; 4×4/5×5 bounded BFS == independent reference |
| **n-queens** (pure) | n=4..12 | PURE MORKL (arithmetic precomputed into literal tables, no grounded fns); solution counts match OEIS A000170 through n=12 (14 200); a solution = a distinct length-n path prefix |
| **Temperature** | NOAA gridded anomaly (May 2026, 2592 cells) | trie-prefix spatial range query + temperature-band query; SC specializes the grid away |

## Upstream correctness fixes found while building this

1. `Lower.UnwrapConcat_Unwraps` stripped prefix factors in **reversed** order
   (`Unwrap(s, l·r) ⇒ Unwrap(Unwrap(s, r), l)`); corrected to `Unwrap(Unwrap(s, l), r)`,
   consistent with the `formal.egg` law `Unwrap(Wrap p s, p·q) = Unwrap s q`.
2. `subs` and `collect` did not recurse into the argument of grounded nodes
   (`GroundedPP/SP/PS/SS`), so variable substitution silently skipped terms buried inside
   grounded functions — fatal once an iteration over them was unrolled. Both now recurse.

## Reporting & public API

`Supercompiler.compileCall` / `compileRoutine` / `specialize` return a `SupercompiledProgram`
= the `Residual`, an `SCReport`, and any operation-graph lowerings.  The report is auditable:
node counts before/after, the SC-specific counters (reductions, unfoldings, folds, whistles,
generalizations), `converged`, `backendCompiled` / `backendUnsupported`, and a
`compileTimeEvaluated` flag that distinguishes "the answer was computed at compile time" from
"a reusable residual was produced".  Where the residual is in the backend-supported fragment
it is lowered with `transpile`/`optimize` and `exec` is checked to agree with `eval`.

## Soundness hardening (what holds up to scrutiny)

- **Capture-avoiding substitution** — binders (Iteration/Fold) are alpha-renamed to fresh
  names when a substituted term would otherwise be captured; not merely shadow-aware.
- **Reserved-prefix enforcement** — generated names use `#` (canonical/holes) and `~` (fresh);
  the entry point rejects user inputs using those prefixes, so generated and user names cannot
  collide.
- **Grounded nodes** are opaque operations keyed by closure identity: they couple/match/msg
  only when they are the *same* host operation, recursing into arguments without inspecting the
  body.
- **Fold** is treated structurally throughout (substitution, renaming, instance matching, msg).
- **The embedding heuristic is explicit.**  `Config.literalsAreAtoms` (default true) treats any
  literal/constant as one atom so a growing static accumulator trips the whistle and is
  generalized into a loop; `false` gives the precise structural embedding.  Both are sound and
  tested; they trade residual *shape* (loop vs. unrolled answer).
- **Termination caps** — the whistle bounds the process tree; `reduce` additionally has a local
  step cap so a non-converging rewrite errors rather than hangs.
- **Folding is global** (against every function node, not only path ancestors): sound because a
  configuration denotes a pure function of its free variables and each node is parameterized by
  exactly those.  The *whistle* still uses the ancestor path (innermost first), so
  generalization is deterministic — supercompiling alpha-renamed inputs yields the same residual.

The `formal.egg` model carries the canonical laws the reducer implements, including the two
corrected ones below; `SC.sourceLaws` names each Scala law.

## Running

No system JVM/sbt is required beyond `scala-cli`.  One reproducible command from a fresh
checkout (builds a scratch dir of symlinks + using-directives; nothing to install):

```
bin/test                    # full suite (108 tests; lot.metta/fred.rle/carac/NOAA examples
                            # use the real files when present, deterministic fixtures otherwise)
bin/test 'morkl.ExDatalog'  # one suite
```

The committed NOAA fixture (`src/test/resources/noaa_slice.txt`) is reproduced by
`scripts/extract_noaa_slice.py` and pinned by a checksum test.

## Honest limitations / future work

- For a *fully static* recursive computation (e.g. n-queens with a fixed board, datalog over a
  fixed graph) the driver computes the answer at supercompile time; that is correct but is
  essentially compile-time evaluation. The interesting transformation — turning recursion into
  a compact, data-independent residual loop — happens when *part* of the input is symbolic, and
  is what the generalization machinery delivers.
- The supercompiler **preserves and specializes** a semi-naive solver; it does not *derive*
  semi-naive from a naive specification. Automatically discovering the delta/accumulator split
  (ALGEBRA.md §9) is a distillation-class transformation and remains future work.
- The whistle uses a standard homeomorphic embedding; the generalization is the textbook msg.
  More aggressive strategies (e.g. distillation, speculative evaluation, or using the op-graph
  `push_out`/`optimize_sharing` on residuals) are natural extensions.

## Appendix: a concrete generalized residual

Supercompiling the semi-naive transitive-closure solver against the static graph
`{a.b, b.c, c.d}` produces (the static graph is fused in as a literal; the accumulator `#g0`
and frontier `#g1` are generalized to loop parameters):

```
top: sn_tc_sc1()
sn_tc_sc1() := {a.b,b.c,c.d} \/ sn_tc_sc2({a.b,a.c,b.c,b.d,c.d}, {a.c,b.d})
sn_tc_sc2(#g0, #g1) := #g0 \/ sn_tc_sc2(
      #g0 \/ (#g1.iter(n, nbs, n x \/({a.b,b.c,c.d} <| nbs)) \ #g0),
            (#g1.iter(n, nbs, n x \/({a.b,b.c,c.d} <| nbs)) \ #g0))
```

## Interned IntMap trie (most performant backend)

`src/main/scala/IntTrie.scala` interns every `PathItem` to an `Int` once (a global, O(1)
`Interner`) and keys the trie children by `IntMap[ITrie]` (a Patricia trie).  The ring
operations are then `IntMap` callback merges — `union = unionWith(recursive union)`,
`intersection = intersectionWith(recursive intersection)` — which match the algebra and merge
in one O(n+m) structural pass.  `evalI` (the evaluator over `ITrie`) touches **no `PathItem`
during evaluation**: constants are interned at construction and the operations only combine
ints; un-interning happens only at the `SpaceValue` boundary.  Benchmarks: geomean ≈ **16×**
faster than the reference Set across the six (pure) example domains, and ≈ **1.5×** (up to 2.4×)
faster than the TreeMap trie — see `BENCHMARKS.md`.

## Trie backend (optimized data structure)

`src/main/scala/Trie.scala` provides a persistent, structurally-shared path-trie keyed by
`PathItem` (`Trie`) and a direct evaluator `evalT` — the native counterpart of the reference
`Set[List[PathItem]]` semantics. Every operation is a structural trie op: union/intersection/
subtraction are recursive merges; composition grafts a *shared* `b` at each terminal of `a`;
restriction/wrap/unwrap walk a spine; `iter` reads each child's tail-trie directly (no flat-set
regrouping). The n-ary `joinAll`/`meetAll` are the asymptotically careful ones — `meetAll` is
bounded by the *smallest* branch rather than the largest. A read `Zipper` (descend/ascend/focus)
is the imperative-execution view for a future op-graph backend.

`evalT` is proven to agree with `eval` (property tests over 1000+ random spaces and on every
example domain).  Two sound `evalT` optimizations matter in practice: **short-circuiting**
empty-annihilated operands (∩/·/`<|`/`\||`/wrap/unwrap), which skips the many empty guarded
branches a union-of-cases program produces, and **memoizing `Literal → Trie`** so stable literal
tables (e.g. the n-queens `add`/`sub`/`upto`) build their trie once.

Benchmarks (`BENCHMARKS.md`) — with all six example domains now expressed as **pure** MORKL
(the sliding puzzle and n-queens use no grounded functions) — show the trie faster across the
board: datalog TC up to 24.6×, aunt up to 21.3×, prefix range queries 58–882×, Game of Life
4.7×, sliding puzzle 3–4×, n-queens 4–13×, and `meetAll` 18–116× over pairwise reduce
(`joinAll` ~parity).  Geometric mean ≈ 9× overall, ≈ 10× across the six example domains.

## Op-graph trie-native executor (execT) and the optimizer

The `RecursiveOpGraph` is the compiled IR: `transpile` lowers a `Routine` to a flat op-graph
(iterations become recursive subgraphs), `optimize` rewrites it, and an executor runs it over a
stack of frames.  The original `exec` (`GraphExec.scala`'s `runGraph`) is eval-based — it
rebuilds a `Space.Literal` and calls `eval` per node.  `execT` is the trie-native analog: space
slots hold `ITrie`, path slots hold interned `List[Int]`, and there are **no intermediate `eval`
calls and no `PathValue` allocations** — every node is a direct `ITrie` operation, and
`Iteration` walks the source trie's `IntMap` children directly.  Inputs are bound by **name**
(`ExtractPathRef`/`ExtractSpaceMention`), so the executors are robust to the optimizer reordering
nodes.

**Inlining & lowering — the executor-ready form.**  Before execution every routine is folded into
the graph so the executor does no Call dispatch.  Non-recursive Calls are **inlined**: `inlineCalls`
splices each callee's body (arguments substituted for parameters) to a fixed point, so `transpile`
yields a Call-free graph (n-queens `place→aoe`, sliding `→superpose/collapse` both reach 0 Call
nodes).  Union-saturating self-recursion — the datalog shape `r(m) = m ∪ r(next(m))` with `next`
extensive/monotone — is instead **lowered** to a `Fixpoint` subgraph: the body computes `next(cur)`
and exec/execT iterate `cur := next(cur)` to the least fixpoint (`ITrie ==` is structural).
`transitive_routine` thus transpiles Call-free; `execT(Fixpoint) == exec == eval`.  (Multi-mention
recursion such as `reachable`/`scc` is not yet matched and stays a Call node.)

**The optimizer — now well-formed by construction.**  Two passes: `optimize_sharing` (CSE — dedup
identical subgraphs) and `push_out` (LICM — hoist loop-invariant nodes, especially constant literal
tables, out of iteration subgraphs).  `push_out` was **rewritten**: the old version threaded one
mutable level→coordinate stack through a gather/recurse pair, and on deep nesting reused a deeper
level-map across sibling/ancestor scopes, so a node not re-hoisted at the inner level kept a
coordinate into the wrong graph (the malformed `(11,3)` downward coordinate that crashed `optimize`
on sliding 3×3).  The new pass is **coordinate-free until linearization**: every node gets a stable
id, inputs resolve to ids, each node's earliest-legal scope is the deepest scope among its inputs'
placements (constants → root; `Extract`s and each scope's result node pinned; subgraphs pinned — we
move nodes, never scopes), and a final top-down pass lays each scope out `[Extracts][interior topo]
[result]` with fresh coordinates.  Two subtleties the tests pinned down: a subgraph must be ordered
after **every** same-scope node its *body subtree* references (not just its `root.inputs`), else a
hoisted constant lands after the loop that uses it; and a scope whose result *is* an `Extract`
(identity-body iteration) must not duplicate it.  `optimize`'s `wellFormed`/`safe` guard is retained
as cheap defence but no longer triggers.  (The earlier lossy-`Constant`-round-trip bug stays fixed
via `LiteralCodec.encodeConst/decodeConst`.)

**Why `exec` had no business being slower than `eval`.**  The op-graph stores Literal/Constant
payloads as serialized strings; `execT` was re-decoding (base64 + parse + intern) and rebuilding the
trie on *every* node execution, while `evalI` holds live interned objects.  Process-wide string-keyed
caches (`iLiteralStr`/`internConstStr`) decode each distinct constant exactly once, turning every
later hit into one `O(1)` lookup.

Op-graph backend benchmark (`BENCHMARKS.md`, best-of-N ms).  `execT(inline+opt)` is the
executor-ready form; the last column is `execT(inline+opt)/evalI` (<1 ⇒ the compiled graph beats
the interpreter):

| program | evalI | exec | execT | execT(opt) | execT(inline+opt) | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=400 | 1.7 | 120.6 | 1.4 | 1.3 | 1.2 | 0.72 |
| n-queens n=6 | 7.1 | 118.0 | 33.5 | 29.1 | 0.9 | **0.13** |
| n-queens n=7 | 9.3 | 564.2 | 146.9 | 142.8 | 3.6 | **0.39** |
| union_iter | 0.0 | 0.5 | 0.0 | 0.0 | 0.0 | 0.48 |
| datalog tc n=40 | 1.7 | — | 1.1 | 1.0 | 1.0 | 0.57 |
| datalog tc n=80 | 17.6 | — | 11.8 | 11.9 | 11.9 | 0.68 |

With constants decoded once, Calls inlined, and recursion lowered, **`execT(inline+opt)` beats the
`evalI` interpreter on the substantial workloads** — n-queens (~3–8×), aunt (~1.4–2×), `union_iter`
(~2.5×), datalog (~1.5×).  (Temperature is *not* a counter-example despite its >1 ratio: both its
times are well under a millisecond — the query collapses to a near-empty result and the resident
grid is memoised on both sides — so that column is rounding noise, not a regression.  In absolute
terms execT runs it in ≤0.1 ms.)  The eval-based `exec` — which rebuilds a `Space.Literal` and calls
`eval` per node — is the slow path the trie-native executor replaces, and execT beats it everywhere;
constant-decode caching alone cut raw `execT` by an order of magnitude (n-queens n=7 1927→147 ms,
temperature 16384 78→0.1 ms), and inlining closed the rest.

## Bounded compilation and per-pass timing

A supercompiler trades compile time for run time, so compilation must itself be **bounded** and
**accounted separately from runtime**.  Two facilities (`MORKL.scala`):

- **`Deadline`** — a wall-clock bound (`Deadline.never` / `Deadline.inMillis`).  Every fixed-point
  pass polls it and stops *gracefully*: `optimize`, `all_forever`/`inlineCalls` return the best
  result reached so far.  This is sound because each pass is semantics-preserving — an early stop
  only forgoes further optimization, never correctness.
- **`Profiler`** — accumulates wall-clock time and call counts per named pass (`Profiler.off` is a
  zero-overhead sink, so un-instrumented call sites are unaffected).

`SC.Config.compileBudgetMs` (default ∞; the count caps `maxNodes`/`maxDepth`/`maxReduce` still
apply) bounds the driver: when it expires, `scCall` raises `CompileBudgetExceeded`, `run` catches
it and **falls back to interpreting the original program** — env = every routine reachable from the
configuration — reported with `converged = false`.  `compileCall` threads one shared deadline
through both the driver and the optimizer, so *total* compile time stays within the budget, and
times every phase into `SCReport.{compileMillis, phaseMillis}` (rendered by `SCReport.timing`):
`supercompile`, `transpile`, `push_out`, `optimize_sharing`.

`BENCHMARKS.md` adds a **"Compile time per pass"** table next to the runtime numbers.  The point is
concrete: temperature 16384 spends ~317 ms compiling (mostly transpiling a 16 k-literal table) for
a ~0.06 ms run — `compile/run ≈ 5600×` — exactly the regime a budget must bound, whereas
aunt/datalog sit at ≈1× or below.

> Implementation note / footgun: a single-line Scala 3 `catch case X => a; b; c` does **not** place
> `b; c` in the arm — they leak into the enclosing block and run unconditionally.  An early version
> of `run`'s budget fallback hit this, making *every* compile fall back to the un-optimized program;
> the fix is an explicit multi-line block for the catch arm.

## Publication-hardening pass (correctness, power, accounting)

A focused pass to make the supercompiler/optimizer hold up to scrutiny:

- **`Space.Fixpoint` is first-class.**  `Fixpoint(init, rec, body)` denotes the union-saturating least
  fixpoint `init ∪ body[init] ∪ body²[init] …` (`rec` binds in `body`).  It is composable and
  supercompilable: handled in `eval`/`evalT`/`evalI`, `transpile`↔`untranspile`, `subs`/`collect`,
  and all of `Matching` (free vars, capture-avoiding `subst`, `canon`, `instanceOf`, `embeds`, `msg`).
  Recursion lowering now produces this node rather than an ad-hoc graph construct.

- **SCC-aware inliner/lowerer (`lowerCalls`).**  Given a routine module it (1) rewrites each
  recognized union-saturating routine to a `Space.Fixpoint` (`asFixpoint` — single changing mention
  + identity base; covers single-mention `transitive` and multi-parameter `reachable`), (2) finds
  routines still in a call cycle, (3) **inlines** every acyclic routine into the entry and into each
  surviving recursive body, and (4) leaves genuine recursion (mutual, or unrecognized) as **honest
  residual `Call`s**, returned so the result is self-contained and directly evaluable.

- **Proper CSE incl. subgraph sharing.**  `optimize_sharing` is value-numbering hash-consing (O(n),
  exact keys — a lossy hash would be unsound).  It deduplicates flat nodes AND whole structurally
  identical iteration subgraphs, scoped so it only ever redirects to a visible (ancestor / earlier
  same-scope) node.  `Extract`s are scope-level-keyed bindings and are never merged across scopes
  (so a Fixpoint body's loop variable never collapses into an ancestor mention of the same name).

- **`push_out` (LICM)** is coordinate-free until linearization, well-formed by construction at any
  depth, and no longer guarded by a swallow-everything `catch` (a malformed graph is now a surfaced
  bug, not a silent revert).  `optimize` converges on a 64-bit **structural hash** rather than
  `show` strings, and reports per-pass **timing AND improvement** (push_out: nodes hoisted out of
  loops; optimize_sharing: duplicate nodes removed).

- **Bounded compilation, fully threaded.**  The compile `Deadline` is checked across the *whole*
  driver — `drive`, `reduce`, `scCall` — and `SC.Config.compileBudgetMs` now defaults to a **finite**
  10 s; on expiry the driver falls back to interpreting the original (`converged = false`).
  `optimizedAway` is reported explicitly when the whole program is evaluated to a constant at compile
  time, and the benchmark reports compile time, runtime, and their combined total.

- **Grounded audit.**  An executable audit pins that `interval`/`temperature` and the
  relational/recursive examples use **zero** grounded nodes; Game of Life is the lone deliberate
  grounded example (B3/S23 counting), with a plain-Scala reference used only for correctness checks.

- **Randomized property tests.**  300 random op-graph programs assert `transpile+execT` and
  `transpile+optimize+execT` both equal `eval` (and `evalT`/`evalI` agree); 60 random graphs assert
  `Space.Fixpoint` transitive closure equals an independent reference.  These immediately surfaced —
  and we fixed — a latent transpile bug: a scope whose body was a bare `Mention` (resolving to an
  ancestor or its own `rest`) didn't materialize a result node, so the executor read the wrong slot;
  transpile now appends a pass-through so a scope's result is always its last node.
