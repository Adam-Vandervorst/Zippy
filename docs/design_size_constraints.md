# Constraint-based size analysis — design plan

## Problem

`Lower.sizeBounds` is a bottom-up, **non-relational** interval analysis: every node's
interval is a function of its children's intervals alone.  It therefore loses all
*correlation* between occurrences of the same subterm:

- **over-estimate** — `x \/ (x /\ y)`:  true size is `|x|` (absorption), but the analysis
  computes `hi = ⌈x⌉ + min(⌈x⌉, ⌈y⌉)` because the union transfer treats its operands as
  independent sets;
- **under-estimate** — `x /\ (x /\ y)`:  true size is `|x ∩ y|`, but the intersection
  transfer zeroes the lower bound (`lo = 0`) because it cannot see that the right operand
  is *contained in* the left one.

The tightness report (`SizeBoundsReport`, build.log 2026-07-13) shows the same failure
class at scale: 39 % of corpus instances have a vacuous lower bound, and the worst upper
bounds compound multiplicatively through nests whose operands are in fact correlated.

The fix is a **relational** abstract interpretation: name every distinct subterm, generate
*constraints* relating their cardinalities, and extract bounds by solving/propagating the
constraint system instead of a single bottom-up sweep.

## Architecture: two tiers over one constraint generator

```
            Space term
                │  hash-consing (shared subterms → one node)
                ▼
            Term DAG ──────────────► seed intervals  (existing Lower.sizeBounds, unchanged)
                │
                │  constraint generation (one schema per constructor + derived facts)
                ▼
   ┌── constraint system: vars n(t), eps(t); relations ⊑, disj; equations ──┐
   │                                                                        │
   ▼ tier 1 (default, in-process)                 ▼ tier 2 (optional, exact)│
 bound propagation to fixpoint                  z3 Optimize (νZ):           │
 ("belief propagation" style local              maximize / minimize n(root) │
  narrowing on a worklist)                      via the existing sh("z3")   │
                                                pipeline plumbing           │
```

Both tiers consume the *same* generated constraints, so tier 2 doubles as the test oracle
for tier 1: propagation may be looser than the LP/SMT optimum but must never be tighter.

### Variables

For every hash-consed node `t`:
- `n(t) ∈ ℕ` — result size, with interval `[lo, hi]` seeded from `sizeBounds`;
- `eps(t) ∈ {0,1}` — is ε in the result; headed count is *derived*: `hd(t) = n(t) − eps(t)`
  (cleaner than the current separate `loHeaded`, and exact by definition).

Hash-consing is what makes the system relational at all: in `x \/ (x /\ y)` the two `x`
occurrences are **one node**, hence one variable.  A light canonicalization pass runs
first (sort commutative operands, local idempotence/absorption — reusing `Lower`'s laws)
so ACI-equal subterms also share nodes; no full e-graph needed initially (see Risks).

### Fact relations (Horn saturation)

Two binary relations over DAG nodes, saturated to a fixpoint by Datalog-style rules,
bounded to the existing nodes:

**Subset `t ⊑ s`** (eval(t) ⊆ eval(s)) — seeded structurally:
`a∩b ⊑ a, a∩b ⊑ b`; `a∖b ⊑ a`; `a<|y ⊑ a`; `a\|y ⊑ a`; `a ⊑ a∪b, b ⊑ a∪b`;
`Range(a,_,_) ⊑ a`; `init ⊑ Fixpoint(init,…)`.  Closure rules:
- reflexive, transitive;
- `c ⊑ a ∧ c ⊑ b ⟹ c ⊑ a∩b` (meet is a glb);  `a ⊑ c ∧ b ⊑ c ⟹ a∪b ⊑ c` (join is a lub);
- congruence/monotonicity: `a ⊑ a' ⟹ p×a ⊑ p×a'`, `a·c ⊑ a'·c`, `a∖b ⊒ a∖b'` when `b ⊑ b'`, …

**Disjointness `disj(a,b)`** (eval(a) ∩ eval(b) = ∅) — seeded from:
- `a∖b` vs `b`;  `x<|y` vs `x\|y` (the certified partition, law_raff_restrict_algebra);
- wrap-disjoint cylinders: `p×a` vs `q×b` with incomparable constant heads
  (law_wrap_disjoint);
- literals with disjoint path sets.
Closure: `disj(a,b) ∧ c ⊑ a ⟹ disj(c,b)`.

### Constraint schemas (each one a certified cardinality law)

| node | constraints |
|---|---|
| `u = a∪b` | `n u ≥ max(n a, n b)`; `n u ≤ n a + n b`; **if `disj(a,b)`: `n u = n a + n b`**; with meet node m=a∩b present: `n u = n a + n b − n m` (inclusion–exclusion) |
| `i = a∩b` | `n i ≤ min(n a, n b)`; **relational lower**: for any `c` with `c ⊑ a ∧ c ⊑ b`: `n i ≥ n c` (via `c ⊑ i` closure); if `disj(a,b)`: `n i = 0` |
| `d = a∖b` | `n d ≤ n a`; `n d ≥ n a − n b`; with meet node: `n d = n a − n(a∩b)` (partition `d ⊎ (a∩b) = a`) |
| `r = x<|y`, `f = x\|y` | `n r + n f = n x` when both nodes exist (partition); each `⊑ x` |
| `c = a·b` | `n c ≤ n a · n b` (nonlinear — tier 1 propagates with interval endpoints, tier 2 uses NIA); `n a ≥ 1 ∧ n b ≥ 1 ⟹ n c ≥ max(n a, n b)` (indicator constraint) |
| `w = p×a` | `n w = n a`; `eps w = eps a ∧ (p = ε)` |
| `iter(src, body)` | `hd(src) ≥ 1 ⟹ n ≥ n(body under widened binders)`; `n ≤ g·⌈body⌉` with group count `1 ≤ g ≤ hd(src)`; **keyed bodies** (`keyedBy`): groups pairwise disjoint ⟹ `n ≥ g·⌊body⌋` |
| guards (`provablyEpsSubset`) | `n ≤ 1 ∧ hd = 0` |
| `Fixpoint(init, …)` | `n ≥ n init` (accumulator only grows); `hi = ∞` |

Subset feeds intervals directly: `t ⊑ s ⟹ n t ≤ n s` — propagated as
`hi(t) := min(hi t, hi s)` and `lo(s) := max(lo s, lo t)`.

**Worked examples** (both motivating cases close under M1 alone, before any
inclusion–exclusion):
- `u = x ∪ (x∩y)`:  `x ⊑ x`, `x∩y ⊑ x` ⟹ (lub rule) `u ⊑ x`; with `x ⊑ u` structural ⟹
  `n u = n x` — interval collapses to `[⌊x⌋, ⌈x⌉]`.  Exact.
- `i = x ∩ (x∩y)`:  let `b = x∩y`; `b ⊑ x ∧ b ⊑ b` ⟹ (glb rule) `b ⊑ i`; with `i ⊑ b`
  structural ⟹ `n i = n b`.  Exact.
- NOAA report row: once a query is phrased with both partition halves
  (`world<|band` and `world\|band`), the partition equation replaces both vacuous lower
  bounds with an exact sum.

### Tier 1: bound propagation ("belief propagation" flavor)

Each constraint is a local **propagator** that narrows the intervals of its participant
variables in every direction (e.g. the partition equation `n r + n f = n x` refines all
three).  A worklist runs propagators whose inputs changed, to quiescence.

- **Termination**: every update strictly tightens an integer interval (lo only rises,
  hi only falls, both within `[0, INF]`), so the fixpoint is reached in finitely many
  steps; a `Deadline`-style budget caps pathological chains (an early stop is sound —
  intervals are valid at every intermediate state).
- **Monotone and order-independent** (each propagator is a monotone narrowing on the
  product lattice), so the fixpoint is unique — no message schedule sensitivity, which is
  the well-behaved corner of belief propagation.
- **Cost**: O((nodes + facts) · rounds); corpus programs are tiny.  For use inside
  rewrites, memoize per `optimized()` run (the analysis is pure per term).

### Tier 2: solver-backed exact bounds

Emit the same system as SMT-LIB2 over `Int` with z3's `(maximize (n root))` /
`(minimize (n root))` (νZ).  z3 is already a hard dependency of the proofs pipeline and
`EquivPipeline.sh` provides the shell plumbing.  Uses:
1. **oracle tests**: on corpus samples, assert `propagation ⊇ z3-optimum ⊇ |eval|`;
2. an on-demand `sizeBoundsExact(s, budget)` API for reports and one-off tooling;
3. LP relaxation note: if z3 Optimize proves too slow on big DAGs, the linear subset of
   the system relaxes soundly to LP (relaxed max ≥ integer max, relaxed min ≤ integer
   min — bounds stay valid), so an LP fallback is possible without new soundness
   arguments.

### Certification discipline

Every constraint schema gets a law certificate in `proofs/laws/` via
`scripts/gen_law_obligations.py`, like the rewrite laws: inclusion–exclusion, the
subtraction partition, subset-monotonicity of each constructor, the disjoint-union sum.
Several are already certified (raff/restrict partition, wrap-disjoint).  The propagators
then implement *only* certified equations — same trust story as `Lower`.

## Integration points

1. `Lower.sizeBounds` stays as-is (seed + fast path for rewrites).
2. New `Lower.sizeBoundsRel(s)` = tier 1; behind it, `sizeBoundsExact` = tier 2.
3. `SizeBoundsReport` gains a column: seed vs relational vs (sampled) exact — the
   tightness deltas ARE the evaluation of this design.
4. Rewrites (`SizeEmpty`, `provablyHeaded`-gated hoists) may consult tier 1 behind a
   `Tuning` flag once the cost is measured; they must never consult tier 2.

## Status

Tier 2 is IMPLEMENTED (`src/main/scala/SizeConstraints.scala`, `SizeZ3.bounds`) with the
M1+M2 constraint set: hash-consed DAG, ⊑ saturation (structural seeds, transitivity,
glb/lub incl. the child-vs-child cases, wrap congruence), subtraction ⊑-annihilation,
restriction/raffination partition equality and partition-union exactness, disjoint-cylinder
union sums, exact `Range` windows, `TailsUnion ≤ hd(src)`, the relational rest-mention
bound, and eps (ε-membership) as a 0/1 variable making the headed count derived.  The
system is kept LINEAR (multiplicative bounds use baseline-constant coefficients), solved
by z3 Optimize in box mode (min n, max n, min hd), seeded with the baseline intervals of
every node (dominance by construction), and falling back to the baseline on any failure —
including `scopesOk` rejection (duplicate/free-clashing binder names, referenced `_`),
which is what makes the adversarial-variable reading of binder-dependent nodes sound.

Verified (`morkl.SizeZ3Check`): both motivating shapes exact — `x ∪ (x∩y)` → [3,3] from
baseline [3,6]; `x ∖ (x∩(x∩x))` → [0,0] from [0,∞) — the partition program pins |x|
exactly ([4,4] from [0,8]); suite programs and all 1000 corpus programs (open AND one
closed instance each): dominated everywhere, sound everywhere; strict improvements on 97
closed + 13 open corpus instances; ~40 ms/query.

Remaining: M3 (lazy meet variables + inclusion–exclusion, keyed-iteration sums),
certificates for each constraint schema, and the tier-1 in-process propagator.

## Milestones

- **M1** — DAG + hash-consing + ⊑/disj saturation + subset/interval propagation.
  Acceptance: both motivating examples exact; corpus soundness suite green; report
  vacuous-lower % strictly down, no upper regression.
- **M2** — partition and disjoint-union equalities (restriction/raffination, subtraction
  meet, wrap-disjoint cylinders).  Acceptance: NOAA-style rows exact when both halves
  occur; distinct-head literal unions exact.
- **M3** — lazy meet variables + inclusion–exclusion + indicator constraints for
  composition/iteration nonemptiness; keyed-iteration sum lower bounds.
- **M4** — z3 Optimize backend + oracle test + certificates for every schema.
- **M5** — report integration, corpus tightness deltas in build.log, optional Tuning
  flag for rewrite-time use.

## Risks / alternatives considered

- **Constraint blowup**: meet variables for every union pair are quadratic — introduce
  lazily (only for pairs with shared support or an existing ⊑ path).  Budgeted saturation.
- **Nonlinearity** (composition, iteration): tier 1 propagates products with interval
  endpoints (already sound today); tier 2 accepts NIA or falls back to McCormick-style
  linearization with the seed intervals as the box.
- **Full e-graph canonicalization** (egg is already in-repo for laws): would subsume the
  ACI pass and find more congruences; deferred — the light pass covers the motivating
  cases, and the e-graph can later *feed* ⊑ facts without changing the solver.
- **Octagon/polyhedra domains**: strictly more general relational domains, but heavy
  dependencies and no story for the set-specific facts (partition, disjointness,
  headedness) that carry most of the tightness here.
