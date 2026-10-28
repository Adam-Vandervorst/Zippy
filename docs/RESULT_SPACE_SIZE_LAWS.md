# Result-space cardinality laws

This document states the sound laws used by the result-size constraint graph. Let `|X|` denote the concrete cardinality of a path set, `L(X)` and `U(X)` its abstract lower and upper bounds, `[p]` the zero-or-one indicator of proposition `p`, and `ε` the empty path. `∞` means that cardinality alone gives no finite ceiling.

The original compositional interval analysis remains unchanged as `ResultSpaceSize.estimateBaseline`. These laws form a separate refinement, and the public estimate combines lower bounds with `max` and upper bounds with `min`. Consequently a law or solver failure cannot weaken the baseline.

## Boolean set operations

For union, intersection, and subtraction:

```text
max(|A|, |B|) ≤ |A ∪ B| ≤ |A| + |B|
0 ≤ |A ∩ B| ≤ min(|A|, |B|)
max(0, |A| - |B|) ≤ |A \ B| ≤ |A|
```

The Z3 Venn-region encoding additionally preserves repeated operands and proves subset/disjointness. Selector operations also export relations across otherwise opaque atoms: intersection, subtraction, restriction, raffination, and range results are subsets of their selected input; a subtraction is disjoint from every subset of its removed operand; and matching restriction/raffination results are disjoint. Z3 sets the corresponding impossible Venn regions to zero. It therefore derives absorption, idempotence, cancellation, and related identities without relying only on syntactically repeated atoms.

## Restriction

`A <| P` retains exactly the paths of `A` prefixed by a path in `P`:

```text
(A <| P) ⊆ A
0 ≤ |A <| P| ≤ |A|
|A| = 0 or |P| = 0  =>  |A <| P| = 0
ε ∈ P                  =>  |A <| P| = |A|
```

If every path of `A` is covered by `P`, the result equals `A`. If no path is covered, it is empty. Cardinalities alone cannot distinguish those two cases, so the general lower bound remains zero.

Raffination is the complementary partition of the left operand and has the same subset/upper law.

## Composition

Composition concatenates every left path with every right path. Fixing either operand makes concatenation injective in the other operand:

```text
max(|A| · [|B| > 0], |B| · [|A| > 0]) ≤ |A × B| ≤ |A| · |B|
|A| = 0 or |B| = 0                       => |A × B| = 0
|A| = 1                                  => |A × B| = |B|
|B| = 1                                  => |A × B| = |A|
```

The upper product can be loose because different pairs can concatenate to the same path. No stronger general lower bound follows from cardinalities alone.

## Iteration

Iteration ignores `ε`, groups source paths by their first item, binds the group head and its set of tails, evaluates one body per distinct head, then unions the branch results. Let `G(S)` be the number of distinct headed groups and `B_g` the body result for group `g`:

```text
0 ≤ G(S) ≤ |S|
|S| ≥ 2                         => G(S) ≥ 1
S is epsilon-free and |S| > 0  => G(S) ≥ 1

|Iter(S, B)| = |⋃g B_g|
|Iter(S, B)| ≤ Σg |B_g| ≤ |S| · max_g |B_g|
G(S) > 0 and every |B_g| ≥ l   => |Iter(S, B)| ≥ l
```

The tail-set binding for a branch has cardinality between one and `|S|`. This gives the body analysis its contextual assumption.

If the body is independent of both iteration binders, every branch is the same set `B`, so unioning groups does not multiply it:

```text
G(S) = 0  => Iter(S, B) = ∅
G(S) > 0  => Iter(S, B) = B
|Iter(S, B)| ≤ [|S| > 0] · U(B)
```

The upper indicator permits the epsilon-only case and is therefore safe but not always exact. The lower indicator is known when the source is epsilon-free and nonempty, or when its lower cardinality is at least two.

A nested iterator over the outer branch's tail set is a flattened union-map when its inner body does not inspect the inner tail set:

```text
Iter(S, x, xs, Iter(xs, y, ys, B(x, y)))
  = ⋃x ⋃y B(x, y)
|Iter(...)| ≤ |S| · max(x,y) U(B(x, y))
```

For each outer head, the inner head groups partition its tail paths, and the outer tail groups in turn partition the headed source paths. The source cardinality is therefore consumed once, rather than once per syntactic iterator. This is the cardinality view of `union(S.map(body))`.

## Unwrap

Unwrap retains paths with one fixed prefix and removes that prefix. Removing a fixed prefix is injective on the retained subset:

```text
0 ≤ |Unwrap(S, p)| ≤ |S|
p = ε  => Unwrap(S, p) = S
S = ∅  => Unwrap(S, p) = ∅
```

When the prefix or source depends on an iteration binder, this finite `|S|` ceiling replaces the previous opaque `∞`. Without prefix-distribution information, cardinality alone gives no positive lower bound.

For a literal finite relation `R` and a dynamic prefix whose length `k` is known, the graph computes the maximum prefix fiber:

```text
fiber(R, k) = max_p |{ suffix | p · suffix ∈ R and |p| = k }|
|Unwrap(R, p)| ≤ fiber(R, k), when |p| = k
```

Iterator heads have known length one, and concatenations add known lengths. This exposes finite function/relation degrees—such as one output for a literal arithmetic relation—to the enclosing map and product constraints without knowing the concrete iterator value.

## Range

Range is an ordered border slice, so its cardinality is an exact function `ρ` of the source cardinality. For `n = |S|`, the implementation normalizes its bounds as follows:

```text
lower(0) = 0
lower(k > 0) = k - 1
lower(k < 0) = n + k

upper(0) = n
upper(k > 0, start = 0) = k
upper(k > 0, start ≠ 0) = k - 1
upper(k < 0) = n + k

lo = clamp(lower(start), 0, n)
hi = clamp(upper(end), 0, n)
ρ(n, start, end) = max(0, hi - lo)
|Range(S, start, end)| = ρ(|S|, start, end)
```

Mixed negative/positive bounds make `ρ` non-monotone, so it is unsound to obtain an interval by simply applying `ρ` to the two interval endpoints. The graph keeps the exact `ρ` relation when source size is exact; otherwise it retains the baseline ceiling until a piecewise range constraint is introduced.

## Tails operations and closures

`TailsUnion` drops one item from every headed path and ignores `ε`. Different heads can produce the same tail:

```text
0 ≤ |TailsUnion(S)| ≤ |S|
|S| ≥ 2                         => |TailsUnion(S)| ≥ 1
S is epsilon-free and |S| > 0  => |TailsUnion(S)| ≥ 1
```

`TailsIntersection` intersects the tail sets of all head groups:

```text
0 ≤ |TailsIntersection(S)| ≤ |S|
S = ∅ => |TailsIntersection(S)| = 0
```

Prefix and suffix closure exclude `ε` but contain the complete original path for every headed source member. A set contains at most one `ε`:

```text
max(0, |S| - 1) ≤ |PrefixClosure(S)| ≤ ∞
max(0, |S| - 1) ≤ |SuffixClosure(S)| ≤ ∞
S is epsilon-free => |S| ≤ |PrefixClosure(S)| and |S| ≤ |SuffixClosure(S)|
```

Tails closure includes every original path (drop zero items), all proper tails, and `ε` for headed paths:

```text
|S| ≤ |TailsClosure(S)| ≤ ∞
S = ∅ => |TailsClosure(S)| = 0
```

A finite upper bound for the closure operations requires path-length information in addition to result-space cardinality.

## Optimization and graph construction

The same constraint analysis is run on both the raw source and `Supercompiler.normalize(source).space`; `Supercompiler.optimizedResultSize(source)` exposes the latter directly. Source normalization removes identities, constant cases, distributive degeneracies, nested ranges, closure idempotence, and iteration special cases before graph construction. The optimized graph therefore contains far fewer repeated Boolean atoms, while the operation laws above continue to constrain the surviving non-Boolean nodes.
