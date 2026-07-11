# Residuals (omitted operators)

MORKL's path-set algebra is composition-centric: `Composition` (written `x`) concatenates every
path of its left operand with every path of its right operand, `A·B = { a·b | a ∈ A, b ∈ B }`.
In any such ordered algebra composition has two natural adjoints — the **residuals**, division-like
operators answering "what can I multiply by to land inside a given set":

- **Left residual** `y /: x` — all prefixes that lead to `y` inside `x`:
  `x /: y = { r | {r}·y ⊆ x }` — read "which prefixes `r` make `r·y` fit in `x`".
  Example: with `x = Test.Foo.{Bar.{1..6}, Baz.{1,2,3,A,B,C}, Cux.{Red,Blue}}` and
  `y = {1,2,3}`, the left residual is `{Test.Foo.Bar, Test.Foo.Baz}` — the places under which
  all of `y` occurs.

- **Right residual** `y :\ x` — all postfixes reachable after `y` inside `x`:
  `y :\ x = { r | y·{r} ⊆ x }` = `⋂_{g ∈ y} unwrap(x, g)`.
  With the same `x` and `y = {Test.Foo.Bar, Test.Foo.Baz}` the right residual is `{1,2,3}` —
  what can be appended to *every* path of `y` and stay inside `x`.

Together with composition they form the usual residuated structure over the prefix ordering:
`A·B ⊆ C  ⟺  A ⊆ C /: B  ⟺  B ⊆ A :\ C`. They subsume several derived queries (right residual
at a singleton divisor is `unwrap`; left residual generalizes "find every location containing this
sub-structure", the query-by-example primitive).

## Why they are omitted

Both operators are **universally quantified over the divisor**: membership of one result path
requires checking *all* paths of `y` against `x` (an intersection over the divisor for the right
residual; a subset test per candidate node for the left). That shape resists all of the engine's
speed machinery:

- **No incremental frontier.** The zipper evaluation model advances by single-key `Descend`
  moves whose child sets come from small per-node key computations. A residual's per-node answer
  flips between "everything" and "nothing" based on a *global* subset test of the divisor —
  there is no sound per-key decomposition to move along, so the movement calculus (and the
  constant-time frontier rewrites built on it) cannot express it without materializing.
- **No sharing-friendly recursion.** The eager trie implementations were whole-divisor loops:
  `rightResidual = ⋂_{g∈divisor} unwrap(dividend, g)` and `leftResidual` walked every dividend
  node running a full `subtraction(divisor, node).isEmpty` subset test — `O(|dividend-nodes| ×
  |divisor|)` with none of the hash-consing/short-circuit wins that make union/intersection fast
  on shared tries.
- **Anti-monotone in the divisor.** Growing `y` *shrinks* both residuals, so the incremental/
  semi-naive evaluation strategies (delta-driven, monotone-least-fixpoint based) don't apply,
  and the supercompiler has no sound rewrite laws to specialize them the way it does for the
  monotone core.

Since nothing in the corpus or the cornerstone programs needed them (both were expressible with
the core algebra where they appeared at all), they are **omitted from the language** rather than
kept as permanently-slow outliers: no `Space.LeftResidual` / `Space.RightResidual` constructors,
no evaluator or backend cases, no rewrite rules. This keeps the invariant that *every* operator
in the algebra has fast paths on all three execution models (set-of-paths reference, eager trie,
zipper) and a certified rule set.

If they return, the honest route is the one the rest of the algebra took: a denotational
membership characterization in `proofs/laws/`, movement-spec rules only if a sound per-key
decomposition exists (it likely does not — see above), and otherwise an explicitly-documented
materializing implementation.
