# Engineering Guide

## Algebra First

Do not change the core algebra described in [ALGEBRA.md](ALGEBRA.md). Treat every other representation with caution when it cannot be re-expressed using core operators and their compositions. Ask the user before adding an abstraction.

## Preserve Distribution-Sensitive Asymptotics

Graph and trie asymptotics are central, subtle, and data-distribution dependent. A trie intersection can reject whole subtries from a disjoint prefix or accept matching subtries by pointer equality. Path ordering changes the conditional probability of either shortcut at every level.

For example, `{a: {v: {x, y}}} /\ {u: {v: {x}}, w: {v: {x}}}` is disjoint at the root, whereas `{x: {v: {a}}, y: {v: {a}}} /\ {x: {v: {u, w}}}` is disjoint only at the leaf level. Conversely, with `S = {a}`, `{x: {v: S, p: {b}}} /\ {x: {v: S, q: {c}}}` preserves `{x: {v: S}}` at the middle level.

## Generalize Optimizations Through Laws

The algebra and its derivatives are highly lawful. Do not specialize an optimization to one program: its justification usually generalizes, and future programs are the important target.

Prefer, in order:

1. Manually proved theorems that enable broad transformations.
2. Lemmas that let an automated theorem prover establish a lowering.
3. Queries for local laws.
4. Manually inferred local laws.

When a law appears, look for its duals and generalizations.

## Optimize by Staged Lowering

Use multi-stage lowering and lawful optimization at each stage. Constant-factor work is justified only when it makes scaling laws observable on larger problems. Use counters and cost models to choose among backends, while exhaustively targeting the set-monotone behavior shared across stages.

## Prefer Composable, Differentially Checkable Components

Many pipeline components are a feature, not code bloat, when each implements a shared interface or the composition of existing interfaces. Such components can be differentially validated, including across languages.

## Use Existing Solvers Where They Fit

Specialized algorithms must justify their cost. Prefer established formal-methods and optimization tools when the problem matches them: lower structural tree filters to state machines for MONA; use Z3 for minimum and maximum assignments of approximate space sizes.
