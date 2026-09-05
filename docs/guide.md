# Development Guide

Guiding principles for extending and optimizing Zippy. Read [ALGEBRA.md](ALGEBRA.md) first for the core
algebra; see [atlas.md](atlas.md) for the component map and [traps.md](traps.md) for hard-won lessons.

- **Do not touch the core algebra** described in [ALGEBRA.md](ALGEBRA.md). Weigh any other representation
  carefully if it cannot be re-expressed in the core operators and compositions thereof. If an abstraction
  needs to be added, ask the user first.

- **Graph and trie asymptotics are central to the project, subtle, and data-distribution dependent.** For
  example, a trie intersection can ignore entire subtries based on a disjoint prefix, and shortcut-accept
  entire matching subtries based on pointer equality; re-ordering the trie paths can completely change the
  conditional probability of either shortcut at a given level of the trie. Concretely:

  ```text
  {a: {v: {x, y}}}  /\  {u: {v: {x}}, w: {v: {x}}}
      → disjoint, decided at the TOP level

  {x: {v: {a}}, y: {v: {a}}}  /\  {x: {v: {u, w}}}
      → disjoint, but only decidable at the BOTTOM level

  let S = {a}:
  {x: {v: S, p: {b}}}  /\  {x: {v: S, q: {c}}}
      → evaluates to {x: {v: S}} at the MIDDLE level
  ```

- **The algebra and its derivatives are extremely lawful**, which gives rise to many families of laws.
  Resist the urge to specialize an optimization to any given program: the reason it can be optimized
  generalizes to many other programs (and the most important programs to optimize are yet to come). Prefer,
  in descending order:

  1. Manually proving theorems that enable powerful transformations;
  2. then lemmas that let an ATP prove the lowering;
  3. then querying local laws;
  4. then, last, manually inferring laws — and if you see one, many duals and generalizations are hiding.

- **Performance comes from multi-stage lowering with strong lawful optimization at each stage.** The only
  valid purpose of a constant-factor optimization is to let you observe scaling laws on larger problems.
  Multiple levels of counters and cost models can guide optimization toward different backends; and a subset
  of cost metrics is monotone across lowering stages — optimize those to exhaustion, since gains there never
  regress downstream.

- **High multiplicity of stage implementations ("components") in a pipeline is a feature, not code bloat.**
  As long as a component follows the same interface — or the interface of a composition of existing
  components — it can be differentially validated, even across different languages.

- **Specialized algorithm implementations must earn their keep.** Tremendous effort has been put into tools
  for formal methods and optimization; reach for them. For example, "lowering structural tree filters into
  state machines" should resolve to MONA, and "minimal and maximal assignments of approximate space sizes"
  should resolve to Z3.
