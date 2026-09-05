# The two-tier correlated spatial domain

The executable domain is
[SpatialDomain.scala](../src/main/scala/SpatialDomain.scala) and its acceptance suite is
[SpatialDomainCheck](../src/test/scala/SpatialDomainCheck.scala); the summarized tier's own laws
remain in [design_spatial_lattice.md](design_spatial_lattice.md) and `proofs/spatial*`.

## 1. Why a second tier

The cost analysis projected every operand to independent scalars (a size interval, a length interval,
a head count) before a transfer ran.  What decides operational cost is *relational*: which keys two
operands share, how many distinct objects an n-ary operation sees, whether a result is an operand by
pointer, where a path sits in the order, how many paths lie under one prefix.  Those facts were gone by
the time an operation was priced, and the loss compounded through puzzle15's projection chain. The
domain below keeps them.

## 2. The carrier

One hash-consed DAG per analysis (`Arena`), three node kinds:

| node | meaning (γ) | tier |
|---|---|---|
| `XTrie(terminal, children)` | { V : ε∈V ⇔ terminal, heads V = keys, ∀k. tails_k V ∈ γ(children k) } | exact |
| `XChoice(alts)` | ⋃ γ(alt) — finitely many alternatives for the subtrie at this prefix, decided independently at each prefix (BDD-like decision sharing) | exact |
| `XSumm(t : SpatialType)` | the product γ of the bounded shape × length histogram (`SpatialTyping.accepts`) | summarized |

The exact tier is everything above the first `XSumm`; a value may be exact where the analysis can
afford it and summarized below.  Nodes are interned per arena (structurally equal nodes are one
object, a shared subtrie is one node), and identity is a *value*: `XNode.key` is the structural
fingerprint and `equals`/`hashCode` are structural, so two analyses produce equal values and no arena
id ever leaves the arena.  Nothing is process-wide (§7).

An abstract value is `Abs(node, alias)`; the **alias channel** says which object the value denotes
when that is known: `Is(m)` (the object bound to input mention `m`, by pointer), `Fresh` (an object
this analysis' operation built), `Unknown`.

## 3. Order, join, meet, projection, widening

| | exact ⊑/⊔/⊓ exact | summ ⊑/⊔/⊓ summ | exact against summ |
|---|---|---|---|
| ⊑ | structural: same ε, same head set, children pointwise; a choice is below when every alternative is, above when some alternative is | `SpatialType.leq` | exact ⊑ summ through the projection; summ ⊑ exact is never claimed |
| ⊔ | the choice of the two when it fits `budget.alternatives`, else the lub of the projections (**widening** `alternatives-budget`) | `SpatialGamma.lub` (**widening** `summarized-join`) | lub of the projections |
| ⊓ | structural (a disagreement on ε, on a head set or in a child is ⊥) | `SpatialType.meet` (⊥ when uninhabited) | filter the enumerable alternatives by γ; otherwise the exact operand stands (⊒ the meet, sound) |
| projection | `Domain.summary`: a trie node is `ε ∪ ⋃_k k·child_k`, built by the CERTIFIED `Wrap`/`Union` transfers (`SpatialTyping.infer`); a choice projects to the lub of its alternatives; memoised per node | identity | — |
| widening | `Domain.widen`: join, then `SpatialRecursion.widenType` past the budget (**widening** `iteration-widening`) | | |

`α(v)` is the exact trie of a concrete value; γ is `Domain.member`.  `SpatialDomainCheck` checks on
the finite universe: γ∘α, join an upper bound, meet a lower bound, `leq ⇒ γ-inclusion`, every node
below its projection, and that the exact operations are **exact** (γ(op#(a,b)) = {op(x,y)}) against
the reference evaluator for every binary and unary operation of the algebra.

## 4. Operations

Exact ⨯ exact is computed structurally, mirroring the trie algebra's own recursion (`union` merges
child maps, `inter` keeps common keys and drops empty children, `sub` keeps left keys, `restrict`
descends common keys and accepts the whole left subtrie at a terminal prefix, `raff` drops it, `comp`
grafts the right operand at every terminal, `wrap`/`unwrap` nest and descend, `tailsUnion`/`tailsInter`
fold over the children, `range` slices the enumerated canonical order).  Anything touching an `XSumm`
goes through the summarized tier's transfers by building the two-mention term and calling
`SpatialTyping.infer` on it — the certified transfers are reused, never re-implemented.  Choices
distribute (the product of the alternative counts must fit the budget, else `alternatives-budget(op)`).

The `Abs` forms carry the alias channel through the executors' identity cases: a result that **is** an
operand node is that operand's object (`x ∪ x` is `x`; `x ∪ y` with `y ⊆ x` returns `x` by pointer,
exactly as `ITrie.unionR` does), otherwise it is `Fresh`; an `unwrap` navigates into a sub-object
(`Unknown`).

## 5. The facts a transfer may read (`DomainFacts`)

| fact | exact tier | summarized tier |
|---|---|---|
| cardinality, length | exact intervals | `SpatialType.size/len` |
| per-prefix fan-out `fanOut` | [must-present heads, all heads] | shape head count |
| per-prefix fibre cardinality `fibre(prefix)` | exact | `Unwrap` transfer |
| order extrema `orderMin/orderMax` | the extremum, when every alternative agrees — `Range(x,0,1)`, `Range(x,-1,0)` are exact | `Shape.orderMin/orderMax` |
| `rank(p)` (ordered frontier position) | exact | — |
| `headDisjoint(a, b)` | exact head sets | `Shape.possibleHeads` (the certificate tier keeps it past the caps) |
| `mustAlias`, `mayAlias` | the alias channel: same input mention ⇒ must; two fresh results ⇒ never | |
| `distinctLive(ops)` | [must-live pairwise non-aliasing operands, may-live distinct groups] | |
| `provenReuse(result, ops)` | the operand the result is, by pointer | |
| pointer-preserving sharing | a shared subtrie is one node (`XTrie.children("a") eq children("b")`) | |

Correlations are never projected away before a transfer reads them: the exact tier keeps
cardinality, key layout, order and fibres in one structure; the summarized tier keeps them as the
reduced product's per-depth `K_d`/`E_d` and the shape's heads and extrema.

## 6. Survival past the shape caps

`Shape.MaxDepth` and `Shape.MaxHeads` apply only to `XSumm`.  A 15-deep exact value keeps its head
disjointness, its extrema and its per-prefix fibres (`SpatialDomainCheck`: 16 one-tile fibres compose
to a size-1 path exactly, no `Shape.top`), and a 40-head value keeps an exact fan-out and an exact
first/last selection where the summary can only bracket.

## 7. Scoping and certificates

Every cache is inside one `Domain` (arena, summaries, sizes, lengths); nothing is static.  Results
are therefore invariant under prior analyses in the same JVM (checked: the same analysis before and
after 20 unrelated analyses and arenas yields the same value, alias and certificate).

`Domain.certificate` is the immutable `DomainCert(budget, widenings)`: every budget crossing is a
named `Widening(reason, before, after, sizes, lengths)`.  A widening may lose precision but may not
change a must fact or a growth class: the after value is checked to be ⊒ every before value at the
crossing.  A run with no widening reports `exact`.

## 8. Provenance

Every node records its `Cause` in the arena — an input mention, a literal, an operation over operand
nodes, an alternative of a join, a fixpoint round, a widening, a summarisation — indexed by the node.
The same DAG serves the denotational reading (a node's meaning is its structure) and the resource
reading (what was computed from what), without conflating them. The cost analysis attaches the event sites that
consumed a node to the same table.
