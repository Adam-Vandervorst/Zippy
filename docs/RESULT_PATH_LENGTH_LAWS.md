# Result path-length laws

For a path set `X`, `l(X)` is a lower bound on the length of every path in `X` and `u(X)` is an upper bound. Bounds for an empty set are vacuous; the canonical empty interval is `[∞, 0]`, while `[0, ∞]` is completely unknown. The public analysis retains the compositional interval as a fallback and accepts a Z3 result only when it tightens that interval.

## Paths

| Path | Lower and upper length |
|---|---|
| constant `p` | `|p|` |
| dereference `p` | its lexical assumption, then `lengthHint`, then the symbolic runtime length |
| concatenation `p · q` | `[l(p) + l(q), u(p) + u(q)]` |
| grounded path | its symbolic runtime length when closed; `[0, ∞]` when it captures a lexical binder |

## Set algebra

| Space | Compositional interval |
|---|---|
| `∅` | `[∞, 0]` |
| singleton `{p}` | `[l(p), u(p)]` |
| literal | exact minimum and maximum member lengths |
| `X ∪ Y` | `[min(l(X), l(Y)), max(u(X), u(Y))]` |
| `X ∩ Y` | `[max(l(X), l(Y)), min(u(X), u(Y))]` |
| `X \ Y` | `[l(X), u(X)]` |
| restriction `X <| P` | `[max(l(X), l(P)), u(X)]` |
| raffination | `[l(X), u(X)]` |
| composition `X × Y` | `[l(X) + l(Y), u(X) + u(Y)]` |

Union, intersection, and subtraction are also translated into Boolean formulas over their distinct set atoms. Z3 assigns a non-negative cardinality to every Venn region, constrains each atom with the existing result-size bounds, and zeros regions forbidden by structural subset/disjointness facts. A region can contain paths only where all of its member atoms' length intervals overlap. The result minimum is the minimum feasible-region lower endpoint, and the result maximum is the maximum feasible-region upper endpoint. Solver failure, timeout, or an oversized Boolean component returns the compositional interval unchanged.

This preserves correlations such as `X ∪ (X ∩ Y) = X` and proves that an intersection of disjoint length ranges is empty before a surrounding composition is analyzed.

## Binders and remaining spaces

| Space | Propagation law |
|---|---|
| iteration over `X` | analyze the body with head length exactly `1` and tail-space interval `[relu(l(X)-1), relu(u(X)-1)]` |
| fold over `X` | use the same head/tail assumptions; retain an exact accumulator length when the update preserves it, otherwise use its hint or `[0, ∞]` |
| identity fixpoint | the initial interval |
| binder-independent fixpoint step | interval union of the initial and step results |
| general fixpoint | `[0, ∞]` |
| wrap by `p` | add `[l(p), u(p)]` |
| unwrap by `p` | `[relu(l(X)-u(p)), relu(u(X)-l(p))]` |
| tails union/intersection | `[relu(l(X)-1), relu(u(X)-1)]` |
| prefix/suffix closure | `[1, u(X)]` (vacuous for an empty result) |
| tails closure | `[0, u(X)]` |
| range | a subset of `X`, hence `[l(X), u(X)]` |
| routine call or grounded space | symbolic runtime minimum/maximum when closed; `[0, ∞]` when it captures a lexical binder |

Mention assumptions, path-reference assumptions, `lengthHint`, and the existing `sizeHint`/result-size analysis are threaded through nested binders. Auxiliary cardinality facts that cannot be evaluated outside a binder's lexical scope are conservatively discarded rather than forcing an out-of-scope evaluation.
