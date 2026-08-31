# Negative controls for the unbounded tier

Eight conjectures that are **FALSE** over the semantics of `src/main/scala/MORKL.scala`
`eval`, each the near-miss of a theorem that *is* in `proofs/unbounded/` and proved.

They exist because an encoding that proves everything proves nothing. A signature with an
inconsistent axiom set, a definition transcribed with the wrong polarity, or a guard that
silently degenerates would all still yield `SZS status Theorem` on the real corpus — and
would also yield it here. `proofs/unbounded/run.sh` therefore runs every file in this
directory and treats a **refutation as a HARD FAILURE**: the expected verdict is
`NOT-PROVED`.

Five of the eight are the exact shape of a bug `docs/traps.md` records as having actually
happened in this repository (reversed wrap/unwrap nesting order, unguarded
tails-intersection monotonicity, unguarded iteration split, `{}` vs `{eps}` in
tails-intersection).

| file | the false claim | the true theorem it near-misses |
|---|---|---|
| `not_wrap_nest_reversed.p`     | `wrap(wrap(A,U),V) = wrap(A, U++V)`        | `wrap_nest.p` — the order is `V++U` |
| `not_unwrap_nest_reversed.p`   | `unwrap(unwrap(A,U),V) = unwrap(A, V++U)`  | `wrap_nest.p` — the order is `U++V` |
| `not_ti_eq_tu.p`               | `ti(A) = tu(A)` unconditionally            | `tails_intersection.p` — only with ONE head |
| `not_ti_monotone.p`            | `A ⊆ B ⇒ ti(A) ⊆ ti(B)`                    | `mono_tails.p` — only if B adds no new head |
| `not_iter_split.p`             | iteration splits over ANY union            | `iteration_split.p` — head-disjoint only |
| `not_card_additive.p`          | `\|A ∪ B\| = \|A\| + \|B\|` unconditionally      | `card_subadd.p` — `≤`, with `=` only when disjoint |
| `not_tu_cap_equality.p`        | `tu(A ∩ B) = tu(A) ∩ tu(B)`                | `tails_union.p` — `⊆` only |
| `not_restr_identity.p`         | `restr(X,Y) = X`                           | `restriction.p` — only when Y contains ε |

MEASURED, 2026-08-31, vampire 5.1.0 (commit 7b2f410), `--mode casc -t 60s`: all eight time
out; none is refuted. Their proved counterparts close in 0.0 s – 6.2 s from the same axiom
modules — `restriction` 0.3 s, `tails_union` 0.0 s, `tails_intersection` 0.2 s, `mono_tails`
0.6 s, `iteration_split` 0.0 s, `card_subadd` 0.6 s, `wrap_nest` 6.2 s.
`run.sh` re-runs them at `NLIMIT=45` by default, with the same outcome.

Vampire reports `Timeout`, not `CounterSatisfiable`: the theories are not finitely
saturable, so absence of a refutation is the strongest signal available here. That is
weaker than a countermodel and is recorded as such — the control catches an encoding that
proves too much, not one that proves too little.
