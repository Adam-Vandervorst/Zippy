# zipper-egg-tests

The certified egg track for the SpaceZipper algebra. **Three notions of the same programs**, each a
layer, all cross-checked:

1. **SET OF PATHS** — the sound REFERENCE: [`../formal.egg`](../formal.egg) models Scala's `exec`,
   eager evaluation of the Space algebra over path sets (no zipper logic; zippers are an
   *optimization* and must be observationally equivalent to this).
2. **EAGER TRIE** — [`../zipper-impl.egg`](../zipper-impl.egg): the recursive `ITrie` set
   operations on sorted child lists.
3. **ZIPPER** — [`../zipper.egg`](../zipper.egg): the movement spec (cursors, virtual operators,
   local observations).

| file | role | source of truth |
|---|---|---|
| [`formal-prelude.egg`](formal-prelude.egg) | SET-OF-PATHS reference rules (sorts `Path/Space`) | extracted from [`../formal.egg`](../formal.egg) |
| [`prelude.egg`](prelude.egg) | MOVEMENT SPEC rules (sorts `B/KL/Z/C/Body`) | extracted from [`../zipper.egg`](../zipper.egg) |
| [`impl-prelude.egg`](impl-prelude.egg) | IMPLEMENTATION rules (sorts `Tr/CL`) | extracted from [`../zipper-impl.egg`](../zipper-impl.egg) |
| [`bridge-prelude.egg`](bridge-prelude.egg) | movement + impl + `Reflect : Tr → Z` | `scripts/make_bridge.py` |
| `<example>.egg` | movement coincidence per program | `morkl.ZipperEggTest` (Scala, this repo: `src/test/scala/ZipperEggTest.scala`) |
| `<example>-impl.egg`, `op-*-impl.egg` | implementation coincidence | same |
| `generated/rand-*.egg` | randomized ZIPPER + EAGER-TRIE differential (7,150 checks) | `scripts/gen_bridge_tests.py` |
| `generated/rand-setofpaths-*.egg` | randomized SET-OF-PATHS differential (the reference computes the same sets) | same script, same reference semantics |
| [`../proofs/`](../proofs/) | UNIVERSAL certification incl. the per-op THREE-WAY theorems (z3 + vampire) | `proofs/run.sh` |

The three-notion equivalence is established in **egg** (the randomized families above — all three
encodings of the same operators, grounded against one independent Python path-set reference), and
in **z3 + vampire** (`proofs/threeway_*.smt2`: per operator, the zipper observation, the
set-of-paths denotation, and the eager-trie recursion are proved equal ∀ operands ∀ paths — with
composition/restriction split into `_zip`/`_trie` legs and the tails-union zip leg in
`keyfolds.smt2`).

Regenerate everything: `scala-cli test scbuild --test-only morkl.ZipperEggTest` (writes the per-example
files), `python3 scripts/make_bridge.py && python3 scripts/gen_bridge_tests.py`, `proofs/run.sh`,
`sh scripts/check_locality.sh`. Run any file standalone: `cd zipper-egg-tests && egglog <name>.egg`
(exit 0 = all checks pass).

## The object

A zipper is **(context, focus)**. Sorts keep movement and space ops distinct:
- `Z` — spaces and operators, with space-level navigation `Sub k z` (`Unwrap` = `Sub`, a space op);
- `C` — cursors: `Root z`, movements `Descend k c` / `Ascend c`, with `Ascend (Descend k c) = c`
  (the zipper contract; `Ascend` at a `Root` is deliberately undefined) and
  `FocusOf (Descend k c) = Sub k (FocusOf c)` (movement agrees with navigation).

**Lock-step invariant**: a cursor over a virtual space is ONE focus into the composite; every `Sub`
rule pushes the *same* key into every operand (linted mechanically: `scripts/lint_zipper_egg.py`).
This is what makes `Ascend` commute with every operator.

## Ops × observations matrix

`✓` = a local rule; `s` = a documented bounded search; `n` = via the op's structural reduction
(the op rewrites to `Guard`/fold form first, then the observation applies); `u` = reduces to the
named uninterpreted symbol over an opaque source (`TermOf`/`EmptyOf`/`KeysOf` — never a silent
dead-end); `—` = a documented impossibility.

| op \ obs | `Term` | `Sub` | `Keys` | `IsEmpty` | `Ascend` |
|---|---|---|---|---|---|
| `Empty`, `Eps` | ✓ | ✓ | ✓ | ✓ | (C-sort: inverts `Descend` only) |
| `Src n` (opaque) | u | ✓ (`ChildOf`) | u | u | 〃 |
| `Wrap1` | ✓ | ✓ | ✓ (1 child `IsEmpty`) | ✓ | 〃 |
| `Union` | ✓ | ✓ | ✓ (`KMerge`) | ✓ | 〃 |
| `Intersection` | ✓ | ✓ | s (`KInter`+filter) | s | 〃 |
| `Subtraction` | ✓ | ✓ | s | s | 〃 |
| `Composition` | ✓ | ✓ | s | s | 〃 |
| `Restriction` | ✓ (total) | ✓ (total) | s | s | 〃 |
| `Raffination` | n (macro) | n | n | n | 〃 |
| `TailsUnion` / `TailsIntersection` | n (Keys fold) | n | n | n | 〃 |
| `Head` | ✓ + n | n | n | n | 〃 |
| `Unwrap` | n (= `Sub`) | n | n | n | 〃 |
| `Iter` (head-dependent, defunctionalized `Body`/`App`) | n (Keys fold) | n | n | n | 〃 |
| `Guard` | ✓ | ✓ | ✓ | ✓ | 〃 |

Notes on honesty:
- **`Keys` is EXACT, not an over-approximation.** In an e-graph every equated observation must be a
  *function of the denotation*: an approximate `Keys` computed differently on two nodes of one
  e-class (e.g. `{∅}` also contains `Wrap1 5 ∅`) equates the two approximations (`KNil = [5]`) and
  poisons the graph by congruence. This was hit in development; exactness is soundness here.
- **`IsEmpty` on ∩ \ · ⟨| is a search** (`¬Term ∧ Keys = []`, recursing by `KFilt`), cost
  O(reachable focus space) — the one non-local observation, used only where exactness is
  semantically required (tails∩ / `Head` / `Iter` key sets).
- **Cost contract** (checked by `scripts/check_locality.sh`, not asserted): one movement step
  rewrites only the top constructor — LHS patterns are ≤ 1 constructor deep (linted); a d-descent
  chain over an opaque source produces exactly `d` `ChildOf` lookups (`2d` through a 2-operand ∪),
  independent of any trie's size; state grows O(1) frames per move per `Composition`/`Restriction`
  node — local in the *op expression*, **not** constant-size.

## What is proved vs tested

- **Proved ∀ (proofs/, z3 + vampire cross-validated, 11/11):** every nontrivial `Term`/`Sub` rule
  against the denotational path-set semantics (incl. the total `Restriction` rules — the old
  `Term(Restriction)=F` was unsound at terminal prefixes and is gone); composition's split theorem
  and normalization (via two certified `append` lemmas); ∪/∩ commutativity+associativity (kept OUT
  of the rewrite system deliberately); the key-fold correctness given exact keys; and the
  implementation characterizations `mem(op(t₁,t₂),p) ⟺ mem(t₁,p) OP mem(t₂,p)` by explicit
  structural induction — which **is** the homomorphism theorem
  `materialize(OpZipper(z₁,z₂)) = Op(materialize z₁, materialize z₂)` in denotational form.
- **Tested on randomized instances (7,150 checks):** the spec-vs-impl commuting squares through
  `Reflect` (`RGet`/`RKeys` are *independent* lookups, so the squares are real checks, not
  definition unfoldings), each side also grounded against an independent Python path-set reference.
  The sorted-child-list representation is the list *refinement* of the proved coalgebra maps and is
  what these randomized differentials validate.
- **Ground regressions:** every previously-stuck probe (duplicate-head tails∩, 3-way tails∩,
  tails-over-`Src` reducing to the *named* `KeysOf` enumeration, composition/restriction movement
  over opaque sources, `Term(Restriction ε ε) = T`, `Mat` of an unwrap cursor) is a `(check …)` in
  `zipper.egg` / `zipper-impl.egg`.

## Workloads

`datalog-tc-virtual.egg` is the datalog workload through the **virtual** algebra: the semi-naive TC
fixpoint unrolled to its convergence depth as nested `Iter`/`JoinBody`/`\`/`∪` over the edge
literal — egg's movement rules walk it (`Keys` enumeration, per-head `App`, `Guard` pruning);
nothing is pre-evaluated. The `Lit`-cursor files (`datalog-tc`, `aunt-kg`, `puzzle-2x2`) remain as
executor-coincidence checks for control-flow programs (that is what `execZ` actually produces).

**Deferred, explicitly:** a virtual `puzzle-2x2` needs the program's own routines
(superpose/collapse `Call`s) defunctionalized as `Body` constructors — mechanical but large; and
**mutation** (insert/remove + zip-up) is out of scope until context frames *store siblings* (real
crumbs): with edits, `Ascend` is no longer the pure inverse `Ascend(Descend k c) = c`, so it is
sequenced after the read-only algebra (this file) is certified.

## Vocabulary mapping (one op, three names)

| MORKL `Space` | spec `Z` (movement) | impl `Tr` | Scala impl |
|---|---|---|---|
| `Union` | `Union` | `TrU`/`ClU` | `ITrie.union` |
| `Intersection` | `Intersection` | `TrI`/`ClI` | `ITrie.intersection` |
| `Subtraction` | `Subtraction` | `TrS`/`ClS` | `ITrie.subtraction` |
| `Composition` (a.k.a. old `Product`) | `Composition` | `TrC`/`ClMapC` | `ITrie.composition` |
| `Restriction` | `Restriction` (+`Restr` alias) | `TrR`/`ClR` | `ITrie.restriction` |
| `Raffination` | `Raffination` (macro) | `TrRaf` (macro) | `ITrie.raffination` |
| `Wrap` (1 item) | `Wrap1` | `TrW` | `ITrie.wrap` |
| `Unwrap` (1 item) | `Unwrap` = `Sub` | `TrUn` | `ITrie.unwrap` |
| `TailsUnion` / `TailsIntersection` | same | `TrTU`/`TrTI` | `ITrie.tailsUnion/…` |
| `Head` | `Head` | `TrH`/`HCl` | `ITrie.head` |
| `Iteration` | `Iter` + `Body`/`App` | (evaluator-level; not duplicated) | `evalI` Iteration |
| — (cursor) | `Root`/`Descend`/`Ascend`/`FocusOf` | `ZLit`/`Mat` | `SpaceZipper` |

Items are interned `i64` everywhere; the old String-item model is gone from the tree (`Interner`
in `MORKL.scala` is the one place items become `i64`).

## The automated equivalence pipeline (`pipeline/`, `../proofs/pipeline/`)

`morkl.EquivPipelineTest` runs, for each cornerstone program (aunt, semi-naive datalog, game of
life, 15-puzzle, temperature, n-queens) and each stage —

1. **Space/term vs its optimisation** (`SC.reduce`),
2. **zipper program** (Scala `transpileZ`) vs the Space/term program,
3. **trie/graph program** (`optimize(transpile(…))`) vs the Space/term program,

— two kinds of machine-checked certificates:

**Data-agnostic** (`<name>-<stage>-agnostic.{egg,smt2}`) — the primary: inputs stay free
(opaque sources in egg, uninterpreted predicates in SMT); iterations stay binders
(defunctionalised `BodyK` + per-program `App` rules); fixpoints/recursion are k-unrolled with a
shared residual input (k=2 egg, k=1 smt — the one-step rule certificate); ground subtrees
constant-fold via the executor (per-op semantics certified in `../proofs/threeway_*`); free
`Range` = a shared opaque input (the positional-op boundary). The egg leg is e-class equality
under the certified movement rules; the smt leg is a **structural-diff decomposition** (each
optimiser-rewritten subterm pair proved ∀ inputs ∀ paths with surrounding binders freed; the whole
program follows by congruence), discharged by z3/vampire.

**Instance** (`<name>-{space,zipper,graph}.{egg,smt2}`) — executor-grounded spot checks: control
flow expanded by exec's own evaluation rules (gated `eval(expanded) == eval(original)` in Scala);
stage 1 in the eager set-of-paths reference (`ElemP` membership observations, ACU-free schedule,
ascending rounds ladder) with documented tiered fallbacks into the eager-trie reference when the
eager closure exceeds budget; stages 2/3 observe the real zipper/DAG through `Reflect` against the
reference output in the bridge.

**Virtual programs** (`<name>-zipper-virtual.egg`) — stage 2's movement-calculus leg with the
REAL binder machinery: iterations render as defunctionalised `Iter`/`BodyK` with per-program
`App` rules and `JoinBody` where the body is a head-dependent join (the `App` rule's universal
soundness is `../proofs/join_spec.smt2`); emitted for all six cornerstones, gated by the Scala
executor. `datalog-sn` converges fully under the movement rules.

**Marker taxonomy** — every emitted file is exactly one of (counted per cornerstone, printed as
`[pipeline] <name> markers so far: …` for CI):
- **real** — carries checks/goals and was verified (egg exit 0; z3 `unsat` AND vampire refutation);
- **`TRIVIAL-NO-OBLIGATION`** — the two sides are syntactically identical after
  alpha-normalisation (or all diff pairs collapse reflexively once binders are freed): recorded,
  counted, no prover invoked, and NEVER a fake `(assert (not true))` check (a self-test asserts
  none is emitted);
- **`LAW-JUSTIFIED[-NO-RESIDUAL]`** — proof-carrying transformation: every differing pair is
  verified (by syntactic replay, `SmtDiff.justify`) to be an instance of the optimiser's
  ∀-certified law set, and cites its universal certificate (`SmtDiff.lawCertificates`, e.g.
  `iterate-literal-union → ../proofs/keyfold_iter.smt2`); residual (unjustified) pairs, if any,
  still go to both provers;
- **`IDENTICAL-LITERAL-NO-EQUIVALENCE-OBLIGATION`** — both sides materialised (in Scala, gated
  by the executor) to byte-equal constructor terms, so an egg "equivalence" would be true by
  hash-consing with ZERO rule applications and is not emitted; the actual equivalence certificate
  is the named twin (`-zipper-virtual.egg` for stage 2, the `-agnostic` legs for stage 1) and the
  file carries only single-side reference observations.  The audit flags any REAL egg file that
  binds byte-identical large terms under two let names, so this class cannot silently reappear;
- **`BUDGET-EXCEEDED`** — the egg observation run did not converge in the rounds ladder; recorded,
  with the equivalence carried by the named law-justification certificates, the smt twin, and the
  randomized Scala gate.

**The law registry** (`../proofs/laws/`) — every optimiser source law and every formal.egg
set-algebra rule has a PER-LAW ∀-certificate: 36 small denotational statements (sets as
`Path -> Bool` predicates over the quantified-append first-order prelude), each negated and
discharged by z3 and/or vampire; induction is never smuggled — the three lemmas that need it
(`law_append_assoc/inj`, `law_isprefix_append`) carry EXPLICIT structural-induction schema
instances.  `REGISTRY.tsv` maps law → kind (FILE / SCHEMATIC / GROUND / DEFINITIONAL) →
certificates; `scripts/check_laws.py` keeps it in sync with `SC.sourceLaws` and fails CI on a
law without a live (PROVED) certificate.  `../proofs/run.sh` writes machine-readable verdicts to
`../proofs/STATUS.tsv` (PROVED / OPEN-expected / OPEN-new / COUNTERMODEL — `sat` fails loudly),
`scripts/check_obligations.py` enforces total rule → obligation annotation coverage over
`zipper.egg`, `zipper-impl.egg` AND `formal.egg`, and rules citing an admitted-OPEN obligation
must acknowledge it inline (counted as open-acknowledged).  Rendered movement programs intern
large ground literals as shared `$glit` globals so BodyK App rules no longer inline the full
relation per occurrence.
