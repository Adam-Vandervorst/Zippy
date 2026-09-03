# Response to the acceptance review of `f6832fc`

This document is part of the delivered change, not a review input. It answers the review section by
section, and it uses three verdicts with fixed meanings:

| verdict | meaning |
|---|---|
| **RESOLVED** | every required change is made and *verified by running it* on this machine; the artifacts are regenerated |
| **PARTIAL** | some required changes are made and verified; the rest are named below, with what is missing |
| **OPEN** | not addressed |

Nothing here is marked RESOLVED on the strength of an argument alone. Where a verdict rests on a
prover or a test run, the command and the outcome are given.

**Toolchain used for every measurement below** — the versions the tree's own headers cite:

    JDK      openjdk 21.0.12
    sbt      2.0.8 (project/build.properties), Scala 3.8.1 (build.sbt)
    z3       5.1.0
    vampire  5.1.0 (commit 7b2f410)
    egglog   3.0.0 (built from source, commit e5dea2d5)
    machine  16-core x86_64, Linux 6.17, 247 GiB RAM

## Summary

| # | review item | verdict |
|---|---|---|
| 1 | fixpoint model denotes the executor; stop expanding control flow | **PARTIAL** |
| 2 | complete the recursive certificates | **PARTIAL** |
| 3 | real, discharged end-to-end cornerstone obligations | **PARTIAL** |
| 4 | every cost-model acceptance gate green | **PARTIAL** |
| 5 | remove hardcoded and dangling paths | **RESOLVED** |
| 6 | regenerate benchmark artifacts from an identifiable source state | **PARTIAL** |
| 7 | preserve disjointness across spills | **PARTIAL** |
| 8 | finish and connect the unbounded tier | **RESOLVED** |
| 9 | clean, internally consistent artifacts | **PARTIAL** |

`PLAN.md` is the companion to this document: what is left, in the order it should be done, with the
gate that decides each step. This one says what is done.

The review's verdict of **Reject** still stands: items 6 and 7 are untouched, item 3's obligations
are not discharged, and five of item 4's cost gates are still red. What follows says exactly which of its required changes are done.

---

## 1. Make the fixpoint model denote the executor — **PARTIAL**

### Done: one semantics, chosen and enforced

The review's first and preferred option is implemented: **every executor now iterates
`cur := cur ∪ F(cur)`** instead of iterating `F` and keeping a side accumulator. Five sites:

| site | function |
|---|---|
| `src/main/scala/MORKL.scala` | `eval` |
| `src/main/scala/MORKL.scala` | `exec` (op-graph, `SpaceValue`) |
| `src/main/scala/GraphExec.scala` | `execT` (op-graph, `ITrie`) |
| `src/main/scala/Trie.scala` | `evalT` |
| `src/main/scala/IntTrie.scala` | `evalI` |

The iterated operator is now inflationary **by construction**, so
`terminating/fixpoint_is_lfp.smt2`'s second premise (`init ⊆ F(init)`) holds without being checked,
monotonicity becomes the one remaining side condition, and it is the premise that buys *leastness* —
which is what `monotoneInMention` already decides. The prose that said monotonicity alone was
sufficient is corrected in all four places that carried it: `formal.egg`,
`zipper-egg-tests/prelude.egg`, `zipper-egg-tests/bridge-prelude.egg` and `EquivPipeline.scala`
(`renderZ`, `AgSmt.fixSym`), plus `Space.Fixpoint`'s own doc comment, which had stated the old
`init ∪ body[init] ∪ …` denotation.

Two consequences of the change, both wanted and both tested: the accumulator becomes redundant
(part (ii) of the certificate), and the loop **terminates** over a finite universe where iterating
`F` alone can cycle forever — a monotone body whose pure-`F` chain is a 2-cycle is now a test case.

It also changes the answer for **non-monotone** bodies, which is the point of choosing one
semantics. `SpatialSoundnessHunt`'s witnesses 1 and 1b are updated with the new ground truth and an
explanation: `Fixpoint(Literal({a·b}), k, TailsIntersection(k))` is `{a·b, b}` (the least
post-fixpoint above the seed, verified by hand in the file) where the old loop returned
`{a·b, b, ε}` — a post-fixpoint, but not the least one, and not what any emitted certificate states.
Witness 1b's probe moved from `{ε}` to `{b}` because the old probe now tests nothing.

### Done: the regression the review asked for

`src/test/scala/FixpointSemantics.scala`, 7 tests, all green. It uses the counterexample
`fixpoint_is_lfp.smt2:47-50` already documents, and it *distinguishes* the two readings rather than
restating one:

* the counterexample **passes every** monotonicity gate in the tree (`monotoneInMention`, and
  `asFixpointGeneral`'s `monoIn`) — so it really is a counterexample to "monotonicity is enough";
* the least post-fixpoint is computed **independently**, by brute force over the finite universe
  ("the least `Y ⊇ init` with `F(Y) ⊆ Y`"), with no iteration of any kind, and the file *checks*
  that it is below every post-fixpoint rather than assuming the smallest is least;
* the old loop shape is kept in the file and shown to return `{a,b}` where the specification says
  `{a,b,c}`;
* all five executors return the specification's value;
* **at the prover level**, and this is the part that makes it a differential:

| file | claim | z3 | vampire |
|---|---|---|---|
| `proofs/pipeline/fixpoint-gate/lfp_agrees.smt2` | the emitted `Fixpoint` model `= {a,b,c}` | `unsat` | Refutation found |
| `proofs/pipeline/fixpoint-gate/accumulator_refuted.smt2` | the same model `= {a,b}` | `timeout` | no refutation |
| `proofs/pipeline/fixpoint-gate/bv_lfp_pinned.smt2` | decidable: the axioms **force** `{a,b,c}` | `unsat` | — |
| `proofs/pipeline/fixpoint-gate/bv_accumulator_refuted.smt2` | decidable: `{a,b}` **contradicts** them | `unsat` | — |
| `proofs/pipeline/fixpoint-gate/bv_nonvacuity.smt2` | decidable: the axioms have a model | `sat`, `fx = #b111` | — |

The first two are emitted by the real `AgnosticPipeline.smtAgnostic`. The last three are a
hand-written decidable twin (a set over `{a,b,c}` as a `(_ BitVec 3)`), for two reasons: a bug in
the Space→SMT emitter cannot make both agree, and the ∀-path negative control comes back `timeout`
rather than `sat` — the absence of a proof, not a separation. The twin turns it into an actual
**refutation** of the pre-fix answer, with a non-vacuity witness beside it.
`proofs/pipeline/fixpoint-gate/README.md` and `STATUS.tsv` record all five.

    sbt 'testOnly morkl.FixpointSemantics'      # 7/7, ~2 min (the FOL leg runs four prover calls)

### Done: the binders now reach the instance renderers

The review's third bullet — carry `Iteration` and `Fixpoint` through the instance renderers, and stop
`expand` executing them into proof sides — is implemented.

**`EquivPipeline.expandKeepBinders`** binds this instance's inputs (a free `Mention` becomes its
`Literal`, a ground path a constant) and stops there, threading the bound names so a binder's own
variable is not looked up in an environment that does not contain it. `Iteration` and `Fixpoint`
survive; `Fold`/`Call`/`Range`/grounded are still executed exactly as `expand` does, and **only when
closed** — one that reads an enclosing binder throws with the node named, and the caller falls back
to the executed form and *prints which node forced it*.

**The renderers gained the arms.**

* `formal.egg` grew a HEAD-DEPENDENT `Iter`, which it did not have — only the loop-*invariant*
  `IterC`. Four rules, certified by a new `proofs/laws/law_iter_set.smt2` (z3 `unsat`, vampire
  Refutation found):

      L1  (Iter src b)                       = (IterH (Head src) src b)
      L2  (IterH (Union a c) src b)          = (Union (IterH a src b) (IterH c src b))
      L3  (IterH (Singleton (Item h)) src b) = (App b h (Unwrap src (Item h)))
      L4  (IterH (Empty) src b)              = (Empty)

  L2 is the load-bearing one and the distinction it rests on is worth stating: an `Iteration` does
  **not** distribute over a union of its SOURCE — a shared head merges the groups and a
  head-dependent body observes the merge, which is machine-refuted as N05 with an executed
  countermodel. What distributes is the HEAD-SET argument, with `src` held fixed. L1 is where the
  headedness guard lives, so nothing but L1 may introduce an `IterH`.

  Writing the law found a **variable-capture bug in the law generator**: `mem_head` and `mem_iterh`
  both bound `hh`, so the generated L1 contained `(= (cons hh nil) (cons hh nil))` and stated
  something false. z3 answering `sat` is what said so.

* `EquivPipeline.formalOf` gained a binder-capable overload emitting `(Iter src (BodyK i))` /
  `(Fix init (FBodyK i))` with one program-supplied `App`/`FApp` rule per distinct body, plus general
  path rendering — a path may now mix constants and bound heads (`aunt`'s `child·$person` is exactly
  that, and it caught the first draft's Deref-only special cases).
* The instance SMT leg no longer has its own compiler. `EquivPipeline.Smt` — a second,
  local-algebra-only membership compiler that **threw on both binders**, which is *why* `expand` had
  to execute them — is deleted, and `smtEquivalence` compiles with `AgnosticPipeline.AgSmt`, which
  already models `Iteration` (group predicate inlined), `Fixpoint` (post-fixpoint axioms + Park) and
  `Range`. Identity is decided in Scala with `SmtDiff.alphaNorm`, i.e. **modulo binder names** —
  strictly stronger than the deleted macro-name test, which could not see binders at all.

**Measured, per stone** (the suite prints a census, so this is not a property of the code path):

| stone | control flow | stage-1 sides |
|---|---|---|
| `aunt` | BINDERS KEPT | **DIFFER — a real obligation** |
| `datalog-sn` | BINDERS KEPT | identical after alpha-normalisation |
| `gol` | BINDERS KEPT | identical after alpha-normalisation |
| `temperature` | BINDERS KEPT | identical after alpha-normalisation |
| `puzzle3-full` | BINDERS KEPT | **DIFFER — a real obligation** |
| `puzzle15` | executed (fell back) | identical |
| `nqueens` | executed (fell back) | identical |

Five of seven keep their control flow, and the two that now carry real stage-1 obligations include
`puzzle3-full` — the unbounded-`Space.Fixpoint` cornerstone, whose `-space` cell was
`IDENTICAL-STRUCTURE`. On the three stones that still report identical sides the optimiser genuinely
does nothing to the program (their `-space-agnostic` twins are `TRIVIAL` for the same reason), so the
marker is now a fact about `SC.reduce` rather than an artefact of the executor.

**What the fallback costs, precisely.** `puzzle15` and `nqueens` still go through `expand`, because a
`Fold`/`Range`/grounded node in them reads a variable bound by an enclosing binder and no renderer
models that. The run log names the node.

    sbt 'testOnly morkl.EquivPipelineTest'      # 7/7

## 2. Complete the recursive certificates — **PARTIAL**

### Done: the residual cut is parameterized by its arguments

`AgnosticPipeline.ResidualCut` replaces the bare name. A cut is now

    residual_<routine>_<depth>_<sha256(alpha-normalised refs; mentions)>

so two cuts share a symbol **iff** they cut the same routine at the same depth with alpha-equal
arguments — the registry's stated condition, decided instead of assumed. `residualCuts` keeps the
full descriptor for every symbol, `residualsOf` recovers them from a term, and `alignCuts` returns a
`CutAlignment` that reports both sides' descriptors on a mismatch.

`EquivPipelineTest` no longer compares name sets. It calls `alignCuts`, and where routine and depth
agree but the arguments do not, it emits the **argument equivalence as its own prover obligation**
(`<name>-residual-args-k<k>-<i>.smt2`) and fails the cell unless that obligation is discharged. An
undischarged one leaves the two cuts as distinct free inputs, which is the conservative direction.
`terminating/REGISTRY.tsv` row O10c is rewritten from `OPEN` to `CONSTRUCTION+GATE` with that
description.

**The cornerstones do not exercise this, and that is recorded rather than glossed.**
`datalog-sn`'s `sn_tc` is the one self-recursive routine no `asFixpoint` lowering recognises (it
changes two mentions at once, and `asFixpointGeneral` requires exactly one), and its two agnostic
sides come out syntactically identical after alpha-normalisation — so `SmtDiff` emits no obligation
and **no residual symbol reaches any emitted file**. The cut aligns for a reason that has nothing to
do with the argument keying. `src/test/scala/ResidualCutCheck.scala` therefore tests the mechanism
directly, on cuts built by real unrollings of a deliberately non-lowerable routine, and its first
test asserts that the probe routine really is non-lowerable — because the first draft used a
single-changing-mention routine, which `asFixpointGeneral` lowered to a `Fixpoint`, so no cut was
made and every other assertion was vacuous. What it checks:

* equal routine, depth and arguments → one symbol; **alpha-equal** arguments → one symbol, so the
  keying is semantic and not syntactic;
* **different** arguments → different symbols (space arguments *and* path arguments), and different
  routine or depth likewise;
* `alignCuts` reports `aligned` for a term against itself and `MISALIGNED` with both descriptors
  against a differently-argued cut;
* the k=1 and k=2 unrollings of the same call share **no** residual symbol — the two certificates
  really are about different free inputs.

    sbt 'testOnly morkl.ResidualCutCheck'      # 6/6

### Done: O6a connected to the implementation — and it found three real bugs

O6a (beta-soundness of capture-avoiding inlining) is still **not a theorem**, and the registry still
says why. What is new is the other half the review asked for ("connect the resulting theorem to the
actual substitution and fold implementation"):

* the **semantic** half is now proved at tier 3: `proofs/unbounded/call_unfold.p` (U63) — a call is
  its body applied to the argument. Its header says explicitly that it is *not* the substitution
  theorem, so it cannot be mistaken for one.
* the **syntactic** half is `src/test/scala/SubstConformance.scala`: subst-then-eval versus
  eval-with-the-name-bound over 300 generated programs, **145 of which shadow the substituted name**
  under an `Iteration`/`Fold`/`Fixpoint` binder, plus 8 explicit hand-written shadowing programs for
  the two recursive binders, plus call-vs-inline through all three executors — with a deliberately
  capture-unsafe substitution as the negative control, which the suite requires to be caught.

It found three defects, all now fixed:

1. `AgnosticPipeline.substMention` had **no `Fold` and no `GroundedSS` arm**. Both fell through
   `case other => other`, so substitution silently did nothing under them — including in `Fold`'s
   *source*, which is not a binder position at all. A `Fold` whose source mentioned the substituted
   name kept an unbound mention and `eval` then failed to resolve it.
2. `AgnosticPipeline.substPathRef` had **no `Fold`, `Fixpoint`, `GroundedPS` or `GroundedSS` arm** —
   a path ref inside a `Fixpoint` was never substituted.
3. `Lower.inline` **captured**. It substituted with `subs`, a blind congruence that rewrites every
   occurrence including ones an inner binder has re-bound, so a routine whose parameter shared a
   name with one of its own binders had its shadowed occurrences replaced by the argument. This is
   precisely the bug O6a is about. It now delegates to the two functions above, which are the single
   implementation of the binder rules; both matches are total, arm per constructor, so a new `Space`
   case cannot repeat the omission.

Row O6a is rewritten to `OPEN+DIFFERENTIAL` and names all three.

    sbt 'testOnly morkl.SubstConformance'       # 4/4

### Done: registry rows that described stale evidence

* **O3d-X1 / O3d-X2** said the refuted arms "must be tightened". They already were: `mono` and
  `monoIn` now forbid the recursive occurrence under `TailsIntersection` and in an `Iteration`'s
  source rather than assuming monotonicity there. Both rows are now `REFUTED-CLOSED` and quote the
  current code, and each cites its **executed** countermodel in
  `proofs/unbounded/COUNTERMODELS.tsv`.
* **O10c** and **O6a** as above.

### Not done

* **O12b** (the supercompiler fold) is untouched and still OPEN. It depends on the substitution
  model O6a lacks, and the differential above does not cover the fold step.
* **O10b** (all-*k* unrolling) is untouched. The review's alternative — narrow every claim to bounded
  unrolling and keep it out of end-to-end verdicts — is not implemented either; a cell whose sides
  contain a residual cut is still not labelled as bounded-unrolling.
**O12d** (whistle termination, Kruskal's tree theorem) is resolved by the review's second option:
it is now an **explicit trusted assumption in the acceptance contract**. `docs/TRUSTED.md` is that
contract — the complete list of what a `PROVED` verdict rests on — and row **T3** states O12d, says
why it is not derivable here, what stands in for a proof (the explicit `Deadline`, so a
non-terminating drive is a timeout rather than a hang, plus `SCHardening`/`SCDriver` on the corpus),
and what would break if it were false: **liveness only**, since per-rewrite soundness is O12a and
the certified law set and does not depend on driving stopping. The registry row is now `ADMITTED`
with `docs/TRUSTED.md T3` in its file column instead of `(none)`.

`docs/TRUSTED.md` also gives the same treatment to the other five assumptions in the tree — the
induction schema of item 8, the four bridging inductions of `fixpoint_is_lfp.smt2`,
`EquivPipeline.expand`, `Range`'s position outside the pointwise algebra, and the grounded-function
determinism contract — and lists O6a, O10b and O12b separately as **gaps, not assumptions**. It is
linked from `README.md` and `docs/atlas.md`.

## 3. Real, discharged end-to-end cornerstone obligations — **PARTIAL**

### Done: the instance sides are independently rendered PROGRAMS

The review's second and third bullets. See item 1 for the mechanism —
`expandKeepBinders`, the four certified head-dependent `Iter` rules in `formal.egg`, the
binder-capable `formalOf`, and the deletion of the local-algebra-only `Smt` in favour of `AgSmt`.
Five of seven stones now reach the renderers with their control flow intact, and two of those
(`aunt` and `puzzle3-full`) carry stage-1 obligations whose two sides genuinely differ.

### AND IT COST TWO DISCHARGED CELLS, WHICH IS THE HONEST HEADLINE

Making a claim stronger can put it out of prover reach, and it did:

| | before | after |
|---|---|---|
| `PROVED` | 8 | **7** |
| `OPEN (prover budget exceeded)` | 4 | **5** |
| `TRIVIAL` / `IDENTICAL-STRUCTURE` / `LAW-JUSTIFIED` | 15 / 11 / 4 | 15 / 11 / 4 |

* `puzzle3-full-space.smt2` was `unsat`/`PROVED` over the executed sides and is now **OPEN**. Its
  file went from a local-algebra comparison to an 847 KB obligation carrying the `Fix` post-fixpoint
  axioms, the Park instances and the binder-preserving program on both sides. The claim is now the
  one the review asks for and it is not discharged. Checked at a 300 s budget, not just at the
  suite's 60 s.
* `nqueens-zipper.smt2` regressed for a different and less satisfying reason: that stone falls back
  to the executed form, so its *content* is unchanged — what changed is the compiler. `AgSmt`'s
  encoding is simply harder for z3 here (still timeout at 300 s). One cell (`aunt-zipper`) was
  recovered by fixing `AgSmt`'s subterm sharing to be **structural** rather than by
  `System.identityHashCode` — the deleted `Smt` shared structurally, and losing that inflated every
  formula; `gol-zipper` also lost its vampire verdict and has not come back.

So the count is worse and the claims are better. Both facts belong in the same sentence.

### Done: the matrix is a checked claim, and the headline claim is corrected

`proofs/pipeline/DECLARED.tsv` declares what every artifact IS, and
`scripts/audit_pipeline_markers.py` fails on drift in either direction — a cell that stops carrying
an obligation, an artifact with no declaration, or a declaration with no artifact. Both directions
are negative-tested. `--run` executes every non-marker artifact and passes, which it could not
before (see the `bridge-prelude.egg` finding below). `README.md`'s verification paragraph no longer
says the pipeline "proves ... on seven cornerstone programs"; it says what is emitted, defines each
marker kind and what it is worth, and points at `STATUS.tsv`.

### Not done

* **No opaque symbolic source in `SpaceZipper`**, so the stage-2 agnostic leg still compares `uO`
  with `zipCollapse(uO)` and is still weak. Untouched.
* **`puzzle15` and `nqueens` still fall back to the executed form**, because a `Fold`/`Range`/
  grounded node in them reads a variable bound by an enclosing binder and no renderer models that.
  The run log names the node.
* **The 26 `TRIVIAL`/`IDENTICAL-STRUCTURE`/`LAW-JUSTIFIED` cells are unchanged in number.** On the
  three stones where stage 1 still reports identical sides the optimiser genuinely does nothing to
  the program, so the marker now means something — but that is a smaller claim than "replace every
  such cell with a two-sided obligation".
* **Five cells are open**, one more than before.

### Found and fixed: `bridge-prelude.egg` did not load

Its park block was ported from `prelude.egg` and uses `(SelfBody)`, `Fix` and `FApp`, but none of the
three was declared in this file's own `datatype*` block. egglog rejects the file outright with
`Unbound function SelfBody`, so **every** artifact that includes it failed at every rounds budget —
the seven `-lit`/`-impl` fallbacks in `zipper-egg-tests/pipeline/`. Four of them (`aunt-space-lit.egg`
and friends) were nevertheless committed *without* a `BUDGET-EXCEEDED` marker, i.e. indistinguishable
on disk from files that had been verified. The three declarations are added, and every `.egg` file in
the tree now loads:

    for f in formal.egg zipper.egg zipper-spec.egg zipper-impl.egg zipper-egg-tests/*.egg; do
      egglog "$f" >/dev/null || echo "REJECTED: $f"; done      # silent

`aunt-space-lit.egg` and `nqueens-space-lit.egg` were `BUDGET-EXCEEDED` markers that existed only
because the `-impl` fallback could not load; with the prelude fixed the fallback works and the `-lit`
degradation is never reached, so both are deleted rather than left claiming a budget was exceeded for
a reason that no longer exists.

## 4. Every cost-model acceptance gate green — **PARTIAL**

Measured on this machine, with all three tools present:

| run | result |
|---|---|
| baseline at `f6832fc` (`sbt test`) | **574 tests, 8 failures** |
| after round 1 (`sbt test`) | **573 tests, 5 failures** |
| after round 2, everything, unconditionally (`sbt 'testOnly morkl.*'`) | **606 tests, 5 failures** |

The same five cost-model gates in both later runs, listed below. The last row is the authoritative
one: `testOnly morkl.*` runs every suite rather than skipping the ones `sbt test` considers current,
which is why its total is higher.

**Four of the baseline's eight are gone.** `EquivPipelineTest` is green (it was an initialisation
error with no prover installed; once it ran, seven of its cells failed for the `bridge-prelude.egg`
reason in item 3). `SpatialAcceptance.5c`, `SpatialPipelineCheck.COST` and
`SpatialEventsCheck.BENCHMARK` were the three contention-sensitive wall-clock failures.

### Done: the wall-clock gates — all THREE of them

`SpatialAcceptance.5c` is now **deterministic**. The review's diagnosis is confirmed by measurement:
the same tree and the same machine put `puzzle15` inside the 4000 ms ceiling when the suite runs
alone and past it when `EquivPipelineTest` is running z3 and vampire on 16 cores beside it. So:

* the two absolute millisecond assertions are **gone**. They are replaced by two gates that do not
  depend on load — the structural **ratio** (decorated vs plain, measured adjacently in the same JVM
  so contention scales both), which was always the real invariant, and **counted work**: the
  decorated node count and observation count against explicit caps (`600` nodes, `30000`
  observations), which are deterministic functions of the term;
* timings are still measured, as **min of 5 samples** — contention can only inflate an elapsed time,
  so the minimum is the least-contended estimate and the right statistic for a latency figure — and
  printed on every run beside the counted figures, with the old ceilings kept as *informational*.
  A sample past one is a loud note, never a failure.

    sbt 'testOnly morkl.SpatialAcceptance'      # green, and green under load

A **third** contention-sensitive gate turned up once the rest of the suite was running beside it:
`SpatialEventsCheck`'s "BENCHMARK: the disarmed sink's cost is measured, not asserted" asserts a
NANOSECOND-scale difference between two 100-million-iteration loops — its own comment already noted
that the sign flips between runs because it sits at the measurement floor. It passes alone and fails
under load. Same treatment: the nanosecond figure is reported with a loud note past the old 1 ns
ceiling, and the gate is now the **counted** invariant that is what "disarmed" actually means — a
disarmed sink records nothing, checked with a fresh `EffortSink.Counter`, identical on every machine.

`SpatialPipelineCheck.COST` failed in the baseline and passed in every later run — the same
sensitivity — and has **not** been given the treatment, because it has not been observed to fail
since. That is a weaker position than the other three and is stated as such.

### Done: the `naryProbes` upper bound, derived and validated

The review's fourth residue cluster. `naryProbes`'s second factor is `Σ_calls |live|`, and it was
`tighter(k·(2·nodes+1), 2·nodes + 32k)` — where `perProbe`'s own comment already said the remaining
slack was there. It is now derived from the descent:

> `IntTrieOps.joinAllTries` / `meetAllTries` partition the live operands on a branching bit, and an
> operand that is a `Bin` at that bit contributes its **two children**, one to each side. So every
> live entry in the whole descent is a distinct Patricia node of some operand's child map, and each
> appears in exactly one call's `live` array. An `IntMap` with `m` entries has at most `2m − 1`
> nodes, hence `Σ_calls |live| ≤ 2·nodes`, plus `k` for the opening `collectLive` pass.

So `2·nodes + 32k` becomes `2·nodes + k`. At the operator table's arity `32k` is 2048 where the
derived bound is a few hundred, which is why it dominated.

**Validated against the counted oracle, because a tighter interval that stops CONTAINING the counted
value is worse than a wide one.** Containment stayed at **100.0% on every gated channel** (graph,
reference, trie and zipper `Work`/`Alloc`/`Rounds`/`Touch`), so the bound is sound. Measured effect
on the widths the review names:

| row | before | after |
|---|---|---|
| `operator iteration trie Work width` | 86.95 | **46.58** |
| `operator tails-inter trie Work width` | 30.71 | **11.84** |
| `operator tails-inter graph Work width` | 30.71 | **11.84** |
| `operator tails-union trie/graph Work width` | 19.16 | **passes** |
| `operator iteration zipper Work width` | 85.00 | **passes** |

and the cornerstone events gate went from 36 to 33 failing checks.

### Not done: the other three residue clusters, and the gates are still red

### Not done: the four residue clusters and the counted-oracle containment failures

Five red gates remain, unchanged from the baseline:

    SpatialScaleCheck    SCALE LADDERS: predicted vs measured SLOPE
    SpatialCostCheck     PRODUCT REQUIREMENT: interval WIDTH (8 failures: OP-2, OP-2z, OP-6, OP-6g, OP-6z)
    SpatialEventsCheck   CALIBRATION: predicted intervals vs counted events
    SpatialPipelineCheck ITEM 5 INVARIANT: no infinite OR ASTRONOMICAL estimate
    SpatialPipelineCheck ITEM 8: cost consumes the DECORATED result

One piece of analysis, in case it is useful to whoever finishes this. Five of the eight width
failures are `OP-6`/`OP-6g`/`OP-6z`, all attributed to `CostModel.naryProbes`, whose upper bound is
`perProbe(k) · tighter(k·(2·nodes+1), 2·nodes + 32k)`. Reading `IntTrieOps.joinAllTries` /
`meetAllTries`: at each call the live operands are partitioned by the branching bit, and an operand
that is a `Bin` at that bit contributes **its two children** — so every live entry in the whole
descent is a *distinct node of some operand*, and each such node appears in exactly one call's
`live` array. That gives

    Σ_calls |live|  ≤  Σ_i nodes_i

which is tighter than either arm of the current `tighter(…)`, and the per-call probe count is at
most three passes over `live` (branching scan, split-or-Tip, identity search) plus `collectLive`'s
dedup, which `perProbe` already models. **This is not implemented**, deliberately: the interval must
still *contain* the counted value, and turning a wide-but-sound bound into an unsound one is worse
than leaving it wide — the review says so directly. Tightening it needs the calibration loop
re-run against the counted oracle, which is the work item, not the formula.

One cost-model change *was* required by item 1 and is made: the fixpoint loop now performs its
accumulating union **unconditionally**, in every round including the convergence-detecting one, so
`CostModel.fixStep` is charged `R` times rather than `R − 1`. Charging `R − 1` would under-price
every fixpoint by one whole merge. `SpatialCost.scala`'s three descriptions of the loop shape are
updated to quote the current code.

## 5. Actually remove hardcoded and dangling paths — **RESOLVED**

### One policy, three thin adapters, no absolute path in the tree

`toolchain.conf` at the repo root **is** the policy: one section per tool with its binary name,
environment override and version flag, plus the search order. All three adapters —
`src/main/scala/Tools.scala`, `scripts/toolpath.sh`, `scripts/toolpath.py` — now *read* it. None
of them contains a tool name, an environment variable name, or an install location of its own, so
there is nothing to keep in sync and no generated file to go stale.

The search order is `env → zippy-tools → path`. The four hardcoded lists (`/usr/local/bin`,
`/opt/homebrew/bin`, `$HOME/.local/bin`, `$HOME/.cargo/bin`) are **gone**, replaced by a single
`$ZIPPY_TOOLS` directory a machine may declare. With the policy file absent the adapters degrade to
`env, path` — the two location-free steps, never to a compiled-in path. Verified that all three
adapters agree, from the repo root and from a subdirectory, on `$Z3`/`$VAMPIRE`/`$EGGLOG`, on
`$ZIPPY_TOOLS`, and on `PATH`.

### The reference checker now supports its claim

`scripts/check_references.py` used to select eight extensions and skip `build.log`, `laws.diff`, the
generated CSV/TSV results and `MINED.tsv` **wholesale**. It now:

* takes its candidate set from **`git ls-files`** — every tracked file, so a new extension is covered
  the day it is added;
* skips binaries **by content** (a NUL byte in the first 8 KiB), never by name;
* has **no whole-file exception**. A file that legitimately contains an unresolvable token declares
  *that token* in `TOKEN_EXCEPTIONS`, one entry each, with the file it applies to and a reason from
  four documented categories. `--strict` **fails on an unused exception**, so a stale one is a
  failure rather than a silent widening;
* treats an **absolute path as a hard failure everywhere**, data files and `build.log` included —
  the check that `laws.diff` used to evade;
* has a **`--fresh` mode** that copies the tracked files into a temporary directory and scans that,
  so an ignored local file cannot make a reference look valid.

Turning it on found **26 dangling references the skip-list had hidden**. All are fixed or declared:

* `laws.diff` — an obsolete committed diff of already-applied changes, referenced by nothing but the
  skip-list itself, and the file the review names as still containing an absolute macOS prover path.
  **Removed.**
* `terminating/datalog_a.txt` — six `/Users/<name>/carac/...` citations rewritten to
  `carac:<repo-relative path>`, with a header saying carac is an external project that is not
  vendored. Three per-token exceptions cover them.
* `build.log` — six personal absolute paths rewritten (`$ZIPPY_DATA/...`, "an absolute macOS prover
  path"), and its citations of removed documents declared as historical, one token at a time, since
  the narrative is the artifact and rewriting it would falsify the log.
* `README.md` — the ignored-local-tool-directory recipe is replaced by a real toolchain table and ordinary
  installation instructions (item 6's third bullet, done here because that is where it lives).
* Four false positives in the checker's own regexes and search roots.

Current state:

    python3 scripts/check_references.py --strict           # dangling references: 0
    python3 scripts/check_references.py --fresh --strict    # dangling references: 0

## 6. Regenerate benchmark artifacts from an identifiable source state — **PARTIAL**

### Done: the metadata the review asks for, and a gate that refuses a dirty stamp

`RunEnvironment`'s block said which JVM ran and which Scala library was on the classpath. Neither
says which BUILD produced the classes, and a table cannot be reproduced from a JVM version. Added,
each read from the file that IS the source of truth so it cannot drift from what a rebuild would use:

* **`sbt`** — from `project/build.properties`, the file that pins it;
* **the compiler version AND ITS FLAGS** — from `build.sbt`. The flags matter: `-source:3.3` changes
  what the compiler accepts and therefore what was compiled;
* **the external tools, version-probed** — z3, vampire and egglog, resolved and asked for their
  versions. Relevant to every table whose numbers came from a prover, and unrecoverable afterwards;
* **`source tree`** — CLEAN, or DIRTY with the modified-path count, as its own row. `<sha>-dirty` as
  a suffix understates the problem: such a tree never existed as a commit, so the numbers cannot be
  reproduced from anything.

And `BenchmarkReport.write` now calls `RunEnvironment.requireCleanIfAsked`: with
`$ZIPPY_REQUIRE_CLEAN` set it **refuses to write a generated section from a dirty tree**. Unset (the
default) a local experiment still works and its header says `DIRTY` with the count, so the weaker
attribution is stated rather than implied.

### Done: the bootstrap recipe (this item's third bullet)

`README.md` no longer makes an ignored, untracked local tool directory the sole reproduction recipe.
It has a toolchain table with the versions this tree is verified against, real installation commands
for all three external tools, and points at `toolchain.conf` as the one resolution policy.

### The regeneration sequence, and what is left

Committing is what this item requires — "a clean code commit followed by an artifact-only commit" —
so it is done rather than described:

    git add -A && git commit                      # the CODE commit; the tree is now clean
    ZIPPY_REQUIRE_CLEAN=1 sbt 'testOnly morkl.GraphBench morkl.TrieBench morkl.CorpusRuntimes morkl.ProgramStats morkl.ProgramExpressivity'
    git add -A && git commit                      # the ARTIFACT-ONLY commit

with the code commit's sha recorded in the artifact commit's message and stamped into every
regenerated table by `RunEnvironment`. Nothing is pushed.

**What is NOT resolved**: the numbers themselves are regenerated from a clean, identifiable commit,
but they are regenerated from a tree in which **five cost-model gates are still red** (item 4). A
benchmark table produced from a tree that fails its own cost gates identifies its source correctly
and still does not establish that the tree is in an acceptable state. That is why this item is
PARTIAL and not RESOLVED, and it cannot become RESOLVED before item 4 does.

## 7. Preserve disjointness across spills — **PARTIAL**

### Done: the WIDTH spill carries a size-independent summary

`HeadAtoms` interns a head-set of any size to one `Int`; `Shape` gained channel **(f)**
`headAtoms: Set[Int]`, and the certificate is now `otherKeys ∪ ⋃ headAtoms`. Over `MaxSpillKeys` the
overflow is **interned instead of dropped**, so what the cap bounds is how many names are carried
*enumerated* — a representation choice — not what can be proved. Every lattice step manipulates ids
only (`possibleHeadsCert` never enumerates an atom); the one size-dependent question, whether two
atoms are disjoint, is decided once per pair and memoised. The carrier stays finite — the atom table
is append-only and `headAtoms` is a subset of it under `⊆` — so the widening still terminates, with
height now the number of distinct head-set ORIGINS rather than `MaxSpillKeys`.

The channel joins **every** channel test, because `Shape.isTop`'s own comment says what happens
otherwise: `isTop`, `mayHaveHead`, `contains` (γ), `leq`/`keysExceed`, `weaken`, `openCounts`,
`widen`, `capDepth`, `mk`, `capOthersCert`, `show`, plus `SpatialCheck`'s γ and order and
`SpatialAnalysis.capWidth`.

**Measured**: the width ladder now runs to `3 × MaxSpillKeys = 12288` keys per side (24576 in the
union, six times the cap) and the prediction is **flat** — `rebuilt = [2,2]`, `|Q| = [2,2]` — where
before the certificate became ⊤ over the cap and the growth class changed. The old test stopped at
exactly 4096, so it never crossed.

**Two bugs on the way, both caught by the existing gates and worth recording**:

* the first draft's `headsAtDepth` folded an *unknown* level in as the empty set — a false
  must-absence claim. `SpatialSoundnessHunt` produced the witness on the first run: `{c.b.b.b.a}`
  against a shape that must admit it.
* the overflow first set `otherKeys = Some(∅)`, which for a consumer reading channel (e) alone means
  "no untracked head may exist" — the opposite of ⊤. `Shape.contains` was such a consumer and γ
  rejected everything. The overflow now leaves (e) at `None`, so **any consumer not yet reading (f)
  sees exactly the old behaviour** and adding the channel cannot make anything less sound.

### Not done: the DEPTH spill, and the rows past `MaxDepth + 1`

Built, measured, and reverted rather than half-shipped. A per-level interned certificate on a
`MaxDepth`-deep may-only tail below the collapse **does not deliver the goal**:
`SpatialFrontier`'s disjointness query reads `possibleHeads` AT A LEVEL and never descends into an
`otherTail`'s certificate, so the depth-6 key-disjoint family still predicted `rebuilt = [5,10]`
against a truth of 6. And carrying certificates on both tails made `leq` compare them, which turned
six corpus shapes red in `SpatialAnalysisCheck`'s decorated-soundness gate — sound, but no longer
provable, i.e. a live regression. Getting those rows exact needs the frontier's relational walk to
consult tail certificates; that is a change to `SpatialFrontier`, not to this carrier, and it is not
made. `Shape.capDepth` carries the reason in place.

**The depth ladder is now measured much further out, and that corrected a claim in the test itself.**
It stopped at `MaxDepth + 3` and asserted `≤ 3d`; extended to d = 16 the numbers are

    d      1  2  3  4  5   6   7   8  …  15  16
    hi     1  2  3  4  5  10  14  18  …  46  50     exact to d = 5, then hi = 4d − 14

so the growth past the cap **is** linear, with slope 4 — the old `3d` envelope was simply too tight
for large d, not evidence of super-linear growth, and at d = 15 it wants 45 where the model gives 46.
The gate is now `4·d` (a recorded measurement, named as such, that fails if the over-prediction
GROWS) plus an unconditional soundness assertion at every depth, and the whole ladder is printed
before any assertion so a break shows the line rather than only its envelope.

### Done: the stale channel-count comments

Every "four-channel `Shape`" description is corrected — it was four, then five with the name
certificate, and is now six. `SpatialShape.scala` (five places), `SpatialPipeline.scala` and
`SpatialGamma.scala`.

    sbt 'testOnly morkl.SpatialFrontierCheck morkl.SpatialSoundnessHunt morkl.SpatialShapeCheck morkl.SpatialAnalysisCheck morkl.SpatialLawCheck morkl.SpatialCheckCheck morkl.SpillSoundness'
    # 127 tests, 0 failures

## 8. Finish and connect the unbounded tier — **RESOLVED**

Tier 3 result, from `sh proofs/unbounded/run.sh`:

    before:  certified: 55   expected-open: 1 (mon_cancel)   negative controls held: 8
    after:   certified: 67   expected-open: 0                negative controls held: 11
             unexpected-open: 0   countermodels/contradictions: 0   vacuous axiom sets: 0

### `mon_cancel` is discharged, and the trusted base is one reviewed principle

The direct attempt stays OPEN under every automatic route, and the attempt log in `mon_cancel.p`
now records the ones tried here as well as before: `--mode casc` at 180 s, `--induction struct`,
`--induction int`, and — new — an SMT-LIB2 rendering with `declare-datatypes` for `Path`, with and
without `define-fun-rec`, under `--induction struct` (vampire: timeout at 100 s; z3: timeout at
50 s). No countermodel from any of them, as expected.

`proofs/unbounded/_path_induction.p` is the resolution: the **structural induction schema for the
free term algebra `path`, instantiated at this one predicate**. A schema quantifies over formulas,
so first-order logic cannot state it and a saturation prover has no rule for it — but what is
trusted now mentions `app` only inside the schema's two premises and says nothing about what `app`
computes; instantiate it at any other property of paths and it is just as true. Both premises remain
obligations, and both are separately PROVED in the corpus (`mon_cancel_base`, `mon_cancel_step`).
`mon_cancel.p` closes in **0.02 s** in default mode.

`_cancel.p` is no longer an admission: it is a **proved lemma**, re-asserted for search economy in
the two theorems that consume it, with the measurement for why in its header — `wrap_roundtrip` and
`card_wrap` close in 0.08 s / 12.2 s with the lemma and **time out at a 180 s portfolio budget** with
`_path_induction.p` in its place. That is the same discipline `fixpoint_is_lfp.smt2` applies to its
four set-algebra stepping stones: prove it, then assert it, and say where the proof is.
`run.sh`'s `EXPECTED_OPEN` is now **empty**, and `REGISTRY.tsv`'s header names the schema instance as
the tier's one trusted item.

### Real obligations for Range, Fold, Call and Grounded

Four new operator modules and eleven new theorems, **all PROVED**:

| module | theorems |
|---|---|
| `_fold_ops.p` | `fold_empty` (U57), `fold_support` (U58), `fold_iter_const` (U59), `mono_fold` (U60) |
| `_range_ops.p` | `range_window` (U61), `range_interval` (U62) |
| `_call_ops.p` | `call_unfold` (U63), `call_fix_least` (U64), `call_fix_solves_sup` (U65), `call_fix_solves_sub` (U66) |
| `_grounded_ops.p` | `grounded_functional` (U67) |

Two are worth naming. `range_interval` is the load-bearing one: `Range` is the only operator in the
algebra that is **not pointwise** — survival depends on rank, not membership — and what makes the
four backends agree on it anyway is that a window is an *interval* of the canonical order, proved
here for an arbitrary strict total order so the theorem does not depend on which order was picked.
`call_fix_least` / `call_fix_solves_*` are the theorem `asFixpoint` and `asFixpointGeneral` need:
the `Fix` node they produce **is** the least solution of the recursion it replaced, with
monotonicity used in exactly one place — leastness, as in `fixpoint_is_lfp.smt2`.

`_grounded_ops.p` answers the review's "require contracts or mark them outside the supported tier"
with both: the one contract a grounded node carries is **functionality**, which is load-bearing
(`transpile` hash-conses, `Interner` shares, the e-graph merges, the cost model prices a shared node
once — all four are wrong without it), and the boundary is recorded in `REGISTRY.tsv`.

### Exact operator coverage, and the `Fold → iteration` alias replaced

`UnboundedTier.operators` lied in four places, each making a program look better covered than it
was, since the printed table shows a row only for the keys the function emits:

| was | now |
|---|---|
| `Fold` keyed to `"iteration"` | `"fold"`, with U59 as the *conditional* law (constant update) and `negative/not_fold_eq_iter.p` (N09) as the machine-checked witness that the unconditional identification is false |
| `Range` fell through into its **operand** | `"range"`, with U61/U62 |
| `Call` itself **dropped**, only arguments visited | `"call"`, with U63–U66 |
| `GroundedPS`/`GroundedSS` **omitted entirely** | `"grounded"`, with U67 and N11 |

A new test, `tier-3 covers EVERY algebra constructor`, closes the loop both ways: `allOperatorKeys`
runs `operators` over one term per constructor, every key must have a registry obligation, and no
registry row may file against a key `operators` never emits. So a key can neither be invented
without a proof nor proved without appearing in the table, and a new `Space` constructor makes the
match fail to compile rather than silently contribute nothing.

### Tier 3 connected to the implementation by conformance obligations

`src/test/scala/TierThreeConformance.scala` is the review's "generated/shared definitions or
conformance obligations" for the `generalises` column, which was traceability with nothing checking
it. Sixteen tier-3 laws are re-stated as **executable predicates** and run against the reference
executor **and both trie backends** on random inputs: 3200 executed law checks covering **50 of the
67 registry rows**. The remaining 17 are listed in `notExecutable` **with a reason each** (they
quantify over a reified body, or over all spaces, or are proof-internal induction premises), and a
gate fails on a row that is in neither list — so "no check" is a recorded decision. A second gate
fails on a reference to a row that does not exist.

### Countermodels for the negative controls, and timeout distinguished from validation

`run.sh` can only report a negative control as `NOT-PROVED (expected)` on a **timeout**, which is the
absence of a proof, not a semantic separation. All **eleven** now have an **executed countermodel** —
a concrete input at which the false law fails, checked against the executor and written to
`proofs/unbounded/COUNTERMODELS.tsv`, with a gate that every declared control has one:

    not_wrap_nest_reversed     A={x}, U=u, V=v: lhs={v.u.x} rhs={u.v.x}
    not_ti_monotone            A={p.1} ⊆ B={p.1,q.2}: ti(A)={1} ⊄ ti(B)={}
    not_iter_split             A={p.1} B={p.2.3}: iter(A∪B)={} vs iter(A)∪iter(B)={ε;3}
    not_fold_eq_iter           src={a.1,b.1}, update=acc·h: fold={z;z.a} vs iter-at-seed={z}
    not_range_monotone         A={m} ⊆ B={a,m}: rng(A,1,2)={m} ⊄ rng(B,1,2)={a}
    not_grounded_monotone      f = {x,y}∖·, A={x} ⊆ B={x,y}: f(A)={y} ⊄ f(B)={}
    … and five more

`not_ti_monotone` is the exact witness `terminating/mono_soundness.smt2` (O3d-X1) records, now
executed rather than cited.

    sh proofs/unbounded/run.sh                       # 67 certified, 0 open, 11 controls held
    sbt 'testOnly morkl.TierThreeConformance'        # 3/3
    sbt 'testOnly morkl.UnboundedTier'               # includes the new coverage gate

## 9. Clean, internally consistent artifacts — **PARTIAL**

* **Done.** This document is part of the delivered change and its verdicts are per item with the
  missing work named. The review input itself (`review.md`) is deliberately untracked and
  `.gitignore`'d, with the reason recorded there: a review document quotes the state it reviewed,
  several of whose files no longer exist by design, and `scripts/check_references.py` scans every
  TRACKED file.
* **Done.** `scripts/__pycache__/toolpath.cpython-312.pyc` removed, `__pycache__/` and `*.py[cod]`
  ignored.
* **Done.** `docs/TRUSTED.md` is the acceptance contract: the complete list of what a `PROVED`
  verdict rests on (six assumptions, each with why it is not derived, what stands in for a proof and
  what would break if it were false), plus O6a/O10b/O12b listed separately as **gaps, not
  assumptions**. Linked from `README.md` and `docs/atlas.md`.
* **Done.** Status artifacts regenerated and self-consistent: `proofs/unbounded/STATUS.tsv`,
  `COUNTERMODELS.tsv`, `proofs/pipeline/STATUS.tsv`, `proofs/pipeline/DECLARED.tsv`,
  `proofs/pipeline/fixpoint-gate/STATUS.tsv`, and every emitted `.egg`/`.smt2`. Source anchors
  touched by this change are updated, and both reference-check modes report 0.
* **Done.** Benchmark artifacts regenerated from a clean, identifiable commit — item 6.
* **NOT done, and this is the acceptance blocker.** There is no zero-failure record. Five cost-model
  gates are red, and the proof matrix still contains `OPEN`, `TRIVIAL`, `IDENTICAL-STRUCTURE`,
  `LAW-JUSTIFIED` and `SINGLE-SIDE` cells — twenty of ninety-seven artifacts are `REAL`. A recorded
  baseline failure is still a failure, and the review is right that this cannot be accepted as it
  stands.

## Reproducing everything above

    export ZIPPY_TOOLS=/path/to/dir/containing/z3/vampire/egglog   # or $Z3/$VAMPIRE/$EGGLOG

    sbt test                                        # the whole suite
    sbt 'testOnly morkl.FixpointSemantics'          # item 1's regression, incl. the prover gate
    sbt 'testOnly morkl.SubstConformance'           # item 2's O6a differential
    sbt 'testOnly morkl.TierThreeConformance'       # item 8's conformance + countermodels
    sh  proofs/unbounded/run.sh                     # item 8's tier-3 corpus
    python3 scripts/audit_pipeline_markers.py --run # item 3's declared-matrix gate
    python3 scripts/check_references.py --strict          # item 5
    python3 scripts/check_references.py --fresh --strict  # item 5, fresh-checkout
    python3 scripts/toolpath.py                     # item 5, what resolves
