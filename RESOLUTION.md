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
| 6 | regenerate benchmark artifacts from an identifiable source state | **OPEN** |
| 7 | preserve disjointness across spills | **OPEN** |
| 8 | finish and connect the unbounded tier | **RESOLVED** |
| 9 | clean, internally consistent artifacts | **PARTIAL** |

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

### Not done: carrying the binders through the instance renderers

The review's third bullet — remove the `Iteration`/`Fixpoint` arms from `EquivPipeline.expand`, or
stop using `expand` to produce proof sides — is **not** done, and this is the reason item 1 is
PARTIAL and item 3 keeps four of its five bullets open.

**THE HONEST CAUSE IS THAT THE WORK WAS NOT ATTEMPTED**, not that it was found to be blocked. The
effort available went to items 1, 2, 5 and 8, where the changes could be finished and verified. What
follows is what an attempt would face, separated into what is actually checked and what is estimate.

CHECKED — the vocabularies, by reading them:

* `formal.egg` (the stage-1 instance vocabulary) **already carries `Fixpoint`**: `Fix Space FBody`
  with `FBodyK i64`, "program-defined step, indexed; one FApp rule per index". So the FIXPOINT half
  of this bullet needs NO vocabulary extension, and `puzzle3-full` — the cornerstone whose recursion
  is an unbounded `Space.Fixpoint`, and whose `-space` cell is `IDENTICAL-STRUCTURE` — is the case it
  would bite on first. This is a smaller, self-contained slice than the restructuring, and not
  attempting it is the least defensible part of this gap.
* `formal.egg` does NOT carry a **head-dependent** `Iteration`: it has `IterC`, the loop-INVARIANT
  body form, and its header says the head-dependent `Iter` lives in the zipper prelude. So the
  ITERATION half does need either new `Iter`/`BodyK`/`App` machinery in the formal vocabulary — each
  rule needing its own law certificate, per this tree's own discipline — or that leg moving to
  `prelude.egg`, which changes what "the eager set-of-paths reference system" means for stage 1 and
  is a claims change as much as a code change.
* `zipper-egg-tests/bridge-prelude.egg` (stage 3) carries `Iter Z Body` and `App Body i64 Z`, but its
  `Body` datatype has no `BodyK i64 IL ZL` and the file has no `IL`/`ZL` sorts — `prelude.egg` has
  all three. So stage 3 needs those declarations before a program-defined iteration body can be
  rendered into it.
* stage 2's "virtual" leg already builds exactly the program the review wants — `unrollControl` over
  literal-bound inputs, rendered by `renderZ`, which carries both `Iter` and `Fix` — so the pattern
  to generalise exists and is working.

ESTIMATE, and labelled as such: `expand`'s output also feeds `collectKeys`, `implOfSpace`,
`tnodeOf` and the membership-observation machinery, and it is the executor-agreement gate
(`eval(expand(p)) == eval(p)`), so removing its arms is not a local edit; and each iteration of the
attempt costs a 35-50 minute prover run to evaluate. Neither of those was measured against an actual
attempt.

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

### Not done: four of the five required changes

No opaque symbolic source in `SpaceZipper`; no independent instance rendering paths; no replacement
of the `SINGLE-SIDE-OBSERVATION` / `TRIVIAL` / marker-to-marker cells; no deliberate discharge of the
four opens. All four are blocked on the same restructuring as item 1's third bullet.

One of the four opens did close, as a side effect of fixing `bridge-prelude.egg` below rather than
by any intended work on this item: `nqueens-zipper.smt2` is now `unsat` / `PROVED` where it was
`OPEN (prover budget exceeded)`. Three remain: `puzzle15-graph-agnostic`, `puzzle15-zipper` and
`puzzle3-full-graph-agnostic`.

### Done: the fifth — the matrix is now a checked claim, and the headline claim is corrected

The review's last bullet asks for a gate that fails on any missing, trivial, single-sided or
unexpected-open **required** cell. That needs a declared required set, and there was none: the audit
walked whatever was on disk, and ratcheted marker-to-marker *chains* only.

`proofs/pipeline/DECLARED.tsv` is now that declaration — one row per artifact, naming what the cell
**is**, with the kinds and what each is worth spelled out in its header. `audit_pipeline_markers.py`
fails on drift in **either** direction:

* a cell whose observed kind differs from its declaration. A cell declared `REAL` that becomes a
  marker is a cell that *stopped carrying an obligation* — the regression the gate exists for — and
  a cell that improves fails too, until the claim is updated, because the matrix is a published
  claim and changing a claim belongs in a diff;
* an artifact with **no declaration**: a new cell may not arrive unclaimed;
* a declaration with **no artifact**: the **missing-cell** case, which previously left no trace at
  all because the audit only ever walked what existed.

Updating the claim is a separate command (`--declare`) that never runs as a side effect of an audit,
and the run prints how many declared cells are `REAL` — the only kind that is a certified
equivalence — out of the total. Both drift directions are negative-tested: declaring a `TRIVIAL`
cell `REAL`, and declaring a cell that no longer exists, each make the audit exit 1 with the cell
named.

**What the declaration currently says**, over the 98 emitted artifacts (both directories, all three
stages, both tiers, both variants):

    REAL=22   TRIVIAL=31   IDENT=16   BUDGET=13   SINGLE-SIDE=9   LAW-JUSTIFIED=7
    REAL is the only kind that is a certified equivalence: 22/98

and `proofs/pipeline/STATUS.tsv`, the SMT half of it, reads
`PROVED=9  TRIVIAL=15  IDENTICAL-STRUCTURE=11  LAW-JUSTIFIED=4  OPEN=3` out of 42. That is the
shape the review objected to, now written down instead of inferred. The 12 marker-to-marker chains
remain, at the pinned ratchet.

The audit's `--run` mode — which actually invokes egglog on every non-marker `.egg` and z3 on every
non-marker `.smt2`, rather than grepping for `(check` — now passes for the first time. It could not
have before: `bridge-prelude.egg` did not load, so seven artifacts were rejected outright while
four of them looked verified on disk.

    python3 scripts/audit_pipeline_markers.py --run --timeout 90
    # 98 cells, 0 drifted, 0 undeclared, 0 missing; marker audit: OK

This is the review's "**or** reduce the stated cornerstone/support matrix" option: the shape of the
matrix is written down and checked instead of being inferred from marker vocabulary. It does **not**
discharge anything, and it is not a substitute for the other four bullets.

`README.md`'s verification paragraph is corrected in the same spirit. It said the pipeline "proves
per program that the optimised term, the zipper program, and the compiled operation graph are
observationally equivalent to the reference semantics ... on seven cornerstone programs", which
overstates a matrix in which a minority of the 42 cells are `PROVED`. It now says what the pipeline
*emits*, defines each marker kind and what it is worth, states that only `PROVED` counts, and points
at `proofs/pipeline/STATUS.tsv` and at this document.

### Also removed: two artifacts left stale by that bug

`aunt-space-lit.egg` and `nqueens-space-lit.egg` were `BUDGET-EXCEEDED` markers whose attempt log
read `Unbound function SelfBody` — they existed only because the `-impl` fallback could not load.
With the prelude fixed the `-impl` fallback works and the `-lit` degradation is never reached, so
both are deleted rather than left on disk claiming a budget was exceeded for a reason that no longer
exists.

### Found and fixed: `bridge-prelude.egg` did not load

One thing was found while running the suite for the first time with all three tools present, and it
is worth recording because it made a whole family of artifacts unverifiable.

**`zipper-egg-tests/bridge-prelude.egg` did not load.** Its park block was ported from
`prelude.egg` and uses `(SelfBody)`, `Fix` and `FApp`, but none of the three was declared in this
file's own `datatype*` block. egglog rejects the file outright with `Unbound function SelfBody`, so
**every** artifact that includes it failed at every rounds budget — the seven `-lit`/`-impl`
fallbacks in `zipper-egg-tests/pipeline/`. Four of them (`aunt-space-lit.egg` and friends) were
nevertheless committed *without* a `BUDGET-EXCEEDED` marker, i.e. indistinguishable on disk from
files that had been verified. The three declarations are added, and every `.egg` file in the tree now
loads:

    for f in formal.egg zipper.egg zipper-spec.egg zipper-impl.egg zipper-egg-tests/*.egg; do
      egglog "$f" >/dev/null || echo "REJECTED: $f"; done      # silent


## 4. Every cost-model acceptance gate green — **PARTIAL**

Measured on this machine, with all three tools present:

| run | result |
|---|---|
| baseline at `f6832fc` (`sbt test`) | **574 tests, 8 failures** |
| after this change (`sbt test`) | **573 tests, 5 failures** |
| after this change, everything except the 35-minute `EquivPipelineTest` (`sbt 'testOnly -- -morkl.EquivPipelineTest'`) | **594 tests, 5 failures** |

The five are the same five cost-model gates in both runs, listed below. The third run covers the
final state of the tree (the second predates two of the new suites) and runs the tests `sbt test`
skips as already-current, which is why its total is higher.

Three of the baseline's eight are gone: `EquivPipelineTest` is green (it was an initialisation error
with no prover installed, and once it ran, seven of its cells failed for the reason in item 3), and
`SpatialAcceptance.5c` and `SpatialPipelineCheck.COST` were the two contention-sensitive wall-clock
failures.

### Done: the two wall-clock gates

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

The other wall-clock gate, `SpatialPipelineCheck.COST`, failed in the baseline run and passed in
both later runs — the same contention sensitivity. It has **not** been given the same treatment.

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

## 6. Regenerate benchmark artifacts from an identifiable source state — **OPEN**

Not addressed. `docs/BENCHMARKS.md`, `corpus_runtimes.csv`, `prog_matrix.tsv` and
`expressivity.csv` are regenerated by this change's test runs but still carry a `-dirty` source
stamp, and no clean-commit-then-artifact-commit split has been made. The toolchain fields the review
asks for (exact JDK, Scala, sbt, flags) are not added.

The third bullet **is** done: `README.md` no longer makes an ignored, untracked local tool
directory the sole reproduction recipe. It documents the ordinary installation of all three tools, with the versions
this tree is verified against, and points at `toolchain.conf` as the resolution policy.

## 7. Preserve disjointness across spills — **OPEN**

Not addressed. `otherKeys` still enumerates at most `MaxSpillKeys = 4096` names and still degrades
to ⊤ above the cap; the depth test still accepts exact predictions only through `MaxDepth + 1`; the
stale "four-channel Shape" comments are unchanged.

**THE HONEST CAUSE, first:** the effort available went to items 1, 2, 5 and 8. This one was read,
scoped, and then deliberately not started. Two reasons, one of them a genuine prioritisation and one
of them just the budget:

1. **It is the only item with no red gate and no soundness hole.** Its tests currently PASS — they
   encode "exact through `MaxDepth + 1`, linear past the cap" as the *expected* result, which is
   precisely what the review objects to. So what is unmet is an ambition about precision, not a
   wrong answer or a false certificate, and it ranked below the items that were.
2. **A half-finished channel would most likely have broken what had just been made green.** The
   design the review points at — carry a provenance/partition tag instead of an enumeration, decide
   disjointness symbolically, intern the size-dependent set comparison once at spill time rather
   than on every lattice step — is a NEW CHANNEL, and in this carrier a channel is not local: it is
   consumed by `Shape.contains` (γ), `leq`, `joinAlternatives`, `meet`, `widen`, `unionTransfer`,
   `possibleHeads`, `isTop` and `SpatialAnalysis.capWidth`. `Shape.isTop`'s own comment records what
   happens when a new channel misses one of them: *"a prototype key certificate that did not was
   caught by the randomized order matrix in one pass: `{ε?, +[0,inf] more of 2 named}` looked like ⊤
   to `leqStrong`'s short circuit, so the order accepted a left-hand side with thirteen heads while
   γ — which enforced the certificate — rejected its values."* That is the `SpatialSoundnessHunt` /
   `SpatialLawCheck` γ-simulation matrix, i.e. exactly the suites that had just been brought back to
   green after the item-1 executor change.

Neither reason makes the work optional. It is the one item where the review's stated ambition is
rejected outright rather than partly met, and the last two required changes — tests at
`MaxSpillKeys + 1` and well beyond `MaxDepth + 1` that demand the same growth class as the unspilled
family — cannot even be written until the carrier changes, because today they would simply fail.

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

* **Done.** This document is part of the delivered change, and its verdicts are `RESOLVED` /
  `PARTIAL` / `OPEN` per item with the missing work named. The review input itself
  (`review.md`) is deliberately *not* tracked: it is an input, not an artifact.
* **Done.** `scripts/__pycache__/toolpath.cpython-312.pyc` is removed and `.gitignore` now excludes
  `__pycache__/` and `*.py[cod]`.
* **Partial.** Status artifacts are regenerated by the runs above —
  `proofs/unbounded/STATUS.tsv`, `proofs/unbounded/COUNTERMODELS.tsv`,
  `proofs/pipeline/fixpoint-gate/STATUS.tsv`, `proofs/pipeline/*` and
  `zipper-egg-tests/pipeline/*`. Source anchors touched by this change are updated. The benchmark
  artifacts are **not** regenerated from a clean identifiable commit (item 6).
* **Not done.** There is no zero-failure acceptance record. Five cost-model gates are red (item 4),
  and the proof matrix still contains `OPEN`, `TRIVIAL`, `IDENTICAL-STRUCTURE` and marker-only cells
  (item 3).

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
