# The trusted base

Every claim this tree makes rests on some assumption. This file is the **complete list of the
assumed FACTS**, so that "PROVED" in a status table can be read without reconstructing what it is
proved *relative to*. Nothing else may be assumed; anything not here is either derived or is an open
obligation named in a registry.

**Two distinctions that an earlier revision of this file left implicit, and that its "complete list"
claim needs.** A proof corpus contains axioms of two quite different kinds:

* **Definitional axiomatization** — the clauses that *say what the objects are*: `_signature.p`'s
  sorts and operations, `_paths.p`'s free-monoid laws for `nil`/`cons`/`app`, `_nat.p`'s arithmetic.
  These are not assumptions that could be false; they are the subject matter. They are not listed
  here and do not need to be.
* **Assumed facts about those objects** — clauses that *could* be false and are not derived in the
  corpus. Every one of these is a T entry below.

That distinction is now **enforced rather than stated**: any axiom file carrying an `% ASSUMED`
block must also carry a `% TRUSTED-ENTRY: T<n>` marker naming its entry here, and
`scripts/proof_closure.py --check` fails if it does not, or if the entry does not exist. The check
was added because the claim was already false: `_card.p` declared six assumed counting axioms, in
its own header, and none of them was a T entry — see **T7**.

## The three markers, and which direction each points

There are now **three** machine-read markers about this list, and they are deliberately separate
because they make three different claims. Conflating any two of them would make one of the
directions unfalsifiable.

| marker | in | says | read by |
|---|---|---|---|
| `% TRUSTED-ENTRY: T<n>` | an axiom file with an `% ASSUMED` block | *this file asserts* entry T\<n\> | `proof_closure.py --check` |
| `; TRUSTS: <list>` | an **emitted artifact** (SMT, egglog, TPTP) | *this artifact's claim rests on* these entries | `proof_closure.py`, `audit_pipeline_markers.py` |
| `% MECHANIZED-IN: <file>#<thm>` | the file that *asserts* an entry | *that entry is a Lean-checked theorem*, so it is no longer assumed | `check_lean.sh`, then `proof_closure.py` |
| `MECHANIZED-IN: <file>#<thm>` | an entry's section **in this file** | *the entry's schema itself* is a Lean-checked theorem, so every row reaching the entry is discharged at once | `check_lean.sh`, then `proof_closure.py` |
| `; ASSUMED: T<n>` / `; PREMISE: …` / `; DERIVED-FROM: <file>` / `; DEFINITION` / `; STONE` / `; GOAL` | the comment **directly above one `(assert …)`** in an SMT obligation | what that one assert *is*: a trusted entry, a hypothesis of the stated theorem, a lemma certified elsewhere, a characterisation of a declared symbol, an in-file stepping stone, the negated goal | `scripts/check_asserts.py` (plan.md 2E.4), which writes the SMT tiers' closure table for `proof_closure.py` |

**The per-assert markers exist because the SMT tiers had no closure at all.** SMT-LIB has no
`include`; an obligation carries its axioms inline, and `proof_closure.py` could not tell a
`(declare-fun append …)` characterisation from an asserted induction schema. Measured on 2026-09-04:
the six SMT corpora hold 1686 top-level asserts, 52 of which were structural-induction schema
instances (the SMT twin of T1, over `Path`, `KList`, `KV` and the mutual `FKV`/`FTrie`) or
bridging inductions over a chain index (T8) with no marker and no entry, plus the counting facts
T7 names and a few dozen per-file premises. `scripts/check_asserts.py` now classifies every one
mechanically (goal, in-file stepping stone, characterisation of a declared symbol, the two
prelude lemmas by formula) or by marker, **fails on an unclassified assert**, and writes
`target/assert-closure.tsv` — one row per obligation with the trusted entries its asserts reach,
transitively through `; DERIVED-FROM:` edges — which `proof_closure.py --check` consumes exactly
as it consumes the TPTP include closure. The generators (`gen_law_obligations.py`,
`gen_spatial_obligations.py`, `gen_spatial_semantic_obligations.py`, `AgSmt` in
`EquivPipeline.scala`, `FixpointSemantics.scala`) emit the markers, so regeneration keeps them.

The first two **declare** a dependency; the third **discharges** one. A discharge that silently
deleted a declaration would leave nothing to audit, which is why `% MECHANIZED-IN:` never edits a
`; TRUSTS:` line — the closure computes the difference, and `proof_closure.py` prints both halves.

### `; TRUSTS:` — the artifact header

`src/main/scala/Certified.scala` is the single specification: `Certified.trustsHeader` writes the
line, `Certified.readTrusts` reads it, `Certified.HeaderPattern` is the one regex, and
`Certified.Trust` is the vocabulary. It exists because review items 4 and 8 each need the other's
output — item 4 must record what each cornerstone cell's claim rests on, item 8 must know what each
artifact claims in order to decide whether any unqualified `PROVED` is honest — and that is the only
real cycle in `plan.md`'s dependency graph. Fixing the format first, with no consumer, breaks it.

    ; TRUSTS: -
    ; TRUSTS: T4, law:unwrap-merge
    ; TRUSTS: O10b, outside:Range

The vocabulary is exactly four forms plus `-`:

* **`T<n>`** — an entry of this file.
* **`O<n><letter?>`** — an **open** obligation row of `terminating/REGISTRY.tsv` or
  `proofs/unbounded/REGISTRY.tsv`. An open row is *not* a trusted assumption; it is a gap (see *Open
  obligations* below), and an artifact leaning on one is reporting something strictly worse than an
  assumption. It is in the vocabulary so that it can be **said**, not to make it acceptable.
* **`law:<name>`** — a law of the optimiser's ∀-certified set (`proofs/laws/REGISTRY.tsv`). This is
  the `LAW-JUSTIFIED` case: the universal certificate *is* the proof for that pair.
* **`outside:<construct>`** — a term outside the certified path-set algebra, named by the construct
  that put it there. `Certified.boundary` is the one decision procedure, and every case it reports is
  a boundary already declared here or in a registry: `Range` → **T5**, the four `Grounded*` families
  → **T6**, `Call` → **O6a**, `Fixpoint` → **O10b**.
* **`-`** — trusts nothing.

**`-` is required, and a missing header is a failure.** Those are not the same thing, and the
difference is the whole point: *"this cell depends on nothing"* is a claim someone made, and
*"nobody said"* is a claim nobody made. A reader that returned "trusts nothing" for a file with no
header would let an emitter bug read as the strongest claim in the tree. `Certified.readTrusts`
returns `Left` for both a missing header and an unparseable token, and every reader must treat that
as a hard failure rather than skipping the line — a token silently dropped is a dependency silently
dropped.

### The `trusts` column

`proofs/pipeline/CLAIMS.tsv` carries the same vocabulary in a `trusts` column, so a declaration and
an emission are comparable without a translation step. It is the **permitted** set per cornerstone ×
boundary, declared *before* the artifact is built (task 2A.1); the emitted artifact's own
`; TRUSTS:` must be a **subset**, and trusting something the declaration does not permit is a
failure. Its column order is `Certified.ClaimsColumns` — declared in code rather than only in the
file's header, so the emitter and the two readers cannot disagree about it.

The `O<n><letter?>` ids the column may name are the **open** rows of `terminating/REGISTRY.tsv` and
`proofs/unbounded/REGISTRY.tsv`. Those two tables do **not** themselves carry a `trusts` column
today: their `kind` and per-row statements already say what each obligation is, and a column
duplicating this file's ids into 200-odd rows would be a second copy to drift. If a row's dependency
turns out not to be recoverable from its file (which is what `proof_closure.py`'s closure reads), the
column belongs there too — but it is not being added speculatively.

Two things are deliberately *not* on this list, because they are checked rather than trusted:

* the **executors** — `eval`, `exec`, `execT`, `evalT`, `evalI` — which are differentially tested
  against each other and against the corpus on every run;
* the **provers and the e-graph engine** (z3, vampire, egglog), which are ordinary software
  dependencies. Their versions are pinned in `README.md` and their verdicts are recorded per file.

Each entry says what is assumed, why it cannot be derived here, what stands in for a proof, and what
would break if it were false.

## Four entries are DISCHARGED (plan.md 1E.3, 2E.3, 2E.4)

**T1, T2, T3 and T8 are no longer assumed.** Both are induction principles over free algebras — the reason
each is here is a limitation of first-order logic, not a fact anyone doubted — and both are now
theorems in `proofs/lean`, checked by Lean's kernel with no axiom of its own beyond `propext` /
`Quot.sound` (`path_induction` uses **none**). `scripts/check_lean.sh` witnesses them and
`scripts/proof_closure.py` lifts the rows that reach them:

| row | table | verdict now |
|---|---|---|
| `mon_cancel` | `proofs/unbounded/STATUS.tsv` | `PROVED` (T1 discharged) |
| `wrap_roundtrip` | `proofs/unbounded/STATUS.tsv` | `PROVED` (T1 discharged) |
| `fixpoint_is_lfp` | `terminating/STATUS.tsv` | `PROVED` (T2 discharged) |
| `card_wrap` | `proofs/unbounded/STATUS.tsv` | `PROVED-MODULO T7` — T1 discharged, **T7 remains** |
| every SMT row whose asserts reach only T1 / T2 / T8 (115 files reach T1) | the five SMT tables | `PROVED` once `check_asserts.py` and `check_lean.sh` have run; `PROVED-MODULO T7` where a counting fact is also asserted |
| O12d / T3 | `terminating/REGISTRY.tsv` | `MECHANIZED (proofs/lean/Zippy/Whistle.lean)` — per run, when `SCReport.leanCovered` |

The entries stay in this file rather than being deleted, because they are still what the TPTP and
SMT corpora assert: a reader of `_path_induction.p` needs to know what it is and where it is
discharged. Each now opens with a **DISCHARGED** line naming the Lean theorem.

**T7 is not dischargeable this way, and the difference matters.** T1 and T2 are schemas; T7
axiomatises an *uninterpreted* function, so there is nothing to derive — proving the axioms would
mean choosing a `card`, which makes every theorem above a statement about that choice instead of
about any measure. `proofs/lean/Zippy/Counting.lean` supplies a **model** instead (finite sets with
`Finset.card` satisfy all six items, and `card_wrap` holds in it), which makes the residual
`PROVED-MODULO T7` demonstrably non-vacuous. What would make `card_wrap` unqualified is a *taxonomy*
decision — whether T7's counting axioms are definitional rather than assumed — and that file states
the case without making the call.

---

## T1. Structural induction over the free datatypes, at one predicate

MECHANIZED-IN: proofs/lean/Zippy/PathInduction.lean#Zippy.path_induction
MECHANIZED-IN: proofs/lean/Zippy/PathInduction.lean#Zippy.list_induction
MECHANIZED-IN: proofs/lean/Zippy/PathInduction.lean#Zippy.ftrie_induction
MECHANIZED-IN: proofs/lean/Zippy/Zipper.lean#Zippy.Zip.term_induction

> **DISCHARGED** by `proofs/lean/Zippy/PathInduction.lean#Zippy.path_induction` — the schema, for
> **every** predicate, depending on **no axioms at all** — and, for the SMT tier's other datatypes,
> by `list_induction` (generic in the element type: `KList`, `KV`) and `ftrie_induction` (the
> mutual `FKV`/`FTrie` pair of `isempty_finite.smt2`, declared in Lean as SMT declares it). The
> three lines above are what `proof_closure.py` reads to lift every row reaching T1 at once.
>
> **Scope, widened on 2026-09-04.** This entry used to say "over `path`" because the TPTP tier was
> the only place the schema was *marked*. `scripts/check_asserts.py` found it asserted 43 more times
> across the SMT corpora (`; ASSUMED: T1` now sits above each), over `Path` in the laws and bridge
> files and over `KList`/`KV`/`FKV`/`FTrie` in the trie-implementation files. Same schema, same
> discharge; the count is in `target/assert-closure.tsv`. That file reproduces this entry's
> derivation rather than shortcutting to the conclusion: `_paths.p`'s three freeness axioms as
> theorems, the schema generically in `Phi`, both premises at the cancellation predicate, the
> instance stated verbatim, then `mon_cancel`. Proving only the conclusion would have left the
> *schema* — the trusted item — undischarged, which is the distinction the next paragraph draws.

**File:** `proofs/unbounded/_path_induction.p` · **Used by:** `mon_cancel.p`, hence `_cancel.p`,
hence `wrap_roundtrip.p` and `card_wrap.p`

    ( Phi(nil)  and  ForAll H,T. (Phi(T) => Phi(cons(H,T))) )  =>  ForAll P. Phi(P)

instantiated at `Phi(P) := "app(P, ·) is injective"`.

**Why it is not derived.** `path` is the free term algebra generated by `nil` and `cons` (its
freeness axioms are in `_paths.p`), and for such an algebra this schema is valid. It is a *schema* —
it quantifies over the formula `Phi` — so first-order logic cannot state it and a saturation-based
prover has no rule for it. The direct attempt is logged in `mon_cancel.p`: vampire `--mode casc` at
180 s, `--induction struct`, `--induction int`, and an SMT-LIB2 rendering with `declare-datatypes`
for `Path` (with and without `define-fun-rec`) all time out, as does z3 on the same rendering. No
countermodel from any of them.

**What stands in for a proof.** Both premises are separately machine-checked obligations in the same
corpus: `mon_cancel_base.p` and `mon_cancel_step.p`, both PROVED. And what is trusted mentions `app`
only *inside* those premises — instantiate `Phi` at any other property of paths and the axiom is
just as true, so nothing about what `app` computes is being assumed.

**If it were false**, term-algebra induction would be unsound and `wrap_roundtrip` / `card_wrap`
would lose their premise. This is the same discipline `terminating/fixpoint_is_lfp.smt2` uses for its
four inductions — base and step machine-checked, then the bridging principle asserted exactly as a
hand proof invokes it (T2).

## T2. The four bridging induction principles of `fixpoint_is_lfp.smt2`

MECHANIZED-IN: proofs/lean/Zippy/Fixpoint.lean#Zippy.Kleene.stationary_is_lfp

> **DISCHARGED** by `proofs/lean/Zippy/Fixpoint.lean#Zippy.Kleene.stationary_is_lfp` and the four
> theorems it composes — `chain_ascends`, `acc_eq_chain`, `init_subset_chain`,
> `chain_below_prefixpoint`. Over `Nat` the bridge is `Nat.rec`; the SMT file needs it asserted
> because its chain index is an unguarded `Int` with a `>= n 0` side condition rather than a
> well-founded type. Both premises (monotone `F`, `init ⊆ F init`) are explicit parameters of every
> one of them, so none can be read as unconditional.
>
> **Part (iv) is NOT discharged**, and it is not one of the four: that the stationary index *exists*
> over a finite universe is a single `card` check whose bridging principle lives in
> `no_infinite_descent.smt2`. `stationary_is_lfp` takes the stationary index as a hypothesis for
> exactly that reason — it says what the answer *is* once the loop stops, not that it stops.

**File:** `terminating/fixpoint_is_lfp.smt2` lines 210, 229, 246, 262 · **Used by:** every
`Fixpoint` claim in the tree

The chain-ascends, accumulator-redundant, above-`init` and below-every-pre-fixpoint inductions. Each
is asserted after its **base and step have been discharged in the same file** (each `(push)` /
`(check-sat)` / `(pop)` block above it is a real z3 query expected `unsat`). As with T1, what is
trusted is the induction principle, not the conclusion.

The file also **assumes semantic monotonicity of `F` as an axiom and says so** (line 46). That is not
a gap: monotonicity is discharged in the compiler by the syntactic gates `MORKL.mono` / `monoIn` and
`AgnosticPipeline.monotoneInMention`, whose own soundness is the separate obligation
`terminating/mono_soundness.smt2` (O3d / O4b) — two of whose arms were machine-**refuted** and are
now conservative (rows O3d-X1, O3d-X2).

## T3. The whistle terminates (Kruskal's tree theorem)

MECHANIZED-IN: proofs/lean/Zippy/Whistle.lean#Zippy.Whistle.kruskal
MECHANIZED-IN: proofs/lean/Zippy/Whistle.lean#Zippy.Whistle.whistle_terminates

> **DISCHARGED** (plan.md 2E.3) by `proofs/lean/Zippy/Whistle.lean#Zippy.Whistle.kruskal` —
> Kruskal's tree theorem, proved from Mathlib's Higman lemma by Nash-Williams' minimal bad sequence,
> because the pinned Mathlib has Higman and not Kruskal (`scripts/check_lean.sh --probe-kruskal`) —
> and `whistle_terminates`: extending a whistle-free path is a well-founded relation.
>
> **What the theorem needs, and where the implementation now supplies it.** Kruskal needs the label
> relation to be a well-quasi-order; over a finite alphabet, equality is one. `Matching.coupledS`
> compared canonical bound names, full `RoutinePtr`s, `Range` bounds and closure identities by
> equality over *unbounded* sets, so the whistle as implemented was **not** a well-quasi-order (an
> infinite antichain of nested `Iteration`s exists) and this entry's statement was false of the
> code. `Matching.labelOf` fixes the alphabet the whistle couples over (all variables of a sort share
> a label; a call is labelled by its *original* routine and arities) and `SC.State` checks per run
> that no label outside the inputs' alphabet was minted (`alphabetEscapes`) and that every blow was
> acted on (`whistleFallbacks`, the coarse whistle vs the fine generalizer). `SCReport.leanCovered`
> says whether a run is inside the theorem. Coverage is therefore **per run and reported**, not
> assumed; what remains operational is the `Deadline`, for runs the report says are not covered.

**Registry row:** `terminating/REGISTRY.tsv` O12d · **Code:** `Supercompiler.scala` (homeomorphic
embedding whistle) · **Status: MECHANIZED, per run**

The homeomorphic embedding on the configuration signature is a well-quasi-order, hence driving
terminates.

**Why it is not derived.** The standard proof is Kruskal's tree theorem, which is outside what z3 or
vampire will find; there is no checked library boundary available here to import it from.

**What stands in for a proof.** Nothing, in the prover corpus. The compensating checks are
operational: the supercompiler runs under an explicit `Deadline` (`all_forever(..., budget)`), so a
non-terminating drive is a *timeout* rather than a hang, and `SCHardening` / `SCDriver` exercise the
whistle on the corpus.

**If it were false**, `SC.reduce` could fail to terminate on some program. It would not produce a
*wrong* answer: soundness of each individual rewrite is O12a and the certified law set, which is
independent of whether driving stops. The consequence is liveness, not correctness — which is why it
is admitted rather than blocking, and it is named here so that a reader of `docs/SUPERCOMPILER.md`
does not have to infer it.

## T4. `EquivPipeline.expand` — the stage-0 control-flow expansion

**Code:** `src/main/scala/EquivPipeline.scala` · **Gated by:** `EquivPipelineTest`

`expand` evaluates `Range`, grounded nodes and (currently) `Iteration` / `Fixpoint` / `Fold` / `Call`
into pure local algebra before the instance proofs run. Each expansion step *is* the corresponding
`exec` evaluation rule.

**What stands in for a proof.** `EquivPipelineTest` asserts `eval(expand(p)) == eval(p)` for every
cornerstone before emitting anything, so the expansion is checked per instance against the executor.

**If it were false**, the instance obligations would be about a different program than the one that
runs. Note that the acceptance review of `f6832fc` requires this trusted boundary to be **removed**
for `Iteration`/`Fixpoint` — the binders should reach the renderers — and that work is open; see
`plan.md`, Track A′ (item 4) and Track D (item 2).

## T5. `Range` is outside the certified path-set algebra

**Code:** `Space.Range`, `RangeBounds.normalize`, `IntTrie.range`

`Range` is a *positional* window: whether a path survives depends on its **rank** in the canonical
order, not on membership, so it is the one operator whose semantics cannot be written as a formula in
`mem(·, A)`. It is therefore not covered by the pointwise algebra laws.

**What stands in for a proof.** Two tier-3 theorems, both PROVED:
`proofs/unbounded/range_window.p` (U61: a window is inside its source; a full window is the
identity) and `range_interval.p` (U62: a window is an **interval** of the canonical order, for an
*arbitrary* strict total order — which is what makes the four backends agree on it, since they all
slice by `pathValueOrdering`).

**Non-monotonicity is NOT certified by this tier, and a previous revision of this entry said it
was.** It claimed the fact was "pinned by (N10) with an executed countermodel", N10 then being a
monotonicity control. Both halves were wrong together:

* `_range_ops.p` axiomatises the window with **path** endpoints — `rng(A,Lo,Hi)` is
  `{P ∈ A : Lo ≤ P < Hi}` — deliberately, because naming the endpoints by *rank* needs counting the
  module avoids. With the endpoints fixed, the window is a pointwise order-interval filter, and
  such a filter **is monotone**: `rng_sub` and `rng_bounds` give `mem(P,A)` and the bounds,
  `A ⊆ B` gives `mem(P,B)`, and `rng_full` puts `P` in `rng(B,Lo,Hi)`. Vampire proves the control's
  conjecture in seconds. So it was not an unprovable statement being used as a control — it was a
  **theorem** labelled as a refutation.
* the recorded countermodel (`A={m} ⊆ B={a,m}` with bounds `1..2`) is a real fact, but about
  **integer** bounds, i.e. about `Space.Range` and `RangeBounds.normalize` — not about the sentence
  it was filed against.

It also went undetected for a round because the file's includes did not resolve under `run.sh`'s
`cd negative`, so vampire could not read it at all and the harness scored the resulting non-answer
as "NOT-PROVED (expected)". `run.sh` now treats an unreadable file as a hard failure on both loops,
and N10 has been replaced by `negative/not_range_identity.p`, which is genuinely unprovable here and
pins the near-miss of U61 (if a window were the identity for *arbitrary* endpoints, U61's
full-window hypothesis would be vacuous).

**So what is trusted here is wider than it was.** The non-monotonicity of `Space.Range` is an
executed observation about the executor and a property of rank arithmetic in tier 1/2
(`SpatialTypeSystem.windowWidth`); it is **not** a machine-checked theorem anywhere in this tree.
`AgnosticPipeline.monotoneInMention` and `MORKL.mono`/`monoIn` refuse a recursion variable under a
`Range` for that reason, and that refusal is the conservative direction, so nothing unsound follows
from the gap — but it is a gap, and it is stated here rather than implied by a control that does not
hold.

**If it were false** — specifically, if a window were not an interval of the order every backend
slices by — the backends could disagree on `Range` even though each is individually correct.

## T6. Grounded functions are deterministic

**Code:** `Space.GroundedPS`, `Space.GroundedSS` · **Contract:**
`proofs/unbounded/grounded_functional.p` (U67, PROVED)

An arbitrary Scala function `f` is opaque, so no algebraic law about it can be stated. The one thing
assumed is **functionality**: equal inputs give equal outputs.

**Why it is load-bearing.** `transpile` hash-conses the op-graph, `Interner` shares literals, the
e-graph merges equal terms, and the cost model prices a shared node **once**. All four are wrong for
a grounded function that consults a clock or a mutable cell, and nothing in the Scala type says so.

**What is explicitly NOT assumed.** Monotonicity — `negative/not_grounded_monotone.p` (N11) is the
control, with an executed countermodel. This is why `monotoneInMention` and `MORKL.mono` / `monoIn`
refuse a recursion variable under a grounded node.

## T7. The counting axioms

> **NOT DISCHARGED, and not dischargeable the way T1 and T2 were** — see the banner above.
> `proofs/lean/Zippy/Counting.lean` is a **model**: finite sets of paths with `Finset.card` satisfy
> all four counting axioms, the injective-image axiom and the comprehension, and `card_wrap` holds
> in it. That makes the residual `PROVED-MODULO T7` non-vacuous, which is not a formality here:
> `_nat.p` records that vampire *refutes* `_signature.p + _card.p` outright when `card` is
> `$int`-valued, and `run.sh`'s vacuity probe against that is a negative check with a 10 s budget.
> A model is the positive statement and does not expire.

**File:** `proofs/unbounded/_card.p` · **Used by:** `card_wrap.p`, and anything whose closure
reaches it · **SMT-tier instances (`; ASSUMED: T7`, 2E.4):** the `card ≥ 0` and strict-monotonicity
axioms of `terminating/{fixpoint_is_lfp, asfixpoint_sound, bounded_growth_decrease, datalog_*,
reachable_decrease, scc_decrease}.smt2`, the per-length-class count facts of
`proofs/spatial/sp_class_{bounds,ie_tighter}.smt2`, and the measure facts of
`proofs/spatial-semantic/gsem_join_union_sound.smt2` — the same counting facts, about a
`card`/count that is uninterpreted there too, so the same entry and the same non-discharge.

Six clauses, and `_card.p`'s own header is the authoritative list of them:

* four counting axioms — `card_empty`, `card_sing`, `card_mono`, `card_disj_add` (non-negativity
  comes free from `_nat.p`'s `zero_le`);
* one axiom and one comprehension of a different character — that an **injective image has the same
  cardinality**, and the `pfxmap` comprehension asserting the prefix map exists.

**Why they are not derived.** Cardinality of an arbitrary path set is not definable in the
first-order signature this tier uses: there is no counting quantifier, and `_nat.p` gives arithmetic
on a `num` sort without any map from sets to it. So the counting facts are stated as axioms or the
operator does not exist in the tier at all.

**Why this entry did not exist until now, which is the part worth recording.** It was assumed in
`_card.p` and absent from this file, while this file's own opening sentence claimed to be the
complete list — so `card_wrap` was reported as an unqualified `PROVED` resting on six undeclared
assumptions. The gap was found by auditing this document against the corpus rather than by any
check, which is why the `% TRUSTED-ENTRY:` marker and its enforcement were added at the same time.

**If they were false**, `card_wrap` (U-series cardinality of a wrap) would lose its premises. Note
that the four counting axioms are the standard ones and `_card.p` separately records which of its
neighbours are *derived* rather than assumed, so the axiom list cannot be accused of containing its
own conclusions.

---

## T8. Induction over the natural-number chain index

MECHANIZED-IN: proofs/lean/Zippy/PathInduction.lean#Zippy.nat_induction

> **DISCHARGED** by `proofs/lean/Zippy/PathInduction.lean#Zippy.nat_induction` — the schema in the
> guarded-`Int` form the SMT files assert, `(=> (and (P 0) (∀ n ≥ 0. P n → P (n+1))) (∀ n ≥ 0. P n))`,
> from `Nat.rec` through the coercion a non-negative `Int` is.

**Files:** `terminating/asfixpoint_sound.smt2` (5), `bounded_recursion_residual.smt2` (1),
`seminaive_correct.smt2` (3), `unroll_vs_kleene.smt2` (1), `proofs/spatial/lat_postfixpoint.smt2`
(1) · **Marker:** `; ASSUMED: T8` above each

**What it is.** The same discipline as T2 — base and step machine-checked in `(push)`/`(pop)` blocks,
then the bridging principle asserted "exactly as a hand proof invokes it" — at predicates other than
T2's four. T2 names the four of `fixpoint_is_lfp.smt2`; these are the rest. Found by
`scripts/check_asserts.py` on 2026-09-04, when they were asserted with no marker and no entry, which
made every one of those rows an unqualified `PROVED` resting on an induction principle first-order
logic cannot state.

**Why it is not derived.** As T2: the chain index is an unguarded `Int` with a `>= n 0` side
condition, not a well-founded type, so the prover has no induction rule to apply.

**If it were false**, the five files' conclusions about their chains would lose their premise. They
would not: `Nat.rec` is a theorem of Lean's kernel and `nat_induction` is its transport.

## Open obligations, which are *not* trusted assumptions

These are gaps, recorded as gaps. A claim that depends on one is not "proved modulo an assumption" —
it is open, and the registries say so.

| row | statement | what stands in for it |
|---|---|---|
| O6a | beta-soundness of capture-avoiding inlining | the semantic half is PROVED (`call_unfold.p`, U63); the syntactic half is the randomized differential `src/test/scala/SubstConformance.scala`, which found three real bugs |
| O10b | *k*-unrolling equivalence for all *k* ⇒ lfp equivalence | **mechanized** (plan.md 2E.1): `proofs/lean/Zippy/Positive.lean` — `Space.fixpoint_is_lfp` (the Kleene union of a positive body is the least post-fixpoint) and `fixpoint_denT_eq_of_step_eq` (one-step agreement for every value of the cut ⇒ the fixpoints agree). What a residual-cut cell still owes is the antecedent for its *own* cut, stated in its header. |
| O12b | the supercompiler fold | **mechanized, parametric** (plan.md 2E.2): `proofs/lean/Zippy/Supercompile.lean#Zippy.Fold.resid_lfp_eq_orig`, under the `FoldPremises` the header maps to executable invariants in `SC.State` (`foldChecks`, `productive`, `residualPositive`); the substitution lemma behind the `fix` premise is O6a's |

`terminating/REGISTRY.tsv` and `proofs/unbounded/REGISTRY.tsv` are the authoritative lists; this
table is the short form for the three the acceptance review names.

---

## The closure, and how it is enforced

An entry in the list above is only useful if a reader can tell **which results depend on it**. A
prover verdict cannot say: it reports `Theorem` under whatever axioms the file included, and it does
not distinguish an assumption from a discharged lemma. So `scripts/proof_closure.py` computes the
transitive `include` closure of every reported status **from the files themselves** — not from a
hand-maintained dependency column, which is the kind of thing that drifts — intersects it with this
list, and reports each status as either `PROVED` or `PROVED-MODULO T…`. With `--check` an
unqualified `PROVED` whose closure reaches a trusted axiom is an **error**.

It found one immediately: **`mon_cancel` was reported as unqualified `PROVED` and its closure
reaches T1.** It is conditional, and `wrap_roundtrip` and `card_wrap` are conditional through it.

That is now recorded in the table rather than only in a report. `--annotate` rewrites a conditional
verdict to `PROVED-MODULO T1`, `proofs/unbounded/run.sh` calls it after every corpus run, and
`--check` holds the table to the closure afterwards — so the prover writes the verdict it reached
and the closure decides whether that verdict is unqualified. The annotation only ever weakens a
verdict, and it is idempotent.

Two limits, stated so the report is not read as complete:

* **T2, T3, T4, T5 and T6 are not reachable through an `include`.** They are properties of a corpus
  or of the implementation, so no closure over axiom files can detect or discharge them; the script
  prints them separately as exactly that.
* **An implementation-correspondence lemma carried by a test is invisible to it.** T4 and T6 are
  both of that kind. A closure over axioms cannot see a claim whose evidence is a differential run.

The script also reports an include that resolves **only from the corpus root**, because TPTP
resolves includes against the prover's working directory rather than the including file — and that
difference is not academic. Three negative controls used a bare `include('_signature.p')` while
`run.sh` runs them with `cd negative`, so vampire could not read them at all, emitted no SZS status,
and the harness scored the non-answer as `NOT-PROVED (expected)` — **a pass for three controls that
pinned nothing, for a whole round.** `run.sh` now treats an unreadable file as a hard failure on
both loops, and fixing the includes is what exposed the invalid N10 recorded under T5 above.
