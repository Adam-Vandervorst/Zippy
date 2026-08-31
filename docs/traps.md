# Lessons

The durable disciplines that would have prevented — or caught for pennies — the recurring failures in [traps.md](traps.md). In a path-set algebra engine almost every wrong answer is *silent*: it type-checks, passes small tests, then surfaces far downstream as a corrupt result, a hang, or a false "proved". The leverage is in making correctness observable up front. Each principle below merges several traps that share one failure mode; every "Grounded in" line names ≥2 concrete traps it generalizes, ordered most-work-saved first.

**How to use (agent):** each `##` heading IS the rule. Scan headings against what you are about to do; the **checklist** under the matching one is the payload — act on each bullet without reading further. `Why:` and `Grounded in:` are there only when you need the rationale or the source trap.

---

## 1. Enumerate the degenerate path-set shapes, and guard on the exact enabling predicate — never a cheaper superset

- Do: For every law, combinator, and transfer function, write the degenerate inputs — `{∅, {ε}, ε-inside-a-literal, single-item source, empty operand}` — as explicit arms *before* the general case, and make the function total on each.
- Do: Gate a hoist on *headedness* via the reusable `headedGuard(x) = Range(x,-1,0).iter(_,_,{ε})`, not `nonEmpty` (`{ε}` is non-empty yet runs zero head-groups).
- Do: Use the `keyedBy` guard for set-op (∩/\) merges.
- Do: Detect known-ε with an actual ground-fold check, never a `[k,k]`-size proxy. (Historical: closed-subterm folding was later removed from every analysis — an abstract interpretation must not consult evaluation output. See docs/design_spatial_lattice.md §0.)
- Never: Confuse ∅ ("no tails") with `{ε}` ("one empty tail") in any arm.
- Never: Assume every path has a head.
- Never: Let an empty operand vanish from a meet.
- Never: Ship a proxy/superset guard without first trying to refute it with a countermodel; if one exists, the proxy is the wrong guard.

Why: reasoning written for the non-degenerate case silently breaks at the edges of set-of-paths semantics, and these shapes rarely appear in hand-written examples, so the bugs stay latent until a real query hits them.

Grounded in: **`IterUnion_Indep` hoist needs HEADEDNESS, not non-emptiness**; **Product-into-union hoist unsound unless the source is provably HEADED**; **`IterateSingleton_Deref` produced the wrong tail-set for a single-item source**; **`IterateLiteral_Union` crashed on the empty path ε inside a literal**; **`IterateLiteral_Union` must group by distinct HEAD, not unroll per path**; **n-ary ∩-chain rewrite would silently drop EMPTY operands from the meet**; **Trie `AlgebraicResult` fast paths: EMPTY must beat `Identity`, and `a\b == b` is never an identity case**; **`IterC` over an ε-only source law was false at p=ε**; **Interval size-analysis sketch had unsound transfer functions**.

## 2. Make a large seeded randomized differential gate the primary soundness net — and assert on semantics, never on serialized structure

- Do: Run a one-command corpus/fuzz runner that generates thousands-to-100k programs.
- Do: Differential every backend against the reference — assert `eval == exec == execT`, assert every size bound contains `|eval|`, and sat-check each law.
- Do: Print the seed on every failure for exact repro.
- Do: Assert on eval-equivalence / cardinality, never on rendered or serialized structure (a byte-for-byte op-graph dump *cements* the bug and hides its fix).
- Do: Give the generator interestingness + responsiveness criteria so it emits expressive programs (a naive generator wastes the gate on ≈74% inert output).
- Do: Port-and-verify any drafted generator code rather than trusting it.

Why: curated tests only pin the shapes you already thought of — the gate surfaces the ones you didn't (seed 49, the 100k-check law gate, the 8k-check guard, and the 1000-program size gate each caught a hole no fixture drove).

Grounded in: **A scope's result must be materialized as its LAST op-graph node**; **`IterateLiteral_Union` must group by distinct HEAD, not unroll per path**; **Path-constant round-trip through the op-graph was lossy (LiteralCodec)**; **A test pinned the old unsound op-graph dump (brittle, hid the fix)**; **The program generator is dominated by degenerate (empty/inert) programs**; **Fuzzer draft Compose/Dep never grew the left operand (returned empty)**.

## 3. Never let a semantics-critical path silently degrade into a no-op or plausible-but-wrong fallback

- Do: Make semantics-critical passes well-formed *by construction* — coordinate-free until linearization, value-numbered, with `wellFormed` assertions — so violations surface.
- Do: Implement backends native-or-crash; never a hidden reference-eval bridge for residuals.
- Do: Give loaders actionable errors ("rerun `morkl.ProgramExpressivity`"), not bare exceptions.
- Do: Require BOTH provers on every obligation and record explicit timeouts — never silently accept the first that passes (z3-first/vampire-fallback hid that vampire can't handle the encoding).
- Do: Add a test asserting the residual actually differs from the original whenever a transform is expected to fire.
- Never: Wrap a pass in a blanket catch/revert net (a `catch => in` around `optimize` hid `push_out` corruption; a one-line Scala `catch case` arm leaked trailing statements into an unconditional fallback).

Why: an error path that quietly substitutes a runnable-but-wrong result disguises a correctness failure as a green build.

Grounded in: **`optimize` must NOT swallow ill-formed graphs or exceptions**; **Scala 3 one-line catch/case arm leaks trailing statements (unconditional fallback)**; **Trie backends silently fell back to reference eval for residuals; `execT` crashed on them**; **Stale `corpus_1000.ser` after a `serialVersionUID` change**; **vampire cannot handle `define-fun-rec`/`match` encodings**.

## 4. Keep hand-written rules 1:1 with the machine-certified algebra, and admit no law until a countermodel search fails to refute it

- Do: Treat `formal.egg` / the egglog + SMT canonical laws as ground truth, and keep each Scala rewrite mechanically 1:1 with the law it implements.
- Do: Add a test that drives each law's canonical shape.
- Do: Screen every candidate/mined law through the sat-check + registry countermodel chain, and keep refuted laws out of the default pipeline.
- Do: Treat the code as wrong whenever it disagrees with its formal twin.
- Do: When a prover refutes an "obvious" theorem, look for the missing well-formedness invariant (e.g. no-duplicate-keys) — a genuine catch, not a tooling artifact.

Why: hand-transcription silently re-introduces subtle errors (reversed factor order, dropped wrapping prefix) and a plausible-looking mined law can simply be false — a certified law set turns "is this rewrite sound?" into a mechanical diff.

Grounded in: **`UnwrapConcat_Unwraps` stripped Concat-prefix factors in reversed order**; **`SingletonRestriction_Unwrap` dropped the restriction prefix (must RE-WRAP)**; **Same-source iteration merges: union gated OFF invariant bodies; ∩/\ require the KEYED guard.**; **`isempty_finite` unconditional theorem refuted by countermodel**; **`IterC` over an ε-only source law was false at p=ε**.

## 5. Canonicalize before you compare, intern, or diff — one value, one representation

- Do: Canonicalize at construction via smart constructors (`Literal(∅)→Empty`; EMPTY takes precedence over Identity).
- Do: Intern on the exact structural key `op|constant|kind|<input VNs>` (constants included) — never a lossy digest/hash.
- Do: Run an `alphaRename`/`alphaNorm` pre-pass (inner-first, scope-discriminating `Extract` keys) before any CSE, hash-cons, encode, or diff.
- Do: Key fixpoint convergence on a 64-bit `structuralHash`, not rendered `.show` strings.
- Never: Use an over-approximate observation (e.g. Keys) as an equational rule — exactness = e-class consistency = soundness.

Why: getting the "are these the same?" key wrong corrupts both directions — too-lossy/scope-blind keys silently *merge* distinct values, missing canonicalization *splits* equal terms, and two spellings of one value stall normalization/absorption.

Grounded in: **CSE value-numbering must use an EXACT structural key, never a lossy hash**; **CSE merged an `Extract` binding with its ancestor (loop var == initial value)**; **z3 size-encoding rejects binder-name reuse (scope limit); hash-consing needs globally unique binders**; **Two representations of the empty space blocked normalization/absorption**; **Over-approximate Keys observation used as an equational rule poisoned the e-graph**; **Diff must alpha-normalize binders or renamings masquerade as real obligations**.

## 6. Give rewrite and fixpoint machinery termination by construction

- Do: Make the firing guards provably disjoint for every inverse-rule pair.
- Do: Fire the adjacent-unwrap merge only CONSTANT→single so the splitter can never re-fire.
- Do: Fire the singleton-wrap merge only when the path is fully constant.
- Do: Fire the singleton-wrap split only on a const-prefix + ≥1 deref factor.
- Do: Require the inline index to be acyclic.
- Do: Lower a cyclic definition to a `Fixpoint` loop instead of inlining it.
- Do: Cap every simplification loop with a step limit that *raises* on non-convergence (comparing a structural hash), never an unbounded `all_forever`.

Why: a rule and its inverse both firing on one term, or a fixpoint with no bound and no acyclicity guarantee, thrashes or hangs with no diagnostic.

Grounded in: **Adjacent-unwrap merge gated to CONSTANT prefixes to avoid ping-pong**; **Singleton wrap merge gated to fully-constant paths (vs the split direction)**; **`reduce`/optimizer convergence used unbounded `all_forever` and fragile `.show`-string equality**; **`inlineCalls` diverges unless the routine index is acyclic**.

## 7. Make every generic term traversal total over the structure and binder-aware

- Do: Audit every rewriter (`subst`, `collect`, `canon`, `diff`, `encode`) for consistent full-subterm recursion, including grounded/opaque closure arguments and all binder bodies.
- Do: Keep substitution capture-avoiding across all three binder forms (`Iteration`/`Fold`/`Fixpoint`) — shadow the binder's names within its body and alpha-rename to a fresh reserved name when a replacement would be captured.
- Do: Reject reserved-prefix free names up front.
- Do: Compare grounded/opaque nodes by closure identity (`f1 eq f2`), recursing only into their args, never their bodies.

Why: a traversal that skips a subterm leaves a dangling `Deref` that only fails at eval, non-hygienic substitution lets a replacement's free name be captured, and inspecting grounded bodies over-collapses distinct functions in the whistle.

Grounded in: **`subs`/`collect` did not recurse into Grounded node arguments**; **Substitution must be capture-avoiding across all three binder forms (+ reserved prefixes)**; **Grounded nodes over-collapsed in the whistle/matching (always-couple)**.

## 8. Layer aggressive precision on a trusted baseline it can only tighten — fall back on any failure, and budget the expensive path

- Do: Assert each node's baseline interval as a lower bound on precision and re-clamp every solver result into it (`lo max base.lo`, `hi min base.hi`, `loHd max base.loHeaded`).
- Do: Return the baseline unchanged on *any* failure (no solver, scope-limited, timeout, exception).
- Do: Gate exact shortcuts behind an explicit budget (closed node, syntactic `hi ≤ 200k`, memoized, `eval` wrapped in try/catch).
- Do: Gate exact shortcuts behind an exactly-verified precondition (binder-aware `freeMentions`/`freeRefs`), never a syntactic proxy.

Why: a solver read-off or exact evaluation is sound only *relative* to the trusted compositional analysis and its precondition; clamp-and-fallback makes the aggressive tier tighter-everywhere / unsound-nowhere by construction.

Grounded in: **z3 size bounds are clamped to the baseline — tighter everywhere, unsound nowhere**; **`groundFold` eps-pin would have been unsound (caught in review)**; **`groundFold` is budgeted so exact evaluation can't blow up compile time**; **Interval size-analysis sketch had unsound transfer functions**.

## 9. A LOWER endpoint may be derived only from MUST facts — and most of this domain's maps are MAY maps

- Do: Before using an abstract quantity as a floor, ask which endpoint it is. `Shape.heads` is a MAY map (a value in γ need only carry the heads whose sub-shape is DEFINITELY non-empty), `Meas.nodes`/`nodesHi` is an UPPER bound, `Layers.maxArity(d)` is a MAX over a level, and `Pairing.pairedAt(d)` counts the whole level.
- Do: Carry BOTH endpoints where a must-count needs one — `Meas.nodesLo` exists because `SpatialFacts.trieNodes` returns an interval and only its upper half was being read.
- Do: State the SIDE CONDITION that turns a level-wide fact into a per-frontier one, and drop the exactness claim when it does not hold (`arityUniform`; "the frontier already holds all `pairedAt(k)` paired prefixes").
- Do: Re-run the counted-event calibration after every floor. A floor that exceeds the run produces an INVERTED interval, which is the unmistakable signature — and the corpus finds it in one pass.
- Don't: Reach for a "surely at least" constant. Three separate must-counts in `SpatialCost` were derived from plausible readings of an abstract map and refuted within one calibration run each; the fourth worked because the quantity was rederived (live DISTINCT operands, not heads) rather than re-guessed.

Why: an upper bound used as a lower endpoint is not conservative in the safe direction — it excludes the real run from the predicted interval, and every consumer downstream then reasons from an interval the program is not in.

Grounded in: **`kLo` scratch/probe must-counts refuted on the first corpus run (heads ≠ live operands)**; **`liveDistinct`'s bare `ArrayBuffer(4)` refuted for the zipper**; **`rebuilt.lo` as a must-rebuild count refuted on eight programs**; **`TailsFacts.distinctLo` counted POSSIBLE children and put datalog-sn's alloc floor at 84 against a counted 67**.

## 10. A fixture whose claim is about representation must PIN the representation

- Do: When a test asserts a cost class that depends on interned-id bit structure ("separated ranges", "power-of-two aligned blocks"), pad the interner to an alignment boundary first. The base id depends on how much of the rest of the suite ran before it.
- Do: Assert the pinned property (`pool(0) % align == 0`), not only the derived one (`consecutive`).
- Do: Suspect the fixture, not the subject, when a measured class OSCILLATES across a geometric ladder (`4,2,2,4,2` where the claim is a flat 2).

Why: a global side table shared by the whole suite makes a "pure" measurement depend on test ORDER, so the test passes or fails according to what was interned first — and the failure looks like a regression in the code under test.

Grounded in: **`OptimalTrieCheck`'s distribution sweep and arity gates broke when the fuzzer gained two operators, purely because the interner base moved**.

---

**Meta-principle:** In an algebra/verification engine a wrong answer is silent by default — so buy observability at authoring time: enumerate the edge shapes, keep every rule diffed against a certified oracle, canonicalize so equality means equality, refuse silent fallbacks, and let a large seeded differential gate surface the shapes you didn't think to enumerate.
