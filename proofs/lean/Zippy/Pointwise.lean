/-
==================================================================================================
THE DENOTATIONAL SEMANTICS OF THE POINTWISE FRAGMENT, AND THE FIRST MECHANIZED THEOREM.

WHY THIS FILE EXISTS.  Two claims in this repository are conditional on a proof principle that
first-order logic cannot state, and every tool in the tree says so:

  * `docs/TRUSTED.md` T1 — structural induction over `path`, instantiated at one predicate.  It is
    asserted as the axiom module `proofs/unbounded/_path_induction.p` because `path` is an opaque TFF
    sort and vampire has no structural-induction rule for it.  `mon_cancel` is proved from it, and
    `_cancel.p` re-asserts `mon_cancel`'s conclusion, so `wrap_roundtrip` and `card_wrap` are
    reported `PROVED-MODULO T1` (scripts/proof_closure.py computes that closure).
  * `docs/TRUSTED.md` T2 — the four bridging induction principles asserted INSIDE
    `terminating/fixpoint_is_lfp.smt2`.

An induction principle over a free term algebra is not something to admit; it is something a
dependently typed proof assistant gives for free from the inductive declaration.  `Syntax.lean` is
that declaration; this file is its semantics and the theorem that makes the point.

==ONE SYNTAX, NOT TWO==
An earlier revision declared its own `Space`/`Path` here, for the CLOSED fragment, so that `denote`
could be environment-free.  Adding `Syntax.lean` for substitution then produced two inductives called
`Zippy.Space` and the package stopped building — `import Zippy.Syntax failed, environment already
contains 'Zippy.Space.unwrap'`.  That was the right failure: two syntaxes for one language is the
duplication this tree keeps having to undo, and a theorem proved about the wrong one of them would
be worthless.  There is now ONE syntax and this file only adds semantics to it.

==`denote` IS PARTIAL, AND IT SAYS WHERE==
`Option`-valued, and `none` at exactly the constructors whose semantics needs machinery a later task
owns.  A total function with a placeholder answer at those constructors would be a silently WRONG
denotation, which is much worse than an honest `none`:

    `fixpoint`   -> `2E.1`: it denotes a LEAST fixpoint, which needs the lattice development and
                    the monotonicity side condition (`terminating/fixpoint_is_lfp.smt2` / T2).
    `iteration`  -> `2E.1`: a group-by over head items, with `rest` bound to each group's tail set.
    `fold`       -> `2E.1`: a path-valued accumulation, and its order-independence is its own
                    obligation.
    `call`       -> `2E.2`: it needs a routine environment, and folding is what that task is about.
    `grounded*`  -> never here.  T6 assumes only that the closure is deterministic, so no definition
                    in this file can say what it computes; a `none` is the honest reading of "outside
                    the certified algebra".
    `range`      -> `1D.2`.  T5 already records that `Range` is OUTSIDE the certified pointwise
                    algebra, so its absence here is the same boundary and not a new one.

Everything else denotes, and the two theorems below are about those.
==================================================================================================
-/
import Zippy.Syntax
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Infix

namespace Zippy

/-- A PATH VALUE is a list of items — `PathValue(items: List[PathItem])` in MORKL.scala. -/
abbrev PathV := List Name

/-- A SPACE VALUE is a set of path values — `SpaceValue(paths: Set[PathValue])`.  `Set` and not
`Finset`: `eval` is `Set[PathValue]`-valued, several certified laws are stated over infinite path
sets (that is the whole point of `proofs/unbounded`), and finiteness is a separate hypothesis that
the `card_*` obligations carry explicitly. -/
abbrev SpaceV := Set PathV

/-- The environment: what the free variables denote.  `PathContext` and `SpaceContext` in
MORKL.scala, which are likewise total maps. -/
structure Env where
  refs : Name → PathV
  spaces : Name → SpaceV

/-! Two-argument lifts, written as explicit pattern matches rather than as `do`-notation.
`do` over `Option` elaborates through `bind` and `pure`, and every proof below then has to name the
right monad simp lemmas for the Lean version in use — the first version of this file failed on
`Unknown constant Option.some_bind`.  A pattern match reduces by `simp [optS2]` and says the same
thing: `none` propagates, which is how a deferred constructor stays deferred through its parents. -/

/-- lift a binary set operation over `Option` -/
def optS2 (f : SpaceV → SpaceV → SpaceV) : Option SpaceV → Option SpaceV → Option SpaceV
  | some a, some b => some (f a b)
  | _, _ => none
/-- lift a (space, path) operation over `Option` -/
def optSP (f : SpaceV → PathV → SpaceV) : Option SpaceV → Option PathV → Option SpaceV
  | some a, some v => some (f a v)
  | _, _ => none
/-- lift a binary path operation over `Option` -/
def optP2 (f : PathV → PathV → PathV) : Option PathV → Option PathV → Option PathV
  | some a, some b => some (f a b)
  | _, _ => none

mutual
  /-- `recp` of MORKL.scala's `eval`.  `none` only at the two grounded forms. -/
  def Path.den (ρ : Env) : Path → Option PathV
    | .deref r => some (ρ.refs r)
    | .const items => some items
    | .concat l r => optP2 (· ++ ·) (l.den ρ) (r.den ρ)
    | .groundedPP _ _ => none
    | .groundedSP _ _ => none
  /-- `recs` of MORKL.scala's `eval`.  Every clause is the same set-theoretic operation the Scala
  evaluator performs, and the same one `proofs/pointwise.smt2` and `proofs/threeway_*.smt2` certify
  the trie and zipper implementations against.  `none` where this file's header says. -/
  def Space.den (ρ : Env) : Space → Option SpaceV
    | .empty => some ∅
    | .lit ps => some {e | e ∈ ps}
    | .mention m => some (ρ.spaces m)
    | .singleton p => (p.den ρ).map (fun v => {v})
    | .union x y => optS2 (· ∪ ·) (x.den ρ) (y.den ρ)
    | .inter x y => optS2 (· ∩ ·) (x.den ρ) (y.den ρ)
    | .sub x y => optS2 (· \ ·) (x.den ρ) (y.den ρ)
    | .restriction x y =>
        optS2 (fun a b => {e ∈ a | ∃ q ∈ b, q <+: e}) (x.den ρ) (y.den ρ)
    -- `x \| y = x \ (x <| y)`, which is how `eval` rewrites it
    | .raffination x y =>
        optS2 (fun a b => a \ {e ∈ a | ∃ q ∈ b, q <+: e}) (x.den ρ) (y.den ρ)
    | .composition x y =>
        optS2 (fun a b => {e | ∃ u ∈ a, ∃ v ∈ b, e = u ++ v}) (x.den ρ) (y.den ρ)
    | .wrap s p => optSP (fun a v => {e | ∃ u ∈ a, e = v ++ u}) (s.den ρ) (p.den ρ)
    | .unwrap s p => optSP (fun a v => {e | v ++ e ∈ a}) (s.den ρ) (p.den ρ)
    | .tailsUnion s => (s.den ρ).map (fun a => {t | ∃ h, h :: t ∈ a})
    | .tailsInter s => (s.den ρ).map (fun a => {t | ∀ h, (∃ t', h :: t' ∈ a) → h :: t ∈ a})
    -- the deferred constructors; see this file's header for which task owns each
    | .range _ _ _ => none
    | .call _ _ _ => none
    | .iteration _ _ _ _ => none
    | .fixpoint _ _ _ => none
    | .fold _ _ _ _ _ _ _ => none
    | .groundedPS _ _ => none
    | .groundedSS _ _ => none
end

/-! ================================================================================================
## THE FIRST MECHANIZED THEOREM, AND WHY IT IS THIS ONE

`wrap_roundtrip` is the obligation whose reported status T1 actually weakens.  Its TPTP form
(`proofs/unbounded/wrap_roundtrip.p`) includes `_cancel.p`, which re-asserts left cancellation of
append; `_cancel.p`'s header names `mon_cancel.p` as its discharge, and `mon_cancel.p` is proved from
the induction SCHEMA `_path_induction.p`.  So the include closure reaches T1 and
`scripts/proof_closure.py` reports `wrap_roundtrip` as `PROVED-MODULO T1` — correctly.

Here there is no schema.  `List` is an inductive type, so left cancellation is a theorem
(`List.append_cancel_left`, itself proved by the recursor Lean derives from the declaration), and the
roundtrip follows without any admitted principle.  That is the whole argument for this directory,
made once, on the smallest statement that carries it.

The marker below is what `scripts/proof_closure.py --annotate` reads: a `MECHANIZED-IN:` line in a
proof file names `<lean file>#<theorem>`, and the status of that row is lifted from
`PROVED-MODULO T1` to unqualified `PROVED` only when `scripts/check_lean.sh` reports that this file
BUILDS and that the named theorem is present and `sorry`-free.  Phase 1's 1E.3 attaches the marker to
the rows the plan names; 0.5 only had to make the marker mean something.

    proofs/lean/Zippy/Pointwise.lean#Zippy.Space.unwrap_wrap
================================================================================================ -/

/-- `Unwrap(Wrap(s, p), p) = s`, for every space, in every environment — PROVIDED `p` denotes.

This is the pointwise half of `proofs/unbounded/wrap_roundtrip.p`.  It needs left cancellation of
`++`, which is T1's content in the TPTP tier and a plain theorem here.

==THE SIDE CONDITION IS NOT AN ARTEFACT, AND THE PARTIAL `den` IS WHAT SURFACED IT==
`p.den ρ = some v` is required, and the first version of this theorem omitted it and did not build:
in the `s.den = some a`, `p.den = none` case the left side is `none` (a `none` operand propagates)
while the right side is `some a`, so the equation is FALSE there.  That case is exactly a `p` that is
a `groundedPP`/`groundedSP` — a term OUTSIDE the certified path algebra, which `docs/TRUSTED.md` T6
covers by assuming only that the closure is deterministic.

The TPTP twin gets this for free by not having grounded paths in its signature at all, so the side
condition is invisible there.  Here it is visible and it is checked, which is the difference between
a law that happens to be stated over a restricted signature and a law that says what it needs. -/
theorem Space.unwrap_wrap (ρ : Env) (s : Space) (p : Path) (v : PathV)
    (hp : p.den ρ = some v) :
    (Space.unwrap (Space.wrap s p) p).den ρ = s.den ρ := by
  cases hs : s.den ρ with
  | none => simp [Space.den, hs, hp, optSP]
  | some a =>
    simp only [Space.den, hs, hp, optSP, Option.some.injEq]
    ext e
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, hEq⟩
      -- `v ++ e = v ++ u`, so `e = u` by left cancellation — the T1 step.
      exact (List.append_cancel_left hEq.symm) ▸ hu
    · intro he
      exact ⟨e, he, rfl⟩

/-- The companion direction, and the reason the roundtrip is stated as an equality of DENOTATIONS
rather than of syntax: `Wrap(Unwrap(s, p), p)` is NOT `s` — it is `s` restricted to the members that
start with `p`.  Stating this explicitly stops the roundtrip above from being read as an inverse
pair, which is exactly the misreading `proofs/wrap1.smt2`'s header warns about. -/
theorem Space.wrap_unwrap (ρ : Env) (s : Space) (p : Path) (a : SpaceV) (v : PathV)
    (hs : s.den ρ = some a) (hp : p.den ρ = some v) :
    (Space.wrap (Space.unwrap s p) p).den ρ = some {e ∈ a | v <+: e} := by
  simp only [Space.den, hs, hp, optSP, Option.some.injEq]
  ext e
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hu, List.prefix_append _ _⟩
  · rintro ⟨he, ⟨t, rfl⟩⟩
    exact ⟨t, he, rfl⟩

end Zippy
