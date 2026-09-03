/-
==================================================================================================
THE MORKL SPACE/PATH ALGEBRA IN LEAN 4, AND ITS DENOTATIONAL SEMANTICS.

WHY THIS FILE EXISTS.  Two claims in this repository are conditional on a proof principle that
first-order logic cannot state, and every tool in the tree says so:

  * `docs/TRUSTED.md` T1 -- structural induction over `path`, instantiated at one predicate.  It is
    asserted as the axiom module `proofs/unbounded/_path_induction.p` because `path` is an opaque TFF
    sort and vampire has no structural-induction rule for it.  `mon_cancel` is proved from it, and
    `_cancel.p` re-asserts `mon_cancel`'s conclusion, so `wrap_roundtrip` and `card_wrap` are
    reported `PROVED-MODULO T1` (scripts/proof_closure.py computes that closure).
  * `docs/TRUSTED.md` T2 -- the four bridging induction principles asserted INSIDE
    `terminating/fixpoint_is_lfp.smt2`.

An induction principle over a free term algebra is not something to admit; it is something a
dependently typed proof assistant gives for free from the inductive declaration.  So the inductives
below are the definition, `denote` is the semantics, and a theorem here is checked by Lean's kernel
with no schema to trust.  Phase 1's `1E.*` and Phase 2's `2E.*` (plan.md) add the substitution
theorems, the positivity/continuity development and the whistle's well-quasi-order on top.

==WHAT IS AND IS NOT MODELLED HERE (0.5 is a scaffold, and says which parts are missing)==

MODELLED: the FIRST-ORDER POINTWISE FRAGMENT -- exactly the operators `proofs/*.smt2` certifies
against the set-of-paths denotation, with `Path` reduced to its two closed constructors.

DEFERRED, each to the task that needs it, so nothing here quietly pretends to be total:
  * `Space.Call` / `Space.Mention` and the routine environment  -> 1E.1 (it is what substitution acts
    on) and 2E.2 (folding).
  * `Space.Fixpoint` / `Iteration` / `Fold`                     -> 2E.1 (monotonicity and
    omega-continuity per constructor) and 2E.2.
  * `Space.Range`                                               -> 1D.2; `docs/TRUSTED.md` T5 already
    records that `Range` is OUTSIDE the certified pointwise algebra, so its absence here is the same
    boundary and not a new one.
  * `Path.Deref` and the two `Grounded*` families               -> 1E.1 (Deref is a variable, so it
    arrives with substitution) and T6 (grounded functions are deterministic -- an assumption about
    Scala closures that no Lean definition can discharge).

`Item` is left OPAQUE.  `PathItem` in MORKL.scala is a string-like atom with no structure the algebra
uses: every operator below compares items for equality and nothing else.  Keeping it a variable makes
that explicit and makes every theorem here uniform in it.
==================================================================================================
-/

-- The two Mathlib modules this fragment actually needs, named rather than `import Mathlib`: the
-- root import pulls ~5000 modules and would make `lake build` (and therefore `sbt check`) pay for
-- all of them on every elaboration change.  `Set.Basic` gives the set algebra and the `{a}` /
-- `{x ∈ s | p x}` notations; `List.Infix` gives `<+:` and `List.prefix_append`.  Left cancellation
-- of `++` (`List.append_cancel_left`) is Lean CORE -- which is the point of this file.
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Infix

namespace Zippy

-- A path ITEM.  Opaque on purpose: the algebra only ever compares two of them, so every theorem
-- below is uniform in it.
variable {Item : Type}

/-- A path VALUE is a list of items -- `PathValue(items: List[PathItem])` in MORKL.scala. -/
abbrev PathV (Item : Type) := List Item

/-- A SPACE VALUE is a set of path values -- `SpaceValue(paths: Set[PathValue])`.  `Set` and not
`Finset`: `eval` is `Set[PathValue]`-valued, several certified laws are stated over infinite path
sets (that is the whole point of `proofs/unbounded`), and finiteness is a separate hypothesis that
`card_*` obligations carry explicitly. -/
abbrev SpaceV (Item : Type) := Set (PathV Item)

/-- The PATH syntax, closed fragment.  `Deref` and the grounded families are deferred; see the
header. -/
inductive Path (Item : Type) where
  /-- `Path.Constant(pi)` -/
  | const (items : PathV Item)
  /-- `Path.Concat(l, r)` -/
  | concat (l r : Path Item)

/-- The SPACE syntax, first-order pointwise fragment.  Binders and recursion are deferred; see the
header for which task adds each. -/
inductive Space (Item : Type) where
  /-- `Space.Empty` -/
  | empty
  /-- `Space.Literal(p)` -/
  | lit (s : SpaceV Item)
  /-- `Space.Singleton(p)` -/
  | singleton (p : Path Item)
  /-- `Space.Union(x, y)` -/
  | union (x y : Space Item)
  /-- `Space.Intersection(x, y)` -/
  | inter (x y : Space Item)
  /-- `Space.Subtraction(x, y)` -/
  | sub (x y : Space Item)
  /-- `Space.Restriction(x, y)` -- keep the members of `x` extending some member of `y` -/
  | restriction (x y : Space Item)
  /-- `Space.Composition(x, y)` -- pointwise append -/
  | composition (x y : Space Item)
  /-- `Space.Wrap(src, p)` -/
  | wrap (src : Space Item) (p : Path Item)
  /-- `Space.Unwrap(src, p)` -/
  | unwrap (src : Space Item) (p : Path Item)
  /-- `Space.TailsUnion(src)` -/
  | tailsUnion (src : Space Item)

/-- `recp` of MORKL.scala's `eval`: a closed path denotes one path value. -/
def Path.denote : Path Item → PathV Item
  | .const items => items
  | .concat l r  => l.denote ++ r.denote

/-- `recs` of MORKL.scala's `eval`, restricted to the fragment above.  Every clause is the same
set-theoretic operation the Scala evaluator performs, and the same one `proofs/pointwise.smt2` and
`proofs/threeway_*.smt2` certify the trie and zipper implementations against. -/
def Space.denote : Space Item → SpaceV Item
  | .empty            => ∅
  | .lit s            => s
  | .singleton p      => {p.denote}
  | .union x y        => x.denote ∪ y.denote
  | .inter x y        => x.denote ∩ y.denote
  | .sub x y          => x.denote \ y.denote
  | .restriction x y  => {e ∈ x.denote | ∃ q ∈ y.denote, q <+: e}
  | .composition x y  => {e | ∃ a ∈ x.denote, ∃ b ∈ y.denote, e = a ++ b}
  | .wrap src p       => {e | ∃ a ∈ src.denote, e = p.denote ++ a}
  | .unwrap src p     => {e | p.denote ++ e ∈ src.denote}
  | .tailsUnion src   => {t | ∃ h, h :: t ∈ src.denote}

/-! ================================================================================================
## THE FIRST MECHANIZED THEOREM, AND WHY IT IS THIS ONE

`wrap_roundtrip` is the obligation whose reported status T1 actually weakens.  Its TPTP form
(`proofs/unbounded/wrap_roundtrip.p`) includes `_cancel.p`, which re-asserts left cancellation of
append; `_cancel.p`'s header names `mon_cancel.p` as its discharge, and `mon_cancel.p` is proved from
the induction SCHEMA `_path_induction.p`.  So the include closure reaches T1 and
`scripts/proof_closure.py` reports `wrap_roundtrip` as `PROVED-MODULO T1` -- correctly.

Here there is no schema.  `List` is an inductive type, so left cancellation is a theorem
(`List.append_cancel_left`, itself proved by the recursor Lean derives from the declaration), and the
roundtrip follows without any admitted principle.  That is the whole argument for this file
existing, made once, on the smallest statement that carries it.

The marker below is what `scripts/proof_closure.py --annotate` reads: a `% MECHANIZED-IN:` line in a
proof file names `<lean file>#<theorem>`, and the status of that row is lifted from
`PROVED-MODULO T1` to unqualified `PROVED` only when `scripts/check_lean.sh` reports that this file
BUILDS and that the named theorem is present.  Phase 1's 1E.3 attaches the marker to the four rows
the plan names; 0.5 only has to make the marker mean something.

    % MECHANIZED-IN: proofs/lean/Zippy/Core.lean#Zippy.Space.unwrap_wrap
================================================================================================ -/

/-- `Unwrap(Wrap(s, p), p) = s`, for every space and every closed path.

This is the pointwise half of `proofs/unbounded/wrap_roundtrip.p`.  It needs left cancellation of
`++`, which is T1's content in the TPTP tier and a plain theorem here. -/
theorem Space.unwrap_wrap (s : Space Item) (p : Path Item) :
    (Space.unwrap (Space.wrap s p) p).denote = s.denote := by
  ext e
  simp only [Space.denote, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, hEq⟩
    -- `p.denote ++ e = p.denote ++ a`, so `e = a` by left cancellation -- the T1 step.
    exact (List.append_cancel_left hEq.symm) ▸ ha
  · intro he
    exact ⟨e, he, rfl⟩

/-- The companion direction, and the reason the roundtrip is stated as an equality of DENOTATIONS
rather than of syntax: `Wrap(Unwrap(s, p), p)` is NOT `s` -- it is `s` restricted to the members that
start with `p`.  Stating this explicitly stops the roundtrip above from being read as an inverse
pair, which is exactly the misreading `proofs/wrap1.smt2`'s header warns about. -/
theorem Space.wrap_unwrap (s : Space Item) (p : Path Item) :
    (Space.wrap (Space.unwrap s p) p).denote = {e ∈ s.denote | p.denote <+: e} := by
  ext e
  simp only [Space.denote, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, List.prefix_append _ _⟩
  · rintro ⟨he, ⟨t, rfl⟩⟩
    exact ⟨t, he, rfl⟩

end Zippy
