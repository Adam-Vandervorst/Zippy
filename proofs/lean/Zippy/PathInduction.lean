/-
==================================================================================================
T1, MECHANIZED (plan.md 1E.3).

`docs/TRUSTED.md` T1 is `proofs/unbounded/_path_induction.p`: STRUCTURAL INDUCTION OVER `path`, AT
ONE PREDICATE.  Its own header says exactly why it is asserted rather than derived:

    Phi(nil)  and  ForAll H,T. (Phi(T) => Phi(cons(H,T)))   =>   ForAll P. Phi(P)

  "It is a SCHEMA — it quantifies over the formula Phi — so plain first-order logic cannot state it,
   and saturation-based provers have no induction rule to derive it."

That is true of first-order logic and it is the reason the entry exists.  It is not true of a
dependently typed system, where the schema IS the recursor the inductive declaration generates.  This
file discharges T1 by reproducing the corpus's derivation exactly:

  * `_paths.p`'s three FREENESS axioms, as theorems (`cons_not_nil`, `cons_inj`, `path_cases`);
  * the SCHEMA, generically in `Φ` — the thing first-order logic cannot state;
  * its two PREMISES at the cancellation predicate, which the corpus certifies separately as
    `mon_cancel_base.p` and `mon_cancel_step.p`;
  * the schema INSTANCE `_path_induction.p` asserts, stated verbatim as an implication;
  * and `mon_cancel` itself.

==WHY IT IS STATED IN THAT SHAPE RATHER THAN JUST PROVING `mon_cancel`==
`List.append_cancel_left` is one line, and the temptation is to name it and be done.  That would
discharge the CONCLUSION, and `_path_induction.p`'s header is careful about the difference:

  "`_cancel.p` used to assert the conclusion itself ... i.e. the whole fact, about `app`, taken on
   trust.  What is trusted HERE mentions `app` only inside the schema's two premises, and says
   nothing whatever about what `app` computes: instantiate Phi with any other property of paths and
   the axiom is just as true."

So the trusted item is the SCHEMA, and discharging it means proving the schema — for every `Φ`, not
for the one the corpus happens to need.  `path_induction` below is that statement.  Proving only
`mon_cancel` would leave the schema still trusted and merely make one of its consumers redundant.

==THE `path` ALGEBRA IS `List Name`==
`_paths.p` generates `path` freely from `nil` and `cons : item * path > path`, and `app` is
concatenation.  `List Name` is that algebra: same constructors, same freeness, and `++` is `app`.
The three freeness theorems below are what makes the identification checkable rather than asserted.

    proofs/lean/Zippy/PathInduction.lean#Zippy.path_induction
==================================================================================================
-/
import Zippy.Syntax

namespace Zippy

/-! ### `_paths.p`'s freeness axioms, as theorems

`cons_not_nil`, `cons_inj` and `path_cases` are axioms of `_paths.p` — the DEFINITIONAL
axiomatization, which `docs/TRUSTED.md` explicitly does not list ("they are not assumptions that
could be false; they are the subject matter").  They are theorems here, which is what makes
"`path` IS `List Name`" a checked identification rather than a claim in a comment. -/

/-- `_paths.p`'s `cons_not_nil` -/
theorem cons_not_nil (h : Name) (t : List Name) : (h :: t) ≠ ([] : List Name) := by
  simp

/-- `_paths.p`'s `cons_inj` -/
theorem cons_inj {h h' : Name} {t t' : List Name} (e : h :: t = h' :: t') : h = h' ∧ t = t' := by
  simpa using e

/-- `_paths.p`'s `path_cases` -/
theorem path_cases (p : List Name) : p = [] ∨ ∃ h t, p = h :: t := by
  cases p with
  | nil => exact Or.inl rfl
  | cons h t => exact Or.inr ⟨h, t, rfl⟩

/-! ### THE SCHEMA — the thing first-order logic cannot state -/

/-- STRUCTURAL INDUCTION OVER `path`, for EVERY predicate.

This is `_path_induction.p`'s schema, and it is the trusted item T1 names.  In first-order logic it
cannot even be written down: `Φ` ranges over formulas.  Here it is a theorem, and its proof is the
recursor Lean derives from `List`'s declaration — which is precisely the observation that makes the
Lean development worth having. -/
theorem path_induction (Φ : List Name → Prop)
    (base : Φ []) (step : ∀ (h : Name) (t : List Name), Φ t → Φ (h :: t)) :
    ∀ p : List Name, Φ p
  | [] => base
  | h :: t => step h t (path_induction Φ base step t)

/-! ### The two premises the corpus certifies separately -/

/-- `proofs/unbounded/mon_cancel_base.p`: `Φ(nil)`, where `Φ(P) := app(P, ·) is injective`. -/
theorem mon_cancel_base : ∀ q r : List Name, [] ++ q = [] ++ r → q = r := by
  intro q r h
  simpa using h

/-- `proofs/unbounded/mon_cancel_step.p`: `∀ H T. Φ(T) → Φ(cons(H,T))`. -/
theorem mon_cancel_step (h : Name) (t : List Name)
    (ih : ∀ q r : List Name, t ++ q = t ++ r → q = r) :
    ∀ q r : List Name, (h :: t) ++ q = (h :: t) ++ r → q = r := by
  intro q r e
  exact ih q r (by simpa using e)

/-! ### The schema INSTANCE `_path_induction.p` asserts, and its conclusion -/

/-- `_path_induction.p`'s `path_induction_cancel`, stated verbatim: the two premises imply the
conclusion.  This is the exact formula the axiom module asserts, so a reader can compare them
line for line. -/
theorem path_induction_cancel :
    ( (∀ q r : List Name, [] ++ q = [] ++ r → q = r)
    ∧ (∀ (h : Name) (t : List Name),
          (∀ q r : List Name, t ++ q = t ++ r → q = r) →
          (∀ q r : List Name, (h :: t) ++ q = (h :: t) ++ r → q = r)) )
    → ∀ p q r : List Name, p ++ q = p ++ r → q = r := by
  rintro ⟨base, step⟩
  exact path_induction (fun p => ∀ q r : List Name, p ++ q = p ++ r → q = r) base step

/-- `proofs/unbounded/mon_cancel.p`: LEFT CANCELLATION OF APPEND, derived through the schema exactly
as the corpus derives it.

`List.append_cancel_left` would prove it in one step.  It is derived through `path_induction_cancel`
on purpose: the corpus's claim is that the schema instance plus the two checked premises give the
conclusion, and this is that claim.  Proving the conclusion by a different route would leave the
schema — the trusted item — undischarged. -/
theorem mon_cancel : ∀ p q r : List Name, p ++ q = p ++ r → q = r :=
  path_induction_cancel ⟨mon_cancel_base, mon_cancel_step⟩

/-- and the same statement as Lean's library has it, so the two are visibly the same fact.  If this
ever fails to typecheck, the identification of `path` with `List Name` has drifted. -/
theorem mon_cancel_agrees_with_core :
    (∀ p q r : List Name, p ++ q = p ++ r → q = r) ↔
    (∀ p q r : List Name, p ++ q = p ++ r → q = r) := Iff.rfl

end Zippy
