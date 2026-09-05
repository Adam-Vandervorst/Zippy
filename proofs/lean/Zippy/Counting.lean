/-
==================================================================================================
T7: A MODEL OF THE COUNTING AXIOMS — WHICH IS NOT THE SAME AS DISCHARGING THEM, AND SAYING SO IS
THE POINT.

`docs/TRUSTED.md` T7 is `proofs/unbounded/_card.p`: four counting axioms plus an injective-image
axiom and one comprehension.  `1E.3`'s gate asks for `mon_cancel`, `wrap_roundtrip`, `card_wrap` and
`fixpoint_is_lfp` to be reported UNQUALIFIED.  Three of the four are, now that T1 and T2 are
mechanized.  `card_wrap` is not, and it cannot be by the same route:

==WHY T7 IS NOT LIKE T1 AND T2==
T1 and T2 are INDUCTION PRINCIPLES over free algebras.  First-order logic cannot state them (T1
quantifies over formulas) or cannot derive them (T2's chain index is an unguarded `Int`), and a
dependently typed system gets both from the inductive declaration.  Discharging them meant proving
the schema — no choice of model, no narrowing.

T7 is an AXIOMATISATION OF AN UNINTERPRETED FUNCTION.  `_card.p` leaves `card : space > num` with no
definition and asserts the four facts the corpus uses, and its header is explicit that this is
deliberate and that the generalisation is load-bearing:

  "nothing here forces `card` to be the cardinality of a FINITE set.  A model in which every
   infinite space is given the same 'size' satisfies all of these axioms.  Every theorem below is
   therefore a fact about ANY measure with these properties — which is exactly the class of facts
   tier-1 (`Lower.sizeBounds`) and tier-2 (`SizeZ3`) implement, so the generalisation is faithful."

There is nothing to DERIVE.  Proving the axioms would mean picking a `card` — and picking one makes
every theorem above a statement about that choice instead of about any measure, which is strictly
WEAKER than what the corpus proves.  `card_wrap`'s honest status is therefore

    PROVED-MODULO T7 (MECHANIZED …#Zippy.path_induction discharges T1)

and `scripts/proof_closure.py` now reports exactly that: T1 gone, T7 remaining.

==WHAT THIS FILE DOES DELIVER, AND WHY IT IS WORTH HAVING==
A MODEL.  Finite sets of paths, with `card := Finset.card`, satisfy every one of T7's six items —
including the injective-image axiom and the comprehension, and including `card_wrap` itself.  That
proves the axiom set is CONSISTENT, i.e. the conditional `PROVED-MODULO T7` is NON-VACUOUS.

That is not a formality here.  `_nat.p`'s header records the measured reason `card` lands in an
uninterpreted `num` rather than `$int`: "vampire 5.1.0 refutes `_signature.p + _card.p` outright when
`card` is `$int`-valued, using only its own internally introduced theory axioms, and an inconsistent
axiom set proves every conjecture."  `proofs/unbounded/run.sh`'s vacuity probe is the guard against
that, and it is a NEGATIVE check: it reports that the prover failed to derive `$false` in 10 seconds.
A model is the positive statement, and it does not expire with a budget.

==WHAT WOULD ACTUALLY MAKE `card_wrap` UNQUALIFIED, stated so the gap is a decision and not a gap==
Reclassifying T7 from ASSUMED to DEFINITIONAL.  `docs/TRUSTED.md`'s own taxonomy already draws that
line — "Definitional axiomatization — the clauses that say what the objects are … These are not
assumptions that could be false; they are the subject matter" — and `_card.p`'s four counting axioms
have a fair claim to it: they say what `card` IS, in the same way `_paths.p`'s freeness axioms say
what `path` is, and `_paths.p` is NOT a T entry.  Whether they cross that line is a judgement about
the trusted base's taxonomy rather than a proof obligation, so this file does not make it: it
supplies the consistency evidence such a decision would want and leaves the decision where it
belongs.
==================================================================================================
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Image
import Zippy.Syntax

namespace Zippy.Counting

open Finset

/-- A FINITE space: a finite set of path values.  `_card.p`'s `space`, in the model. -/
abbrev FSpace := Finset (List Name)

/-- the model's `card` -/
def card (A : FSpace) : Nat := A.card

/-! ### The four counting axioms of `_card.p`, as theorems ABOUT THIS MODEL -/

/-- `card_empty : card(empty) = zero` -/
theorem card_empty : card (∅ : FSpace) = 0 := by simp [card]

/-- `card_sing : ! [P] : card(sing(P)) = one` -/
theorem card_sing (p : List Name) : card ({p} : FSpace) = 1 := by simp [card]

/-- `card_mono : sub(A,B) => le(card(A), card(B))` -/
theorem card_mono (A B : FSpace) (h : A ⊆ B) : card A ≤ card B :=
  Finset.card_le_card h

/-- `card_disj_add : disj(A,B) => card(cup(A,B)) = plus(card(A), card(B))` -/
theorem card_disj_add (A B : FSpace) (h : Disjoint A B) :
    card (A ∪ B) = card A + card B := by
  simpa [card] using Finset.card_union_of_disjoint h

/-! ### The injective-image axiom, and the comprehension

`_card.p`'s note on why these two are of a different character: "`card_image` — an INJECTIVE image
has the same cardinality.  This is the one counting principle that is not about the inclusion
lattice, and it is unavoidable: `|Wrap p A| = |A|` holds because `q |-> p++q` is injective, and no
amount of monotonicity/additivity implies that.  FOL cannot quantify over functions, so path maps are
REIFIED into the sort `pmap` … `pfxmap` is the comprehension axiom asserting that the particular map
`q |-> W++q` exists as an object of that sort."

In Lean there is no reification and no comprehension: a function IS an object, so `pfxmap` is a
definition and `card_image` is `Finset.card_image_of_injOn`.  That is the same observation as T1's —
the axiom exists to work around a limitation of the logic, not to assume a fact. -/

/-- `card_image`: an injective image has the same cardinality. -/
theorem card_image (A : FSpace) (f : List Name → List Name) (hinj : Set.InjOn f A) :
    card (A.image f) = card A := by
  simpa [card] using Finset.card_image_of_injOn hinj

/-- `pfxmap W` — the map `q ↦ W ++ q`.  `_card.p` needs a comprehension axiom to assert this map
EXISTS as an object of the reified sort `pmap`; here it is a definition. -/
def pfxmap (W : List Name) : List Name → List Name := fun q => W ++ q

/-- and it is INJECTIVE — which `card_wrap.p` has to prove from `_cancel.p`, i.e. from T1.  Here it
is `List.append_cancel_left`, the same theorem `PathInduction.lean` derives through the schema. -/
theorem pfxmap_injective (W : List Name) : Function.Injective (pfxmap W) := by
  intro a b h
  have h' : W ++ a = W ++ b := h
  exact List.append_cancel_left h'

/-- `wrap(A, W)` in the model: prefix every member with `W`. -/
def wrap (A : FSpace) (W : List Name) : FSpace := A.image (pfxmap W)

/-! ### And `card_wrap` itself, in the model -/

/-- `card_wrap.p`'s conjecture, `|wrap(A,W)| = |A|`, holds in this model.

`card_wrap.p` derives it from T7's `card_image` plus injectivity of `pfxmap W` (which needs
`_cancel.p`, i.e. T1) plus `wrap_def`.  This is the same derivation, with the T1 step being the
Lean theorem `PathInduction.lean` proves through the schema and the T7 step being `card_image`
above — so the model exercises exactly the two entries `card_wrap`'s closure reaches. -/
theorem card_wrap (A : FSpace) (W : List Name) : card (wrap A W) = card A :=
  card_image A (pfxmap W) ((pfxmap_injective W).injOn)

/-! ### The derived facts `_card.p` lists as "DERIVED, NOT ASSUMED"

`_card.p` is careful to say which of the counting results are conjectures elsewhere in the corpus,
"so the axiom list above cannot be accused of containing its own conclusions".  Two of them are
checked here in the model as well, which is a check on the MODEL rather than on the corpus: a model
in which a derived theorem failed would mean the model does not satisfy the axioms after all. -/

/-- `card_subadd.p`'s subadditivity: `|A u B| =< |A| + |B|`. -/
theorem card_subadd (A B : FSpace) : card (A ∪ B) ≤ card A + card B := by
  simpa [card] using Finset.card_union_le A B

/-- `card_meet.p`: `|A n B| =< |A|` and `=< |B|`. -/
theorem card_meet (A B : FSpace) : card (A ∩ B) ≤ card A ∧ card (A ∩ B) ≤ card B :=
  ⟨Finset.card_le_card Finset.inter_subset_left,
   Finset.card_le_card Finset.inter_subset_right⟩

/-- `card_incl_excl.p`: `|A u B| + |A n B| = |A| + |B|`. -/
theorem card_incl_excl (A B : FSpace) :
    card (A ∪ B) + card (A ∩ B) = card A + card B := by
  simpa [card] using Finset.card_union_add_card_inter A B

/-- THE CONSISTENCY STATEMENT, as one proposition: every item of T7 holds of `Finset.card`.

This is what the file is for.  `proofs/unbounded/run.sh`'s vacuity probe reports that vampire failed
to derive `$false` from the axiom set in 10 seconds, which is a negative check with a budget; this
is the positive one and it does not expire. -/
theorem T7_has_a_model :
    (card (∅ : FSpace) = 0)
    ∧ (∀ p, card ({p} : FSpace) = 1)
    ∧ (∀ A B : FSpace, A ⊆ B → card A ≤ card B)
    ∧ (∀ A B : FSpace, Disjoint A B → card (A ∪ B) = card A + card B)
    ∧ (∀ (A : FSpace) (f : List Name → List Name), Set.InjOn f A → card (A.image f) = card A)
    ∧ (∀ W, Function.Injective (pfxmap W)) :=
  ⟨card_empty, card_sing, card_mono, card_disj_add, card_image, pfxmap_injective⟩

end Zippy.Counting
