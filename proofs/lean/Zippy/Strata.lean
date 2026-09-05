/-
==================================================================================================
SIMULTANEOUS LEAST-POST-FIXPOINT SYSTEMS, STRATA, AND THE UNARY CASE (tasks.md A2).

`DeltaIR.scala` represents every positive SCC as a SIMULTANEOUS system `X_i = init_i ∪ F_i(X̄; L)`
over a finite index set, with the values `L` of lower strata FROZEN.  This module is the semantics
that makes those three words mean something:

  `Sim.tagged_lfp`            the system has a least post-fixpoint above its init, and it is the union
                              of the Kleene chain — obtained by the TAGGED-UNION encoding
                              (`tag : (ι → Set α) ≃ Set (ι × α)`, the encoding `lowerMutualPassthrough`
                              uses, O4) and `Positive.lean`'s `Kleene.iUnion_chain_is_lfp`;
  `Sim.lfp_le_of_post`        it is componentwise least: below every valuation that is a post-fixpoint
                              above init (the "componentwise least solution" of O4's Bekić row);
  `Sim.unary_eq`              a one-equation system's solution IS `Space.fixpoint`'s denotation — the
                              chain of `fixOp init body` — so unary `Fixpoint` is the one-equation case
                              of the IR and nothing is lost either way;
  `Sim.stratum_frozen_sound`  a stratum's operator needs monotonicity in ITS OWN variables only: for
                              every frozen valuation of the lower strata, whatever the variance in them,
                              the least post-fixpoint exists and is characterised as above.  This is
                              why a `-` or `0` edge is admitted when it points to a lower stratum and
                              rejected inside an SCC (`DepGraph`, `Scc.certified`).

    proofs/lean/Zippy/Strata.lean#Zippy.Sim.tagged_lfp
    proofs/lean/Zippy/Strata.lean#Zippy.Sim.unary_eq
    proofs/lean/Zippy/Strata.lean#Zippy.Sim.stratum_frozen_sound
==================================================================================================
-/
import Zippy.Positive

namespace Zippy.Sim

variable {ι α : Type*}

/-! ### The tagged-union encoding -/

/-- a family of sets as one set of tagged elements -/
def tag (V : ι → Set α) : Set (ι × α) := {p | p.2 ∈ V p.1}
/-- and back -/
def untag (S : Set (ι × α)) : ι → Set α := fun i => {a | (i, a) ∈ S}

@[simp] theorem mem_tag (V : ι → Set α) (p : ι × α) : p ∈ tag V ↔ p.2 ∈ V p.1 := Iff.rfl
@[simp] theorem mem_untag (S : Set (ι × α)) (i : ι) (a : α) : a ∈ untag S i ↔ (i, a) ∈ S := Iff.rfl

theorem untag_tag (V : ι → Set α) : untag (tag V) = V := by
  funext i; ext a; simp [untag, tag]
theorem tag_untag (S : Set (ι × α)) : tag (untag S) = S := by
  ext ⟨i, a⟩; simp [untag, tag]

theorem tag_mono {V W : ι → Set α} (h : ∀ i, V i ⊆ W i) : tag V ⊆ tag W :=
  fun p hp => h p.1 hp
theorem untag_mono {S T : Set (ι × α)} (h : S ⊆ T) : ∀ i, untag S i ⊆ untag T i :=
  fun _ _ ha => h ha

theorem untag_iUnion (A : ℕ → Set (ι × α)) (i : ι) : untag (⋃ k, A k) i = ⋃ k, untag (A k) i := by
  ext a; simp [untag]
theorem tag_iUnion (V : ℕ → ι → Set α) : tag (fun i => ⋃ k, V k i) = ⋃ k, tag (V k) := by
  ext ⟨i, a⟩; simp [tag]
theorem tag_union (V W : ι → Set α) : tag (fun i => V i ∪ W i) = tag V ∪ tag W := by
  ext ⟨i, a⟩; simp [tag]

/-! ### A simultaneous system -/

/-- `X_i = init i ∪ step V i`: `step` reads the WHOLE valuation, `init` seeds every component -/
structure Sys (ι α : Type*) where
  init : ι → Set α
  step : (ι → Set α) → ι → Set α

namespace Sys

variable (s : Sys ι α)

/-- the inflationary operator the executors iterate, componentwise (`X ↦ init ∪ F X`) -/
def op : (ι → Set α) → (ι → Set α) := fun V i => s.init i ∪ s.step V i
/-- the same operator on the tagged set -/
def tagged : Set (ι × α) → Set (ι × α) := fun S => tag (s.op (untag S))
/-- THE SOLUTION: the union of the Kleene chain of the tagged operator, read back componentwise -/
def lfp : ι → Set α := untag (⋃ n, Kleene.chain s.tagged (tag s.init) n)

/-- monotone in the system's own variables -/
def Mono : Prop := ∀ V W : ι → Set α, (∀ i, V i ⊆ W i) → ∀ i, s.step V i ⊆ s.step W i
/-- omega-continuous in them, componentwise over a pointwise-ascending chain of valuations -/
def Cont : Prop := ∀ A : ℕ → (ι → Set α), (∀ k i, A k i ⊆ A (k + 1) i) →
  ∀ i, s.step (fun j => ⋃ k, A k j) i = ⋃ k, s.step (A k) i

theorem op_mono (hm : s.Mono) : ∀ V W : ι → Set α, (∀ i, V i ⊆ W i) → ∀ i, s.op V i ⊆ s.op W i :=
  fun V W h i => Set.union_subset_union subset_rfl (hm V W h i)

theorem tagged_mono (hm : s.Mono) : ∀ S T : Set (ι × α), S ⊆ T → s.tagged S ⊆ s.tagged T :=
  fun _ _ h => tag_mono (s.op_mono hm _ _ (untag_mono h))

theorem tagged_infl : tag s.init ⊆ s.tagged (tag s.init) := by
  intro p hp
  simp only [tagged, mem_tag, op, untag_tag]
  exact Or.inl hp

/-- a pointwise-ascending chain of valuations, from an ascending chain of tagged sets -/
theorem untag_chain_ascends {A : ℕ → Set (ι × α)} (h : Monotone A) :
    ∀ k i, untag (A k) i ⊆ untag (A (k + 1)) i :=
  fun k i => untag_mono (h (Nat.le_succ k)) i

theorem tagged_cont (_hm : s.Mono) (hc : s.Cont) : OmegaCont s.tagged := by
  intro A hA
  simp only [tagged]
  have hu : untag (⋃ k, A k) = fun j => ⋃ k, untag (A k) j := by
    funext j; exact untag_iUnion A j
  rw [hu]
  have hasc : ∀ k i, untag (A k) i ⊆ untag (A (k + 1)) i := untag_chain_ascends hA
  -- `op` over the union of the chain is the union of `op` over the chain, componentwise
  have hop : ∀ i, s.op (fun j => ⋃ k, untag (A k) j) i = ⋃ k, s.op (untag (A k)) i := by
    intro i
    simp only [op, hc _ hasc i]
    ext a
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (h | ⟨k, hk⟩)
      · exact ⟨0, Or.inl h⟩
      · exact ⟨k, Or.inr hk⟩
    · rintro ⟨k, h | hk⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, hk⟩
  have : s.op (fun j => ⋃ k, untag (A k) j) = fun i => ⋃ k, s.op (untag (A k)) i := funext hop
  rw [this, tag_iUnion]

/-- **THE SIMULTANEOUS LEAST POST-FIXPOINT.**  Under monotonicity and continuity in the system's own
variables: the solution is a fixpoint of the inflationary operator, contains `init`, and is below
every post-fixpoint above `init` — componentwise. -/
theorem tagged_lfp (hm : s.Mono) (hc : s.Cont) :
    (∀ i, s.op s.lfp i = s.lfp i)
    ∧ (∀ i, s.init i ⊆ s.lfp i)
    ∧ (∀ W : ι → Set α, (∀ i, s.init i ⊆ W i) → (∀ i, s.op W i ⊆ W i) → ∀ i, s.lfp i ⊆ W i) := by
  have h := Kleene.iUnion_chain_is_lfp s.tagged (tag s.init) (s.tagged_mono hm) (s.tagged_cont hm hc)
    s.tagged_infl
  obtain ⟨hfix, hinit, hleast⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i
    -- `tagged L = L` with `L = tag lfp` gives `op lfp = lfp` after untagging
    have : untag (s.tagged (⋃ n, Kleene.chain s.tagged (tag s.init) n)) i
        = untag (⋃ n, Kleene.chain s.tagged (tag s.init) n) i := by rw [hfix]
    simpa [tagged, untag_tag, lfp] using this
  · intro i a ha
    exact hinit (show (i, a) ∈ tag s.init from ha)
  · intro W hW hWop i a ha
    have hy : tag s.init ⊆ tag W := tag_mono hW
    have hFy : s.tagged (tag W) ⊆ tag W := by
      simp only [tagged, untag_tag]; exact tag_mono hWop
    exact hleast (tag W) hy hFy ha

/-- the solution is BELOW every post-fixpoint above init — the componentwise-least clause alone -/
theorem lfp_le_of_post (hm : s.Mono) (hc : s.Cont) (W : ι → Set α)
    (hW : ∀ i, s.init i ⊆ W i) (hWop : ∀ i, s.op W i ⊆ W i) : ∀ i, s.lfp i ⊆ W i :=
  (s.tagged_lfp hm hc).2.2 W hW hWop

end Sys

/-! ### The unary case: a one-equation system IS `Space.fixpoint`'s chain

Stated over `SpaceV` because `fixOp` (Positive.lean) is: the one-equation system over the unit
index set, seeded with `I` and stepping by `B`. -/

/-- the one-equation system over `Unit` -/
def unary (I : SpaceV) (B : SpaceV → SpaceV) : Sys Unit PathV :=
  ⟨fun _ => I, fun V _ => B (V ())⟩

theorem unary_chain (I : SpaceV) (B : SpaceV → SpaceV) :
    ∀ n, Kleene.chain (unary I B).tagged (tag (unary I B).init) n
          = tag (fun _ => Kleene.chain (fixOp I B) I n)
  | 0 => rfl
  | n + 1 => by
      rw [Kleene.chain_succ, unary_chain I B n]
      simp only [Sys.tagged, untag_tag]
      rfl

/-- **UNARY CORRESPONDENCE.**  The one-equation system's solution is the union of the Kleene chain of
`fixOp I B` from `I` — exactly `(Space.fixpoint i r b).denT` with `I = ⟦i⟧`, `B X = ⟦b⟧[r := X]`. -/
theorem unary_eq (I : SpaceV) (B : SpaceV → SpaceV) :
    (unary I B).lfp () = ⋃ n, Kleene.chain (fixOp I B) I n := by
  simp only [Sys.lfp]
  rw [untag_iUnion]
  exact Set.iUnion_congr fun n => by rw [unary_chain I B n, untag_tag]

/-- the same, stated on the syntax: a unary system built from a `Fixpoint`'s init and body solves to
that `Fixpoint`'s denotation -/
theorem unary_eq_denT (δ : RoutineEnv) (ρ : Env) (i : Space) (r : Name) (b : Space) :
    (unary (i.denT δ ρ) (fun X => b.denT δ (ρ.setM r X))).lfp () = (Space.fixpoint i r b).denT δ ρ := by
  rw [unary_eq]; rfl

/-! ### Strata: frozen lower values need no variance -/

/-- a stratum: its own variables `ι`, the lower strata's values `κ → Set α` FROZEN.  `G V L i` is the
`i`-th step read at own valuation `V` and lower valuation `L`. -/
def stratum (init : ι → Set α) (G : (ι → Set α) → (κ → Set α) → ι → Set α) (L : κ → Set α) : Sys ι α :=
  ⟨init, fun V => G V L⟩

/-- **STRATUM-ORDER SOUNDNESS.**  If `G` is monotone and continuous in the stratum's OWN variables for
every fixed lower valuation — and NOTHING is assumed about how it depends on the lower one — then for
every frozen `L` the stratum has its least post-fixpoint, characterised as in `tagged_lfp`.  A negative
or unknown dependency on a completed lower stratum is therefore harmless: it is a constant of the
operator, not a variable of the iteration. -/
theorem stratum_frozen_sound {κ : Type*} (init : ι → Set α)
    (G : (ι → Set α) → (κ → Set α) → ι → Set α)
    (hm : ∀ L, (stratum init G L).Mono) (hc : ∀ L, (stratum init G L).Cont) (L : κ → Set α) :
    (∀ i, (stratum init G L).op (stratum init G L).lfp i = (stratum init G L).lfp i)
    ∧ (∀ i, init i ⊆ (stratum init G L).lfp i)
    ∧ (∀ W : ι → Set α, (∀ i, init i ⊆ W i) → (∀ i, (stratum init G L).op W i ⊆ W i) →
        ∀ i, (stratum init G L).lfp i ⊆ W i) :=
  (stratum init G L).tagged_lfp (hm L) (hc L)

/-- and a `-` dependency really does occur in such a `G` without breaking anything: the stratum reading
`L` antitonically (`∖ L i`) is still monotone in its own variables -/
theorem stratum_antitone_lower_example (init : ι → Set α) (F : (ι → Set α) → ι → Set α)
    (hF : ∀ V W : ι → Set α, (∀ i, V i ⊆ W i) → ∀ i, F V i ⊆ F W i) (L : ι → Set α) :
    (stratum init (fun V L' i => F V i \ L' i) L).Mono := by
  intro V W h i
  simp only [stratum]
  exact Set.sdiff_subset_sdiff_left (hF V W h i)

end Zippy.Sim
