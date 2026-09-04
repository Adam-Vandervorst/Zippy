/-
==================================================================================================
FOLDING PRESERVES THE LEAST-FIXPOINT DENOTATION (plan.md 2E.2) — PARAMETRIC IN `LawOK`.

`terminating/REGISTRY.tsv` row O12b: "FOLD: if C_new = C_anc.σ then residualising with the call
ρ(σ) at the fold point gives a routine whose least fixpoint equals [[C_anc]]."  This module proves
that statement at the level where it is TRUE for every supercompiler of this shape, and names, as
explicit premises, exactly what the implementation (`SC.State` in Supercompiler.scala) has to
guarantee for the proof to apply to it.  Each premise is an EXECUTABLE INVARIANT there; the
correspondence table is at the end of this header.

==THE SHAPE OF THE ARGUMENT==
The residual program is a SYSTEM: one body per function node, each body a term whose residual calls
name other nodes.  Its semantics is the least fixpoint of the operator `R` that reads every body
under a valuation of the nodes (`Resid.sys`).  The original program's semantics is likewise the
least fixpoint of the original routine system (`Orig.sys`), and every node `g` has a CONFIGURATION
`conf g` whose original meaning `t g` is what the residual routine for `g` is supposed to compute.

Write `tₙ` for the original meaning of every configuration at unfolding depth `n` (the `n`-th Kleene
approximant of the original system, plugged into the configurations).  Then:

  (fix)   `R t = t`.  Reading a residual body with its calls given their ORIGINAL meaning yields the
          original meaning of the node's configuration.  This is the conjunction of everything a
          driving step promises: a `reduce` step is a certified law and preserves the denotation
          under every environment (O12a / `LawOK`); an `unfold` is definitional (`Orig.unfold_def`
          below — one clause of the semantics, not an assumption); a FOLD replaces the instance
          `conf g'·θ` by the call `g'(θ)`, whose original meaning is `t g' (θ)` = the meaning of
          `conf g'·θ` by the substitution lemma (O6a, the semantic half of which is U63).
  (prod)  `tₙ₊₁ ≤ R tₙ`.  PRODUCTIVITY: every node's body consumed EXACTLY ONE unfold of its own
          configuration before any fold, so the depth-`(n+1)` original meaning of `conf g` is
          reached by reading `body g` with its calls at depth `n`.  This is what rules out the
          classical fold unsoundness (a body that folds to itself without unfolding first would
          have `R ⊥ = ⊥`, and its "least fixpoint" would be `⊥` whatever the original meant).

From these two, and monotonicity + ω-continuity of `R` (which `Positive.lean`'s per-constructor
theorems supply once every residual call sits in a positive position — `Space.callPosB`), the
theorem `fold_correct` gives `lfp R = t`: the residual system's least fixpoint IS the original
meaning, node by node.  Leastness gives `lfp R ≤ t` from (fix); (prod) and induction on `n` give
`tₙ ≤ lfp R` for every `n`, hence `t = ⨆ tₙ ≤ lfp R`.

==WHAT IS PARAMETRIC AND WHY==
`FoldPremises.fix` bundles the law steps and the fold-site substitution lemma into ONE hypothesis
on purpose: item 4's `SC.reduceTraced` (2A.3) is what discharges the law half per run, by checking
each recorded `(law, before, after)` edge against a certified law instance, and O6a's semantic
substitution theorem is its own row.  Proving `fix` inside this file would mean re-deriving both
here — and a proof that agreed with the implementation by construction would prove nothing about
it, which is the objection O6a's registry row already records.  What is NOT parametric: the
unfold clause, the fixpoint argument, the productivity induction, and the passage from the abstract
lattice to the residual system built from actual `Space` bodies.

==THE CORRESPONDENCE TABLE — premise here ↔ executable invariant in Supercompiler.scala==
  `Resid.sys` monotone/continuous  ↔  `SC.State.residualPositive`: every residual body passes
                                      `SC.callPositive` (residual calls only in positive positions)
  (prod) one unfold per node       ↔  `SC.State.unfoldedNodes`: `makeNode` records the unfold it
                                      performs BEFORE driving the body; the final check asserts
                                      every residual routine has one.
  fold site is an instance         ↔  `SC.State.checkFold`: `Matching.subst(gc, θ)` re-applied ONCE
                                      is alpha-equal to the folded configuration `c`.
  law steps preserve denotation    ↔  `SC.reduceTraced` (2A.3): every edge names a certified law and
                                      re-applying that law at the recorded position reproduces `after`.

    proofs/lean/Zippy/Supercompile.lean#Zippy.Fold.fold_correct
    proofs/lean/Zippy/Supercompile.lean#Zippy.Fold.resid_lfp_eq_orig
==================================================================================================
-/
import Zippy.Positive
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Hom.Basic

namespace Zippy

/-! ### Positivity in the CALL positions

`Space.callPosB s` holds when every `call` in `s` sits under positive constructors only — the same
arms as `Space.posB`, with "the variable is not free in the negative operand" replaced by "the
negative operand contains no call" — AND three restrictions that are specific to calls:

  * a call's ARGUMENTS are call-free;
  * an `iteration`'s SOURCE is call-free (its body may call);
  * a `fixpoint` is call-free altogether.

WHY THE THREE.  Monotonicity in the routine environment `δ` is a statement about a body read under
two valuations `V ≤ V'` of the residual routines.  A residual routine is NOT, in general, monotone
in its own arguments (a datalog body `all ∪ (join(δ, e) \ all)` is antitone in `all`), so a call
whose argument itself grows with `V` — a nested call, or a call under an iteration whose source grows
with `V` and hands the bigger tail set to the call — need not grow with `V`.  The residual system's
operator would then not be monotone and "its least fixpoint" would not name anything.  The three
restrictions are exactly the positions where an argument could grow with `V`; under them the
denotation is monotone and continuous in `δ` for EVERY valuation, with no monotonicity-in-arguments
assumption at all (`denT_mono_delta`, `denT_cont_delta` take none).  `SC.callPositive`
(Supercompiler.scala) is the executable twin and the report records whether a run's residual met it. -/

mutual
  def Space.hasCall : Space → Bool
    | .empty | .lit _ | .mention _ => false
    | .singleton p => p.hasCall
    | .union x y | .inter x y | .sub x y
    | .restriction x y | .raffination x y | .composition x y => x.hasCall || y.hasCall
    | .wrap s p | .unwrap s p => s.hasCall || p.hasCall
    | .tailsUnion s | .tailsInter s => s.hasCall
    | .range x _ _ => x.hasCall
    | .call _ _ _ => true
    | .iteration src _ _ t => src.hasCall || t.hasCall
    | .fixpoint i _ b => i.hasCall || b.hasCall
    | .fold src ini _ _ _ t upd => src.hasCall || ini.hasCall || t.hasCall || upd.hasCall
    | .groundedPS p _ => p.hasCall
    | .groundedSS s _ => s.hasCall
  def Space.hasCalls : List Space → Bool
    | [] => false
    | s :: rest => s.hasCall || Space.hasCalls rest
  def Path.hasCall : Path → Bool
    | .deref _ | .const _ => false
    | .concat l r => l.hasCall || r.hasCall
    | .groundedPP p _ => p.hasCall
    | .groundedSP s _ => s.hasCall
  def Path.hasCalls : List Path → Bool
    | [] => false
    | p :: rest => p.hasCall || Path.hasCalls rest
end

mutual
  /-- every call sits in a positive position.  `SC.callPositive` in Supercompiler.scala. -/
  def Space.callPosB : Space → Bool
    | .empty | .lit _ | .mention _ => true
    | .singleton p => !p.hasCall
    | .union x y | .inter x y | .restriction x y | .composition x y => x.callPosB && y.callPosB
    | .sub x y | .raffination x y => x.callPosB && !y.hasCall
    | .wrap s p | .unwrap s p => s.callPosB && !p.hasCall
    | .tailsUnion s => s.callPosB
    | .tailsInter s => !s.hasCall
    | .range x _ _ => !x.hasCall
    -- a call's own arguments are call-free
    | .call _ refs ms => !Path.hasCalls refs && !Space.hasCalls ms
    -- the source is call-free; the body may call
    | .iteration src _ _ t => !src.hasCall && t.callPosB
    -- call-free altogether
    | .fixpoint i r b => !(Space.fixpoint i r b).hasCall
    | .fold src ini acc sym rest t upd => !(Space.fold src ini acc sym rest t upd).hasCall
    | .groundedPS p _ => !p.hasCall
    | .groundedSS s _ => !s.hasCall
  def Space.callPosBs : List Space → Bool
    | [] => true
    | s :: rest => s.callPosB && Space.callPosBs rest
end

/-- pointwise order on routine environments -/
def RoutineEnv.le (δ δ' : RoutineEnv) : Prop := ∀ r ps xs, δ r ps xs ⊆ δ' r ps xs

/-- the pointwise union of an ascending chain of routine environments -/
def RoutineEnv.iSup (Δ : ℕ → RoutineEnv) : RoutineEnv := fun r ps xs => ⋃ k, Δ k r ps xs

/-! a call-free term does not see the routine environment at all -/
mutual
theorem Space.denT_congr_delta_of_noCall (δ δ' : RoutineEnv) (ρ : Env) :
    ∀ s : Space, s.hasCall = false → s.denT δ ρ = s.denT δ' ρ
  | .empty, _ => rfl
  | .lit _, _ => rfl
  | .mention _, _ => rfl
  | .singleton _, _ => rfl
  | .union x y, h => by
      simp only [Space.hasCall, Bool.or_eq_false_iff] at h
      simp [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ x h.1,
            Space.denT_congr_delta_of_noCall δ δ' ρ y h.2]
  | .inter x y, h => by
      simp only [Space.hasCall, Bool.or_eq_false_iff] at h
      simp [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ x h.1,
            Space.denT_congr_delta_of_noCall δ δ' ρ y h.2]
  | .sub x y, h => by
      simp only [Space.hasCall, Bool.or_eq_false_iff] at h
      simp [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ x h.1,
            Space.denT_congr_delta_of_noCall δ δ' ρ y h.2]
  | .restriction x y, h => by
      simp only [Space.hasCall, Bool.or_eq_false_iff] at h
      simp [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ x h.1,
            Space.denT_congr_delta_of_noCall δ δ' ρ y h.2]
  | .raffination x y, h => by
      simp only [Space.hasCall, Bool.or_eq_false_iff] at h
      simp [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ x h.1,
            Space.denT_congr_delta_of_noCall δ δ' ρ y h.2]
  | .composition x y, h => by
      simp only [Space.hasCall, Bool.or_eq_false_iff] at h
      simp [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ x h.1,
            Space.denT_congr_delta_of_noCall δ δ' ρ y h.2]
  | .wrap s p, h => by
      simp only [Space.hasCall, Bool.or_eq_false_iff] at h
      simp [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ s h.1]
  | .unwrap s p, h => by
      simp only [Space.hasCall, Bool.or_eq_false_iff] at h
      simp [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ s h.1]
  | .tailsUnion s, h => by
      simp only [Space.hasCall] at h
      simp [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ s h]
  | .tailsInter s, h => by
      simp only [Space.hasCall] at h
      simp [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ s h]
  | .range _ _ _, _ => rfl
  | .call _ _ _, h => by simp [Space.hasCall] at h
  | .iteration src sym rest t, h => by
      simp only [Space.hasCall, Bool.or_eq_false_iff] at h
      simp only [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ src h.1]
      exact Set.iUnion_congr fun hd => Set.iUnion_congr fun _ =>
        Space.denT_congr_delta_of_noCall δ δ' _ t h.2
  | .fixpoint i r b, h => by
      simp only [Space.hasCall, Bool.or_eq_false_iff] at h
      simp only [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ i h.1]
      exact Set.iUnion_congr fun n =>
        Kleene.chain_congr (fun X => by
          simp [fixOp, Space.denT_congr_delta_of_noCall δ δ' _ b h.2]) rfl n
  | .fold _ _ _ _ _ _ _, _ => rfl
  | .groundedPS _ _, _ => rfl
  | .groundedSS _ _, _ => rfl
theorem Space.denTs_congr_delta_of_noCall (δ δ' : RoutineEnv) (ρ : Env) :
    ∀ ms : List Space, Space.hasCalls ms = false → Space.denTs δ ρ ms = Space.denTs δ' ρ ms
  | [], _ => rfl
  | s :: rest, h => by
      simp only [Space.hasCalls, Bool.or_eq_false_iff] at h
      simp [Space.denTs, Space.denT_congr_delta_of_noCall δ δ' ρ s h.1,
            Space.denTs_congr_delta_of_noCall δ δ' ρ rest h.2]
end

theorem Space.callPosBs_mem {ms : List Space} (h : Space.callPosBs ms = true) {s : Space}
    (hs : s ∈ ms) : s.callPosB = true := by
  induction ms with
  | nil => simp at hs
  | cons a rest ih =>
    simp only [Space.callPosBs, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hs with rfl | hs
    · exact h.1
    · exact ih h.2 hs

/-! ### Monotonicity in the routine environment -/

mutual
theorem Space.denT_mono_delta {δ δ' : RoutineEnv} (hle : RoutineEnv.le δ δ') :
    ∀ (s : Space) (ρ : Env), s.callPosB = true → s.denT δ ρ ⊆ s.denT δ' ρ
  | .empty, _, _ => subset_rfl
  | .lit _, _, _ => subset_rfl
  | .mention _, _, _ => subset_rfl
  | .singleton _, _, _ => subset_rfl
  | .union x y, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true] at hp
      exact Set.union_subset_union (Space.denT_mono_delta hle x ρ hp.1)
        (Space.denT_mono_delta hle y ρ hp.2)
  | .inter x y, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true] at hp
      exact Set.inter_subset_inter (Space.denT_mono_delta hle x ρ hp.1)
        (Space.denT_mono_delta hle y ρ hp.2)
  | .sub x y, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      simp only [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ y hp.2]
      exact Set.sdiff_subset_sdiff_left (Space.denT_mono_delta hle x ρ hp.1)
  | .restriction x y, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true] at hp
      have hx := Space.denT_mono_delta hle x ρ hp.1
      have hy := Space.denT_mono_delta hle y ρ hp.2
      simp only [Space.denT]
      rintro e ⟨he, q, hq, hqe⟩
      exact ⟨hx he, q, hy hq, hqe⟩
  | .raffination x y, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      have hx := Space.denT_mono_delta hle x ρ hp.1
      simp only [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ y hp.2]
      rintro e ⟨he, hne⟩
      exact ⟨hx he, fun ⟨_, hq⟩ => hne ⟨he, hq⟩⟩
  | .composition x y, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true] at hp
      have hx := Space.denT_mono_delta hle x ρ hp.1
      have hy := Space.denT_mono_delta hle y ρ hp.2
      simp only [Space.denT]
      rintro e ⟨u, hu, v, hv, rfl⟩
      exact ⟨u, hx hu, v, hy hv, rfl⟩
  | .wrap s p, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true] at hp
      have hs := Space.denT_mono_delta hle s ρ hp.1
      simp only [Space.denT]
      rintro e ⟨u, hu, rfl⟩
      exact ⟨u, hs hu, rfl⟩
  | .unwrap s p, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true] at hp
      have hs := Space.denT_mono_delta hle s ρ hp.1
      simp only [Space.denT]
      intro e he
      exact hs he
  | .tailsUnion s, ρ, hp => by
      simp only [Space.callPosB] at hp
      have hs := Space.denT_mono_delta hle s ρ hp
      simp only [Space.denT]
      rintro t ⟨hd, ht⟩
      exact ⟨hd, hs ht⟩
  | .tailsInter s, ρ, hp => by
      simp only [Space.callPosB, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      simp [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ s hp]
  | .range _ _ _, _, _ => subset_rfl
  | .call r refs ms, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      simp only [Space.denT, Space.denTs_congr_delta_of_noCall δ δ' ρ ms hp.2]
      exact hle r _ _
  | .iteration src sym rest t, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      simp only [Space.denT, Space.denT_congr_delta_of_noCall δ δ' ρ src hp.1]
      exact Set.iUnion_mono fun hd => Set.iUnion_mono fun _ =>
        Space.denT_mono_delta hle t _ hp.2
  | .fixpoint i r b, ρ, hp => by
      simp only [Space.callPosB, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      rw [Space.denT_congr_delta_of_noCall δ δ' ρ _ hp]
  | .fold _ _ _ _ _ _ _, _, _ => subset_rfl
  | .groundedPS _ _, _, _ => subset_rfl
  | .groundedSS _ _, _, _ => subset_rfl
end

/-! ### Continuity in the routine environment -/

/-- an ascending chain of routine environments -/
def RoutineChain (Δ : ℕ → RoutineEnv) : Prop := ∀ k, RoutineEnv.le (Δ k) (Δ (k + 1))

theorem RoutineChain.le_of_le {Δ : ℕ → RoutineEnv} (h : RoutineChain Δ) {i j : ℕ} (hij : i ≤ j) :
    RoutineEnv.le (Δ i) (Δ j) := by
  induction hij with
  | refl => exact fun _ _ _ => subset_rfl
  | step _ ih => exact fun r ps xs => (ih r ps xs).trans (h _ r ps xs)

theorem RoutineChain.le_iSup {Δ : ℕ → RoutineEnv} (k : ℕ) :
    RoutineEnv.le (Δ k) (RoutineEnv.iSup Δ) :=
  fun r ps xs => Set.subset_iUnion (fun k => Δ k r ps xs) k

theorem Space.denT_cont_delta {Δ : ℕ → RoutineEnv} (hΔ : RoutineChain Δ) :
    ∀ (s : Space) (ρ : Env), s.callPosB = true →
      s.denT (RoutineEnv.iSup Δ) ρ = ⋃ k, s.denT (Δ k) ρ
  | .empty, _, _ => by simp [Space.denT]
  | .lit _, _, _ => by simp only [Space.denT]; exact (Set.iUnion_const _).symm
  | .mention _, _, _ => by simp only [Space.denT]; exact (Set.iUnion_const _).symm
  | .singleton _, _, _ => by simp only [Space.denT]; exact (Set.iUnion_const _).symm
  | .union x y, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true] at hp
      simp only [Space.denT, Space.denT_cont_delta hΔ x ρ hp.1, Space.denT_cont_delta hΔ y ρ hp.2]
      exact (Set.iUnion_union_distrib _ _).symm
  | .inter x y, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true] at hp
      simp only [Space.denT, Space.denT_cont_delta hΔ x ρ hp.1, Space.denT_cont_delta hΔ y ρ hp.2]
      refine iUnion_binary (fun i j hij => Space.denT_mono_delta (hΔ.le_of_le hij) x ρ hp.1)
        (fun i j hij => Space.denT_mono_delta (hΔ.le_of_le hij) y ρ hp.2) (· ∩ ·)
        (fun _ _ _ _ h1 h2 => Set.inter_subset_inter h1 h2) ?_
      intro S T e he
      obtain ⟨hS, hT⟩ := he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hS
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hT
      exact ⟨i, j, hi, hj⟩
  | .sub x y, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      simp only [Space.denT, Space.denT_cont_delta hΔ x ρ hp.1]
      have : ∀ k, y.denT (Δ k) ρ = y.denT (RoutineEnv.iSup Δ) ρ := fun k =>
        Space.denT_congr_delta_of_noCall _ _ ρ y hp.2
      simp only [this]
      exact Set.iUnion_sdiff _ _
  | .restriction x y, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true] at hp
      simp only [Space.denT, Space.denT_cont_delta hΔ x ρ hp.1, Space.denT_cont_delta hΔ y ρ hp.2]
      refine iUnion_binary (fun i j hij => Space.denT_mono_delta (hΔ.le_of_le hij) x ρ hp.1)
        (fun i j hij => Space.denT_mono_delta (hΔ.le_of_le hij) y ρ hp.2)
        (fun a b => {e ∈ a | ∃ q ∈ b, q <+: e}) ?_ ?_
      · rintro a a' b b' h1 h2 e ⟨he, q, hq, hqe⟩
        exact ⟨h1 he, q, h2 hq, hqe⟩
      · rintro S T e ⟨he, q, hq, hqe⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hq
        exact ⟨i, j, hi, q, hj, hqe⟩
  | .raffination x y, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      simp only [Space.denT, Space.denT_cont_delta hΔ x ρ hp.1]
      have : ∀ k, y.denT (Δ k) ρ = y.denT (RoutineEnv.iSup Δ) ρ := fun k =>
        Space.denT_congr_delta_of_noCall _ _ ρ y hp.2
      simp only [this]
      ext e
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨⟨k, hk⟩, hne⟩
        exact ⟨k, hk, fun ⟨_, hq⟩ => hne ⟨⟨k, hk⟩, hq⟩⟩
      · rintro ⟨k, hk, hne⟩
        exact ⟨⟨k, hk⟩, fun ⟨_, hq⟩ => hne ⟨hk, hq⟩⟩
  | .composition x y, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true] at hp
      simp only [Space.denT, Space.denT_cont_delta hΔ x ρ hp.1, Space.denT_cont_delta hΔ y ρ hp.2]
      refine iUnion_binary (fun i j hij => Space.denT_mono_delta (hΔ.le_of_le hij) x ρ hp.1)
        (fun i j hij => Space.denT_mono_delta (hΔ.le_of_le hij) y ρ hp.2)
        (fun a b => {e | ∃ u ∈ a, ∃ v ∈ b, e = u ++ v}) ?_ ?_
      · rintro a a' b b' h1 h2 e ⟨u, hu, v, hv, rfl⟩
        exact ⟨u, h1 hu, v, h2 hv, rfl⟩
      · rintro S T e ⟨u, hu, v, hv, rfl⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hv
        exact ⟨i, j, u, hi, v, hj, rfl⟩
  | .wrap s p, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true] at hp
      simp only [Space.denT, Space.denT_cont_delta hΔ s ρ hp.1]
      ext e
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨u, ⟨k, hk⟩, rfl⟩; exact ⟨k, u, hk, rfl⟩
      · rintro ⟨k, u, hk, rfl⟩; exact ⟨u, ⟨k, hk⟩, rfl⟩
  | .unwrap s p, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true] at hp
      simp only [Space.denT, Space.denT_cont_delta hΔ s ρ hp.1]
      ext e
      simp [Set.mem_iUnion]
  | .tailsUnion s, ρ, hp => by
      simp only [Space.callPosB] at hp
      simp only [Space.denT, Space.denT_cont_delta hΔ s ρ hp]
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨hd, k, hk⟩; exact ⟨k, hd, hk⟩
      · rintro ⟨k, hd, hk⟩; exact ⟨hd, k, hk⟩
  | .tailsInter s, ρ, hp => by
      simp only [Space.callPosB, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      have : ∀ k, s.denT (Δ k) ρ = s.denT (RoutineEnv.iSup Δ) ρ := fun k =>
        Space.denT_congr_delta_of_noCall _ _ ρ s hp
      simp only [Space.denT, this]
      exact (Set.iUnion_const _).symm
  | .range _ _ _, _, _ => by simp [Space.denT]
  | .call r refs ms, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      simp only [Space.denT, RoutineEnv.iSup]
      have : ∀ k, Space.denTs (Δ k) ρ ms = Space.denTs (RoutineEnv.iSup Δ) ρ ms := fun k =>
        Space.denTs_congr_delta_of_noCall _ _ ρ ms hp.2
      simp only [this]
  | .iteration src sym rest t, ρ, hp => by
      simp only [Space.callPosB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      have : ∀ k, src.denT (Δ k) ρ = src.denT (RoutineEnv.iSup Δ) ρ := fun k =>
        Space.denT_congr_delta_of_noCall _ _ ρ src hp.1
      simp only [Space.denT, this, Space.denT_cont_delta hΔ t _ hp.2]
      ext e
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨hd, hhd, k, hk⟩; exact ⟨k, hd, hhd, hk⟩
      · rintro ⟨k, hd, hhd, hk⟩; exact ⟨hd, hhd, k, hk⟩
  | .fixpoint i r b, ρ, hp => by
      simp only [Space.callPosB, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      have : ∀ k, (Space.fixpoint i r b).denT (Δ k) ρ = (Space.fixpoint i r b).denT (RoutineEnv.iSup Δ) ρ :=
        fun k => Space.denT_congr_delta_of_noCall _ _ ρ _ hp
      simp only [this]
      exact (Set.iUnion_const _).symm
  | .fold _ _ _ _ _ _ _, _, _ => by simp [Space.denT]
  | .groundedPS _ _, _, _ => by simp [Space.denT]
  | .groundedSS _ _, _, _ => by simp [Space.denT]

/-! ### The abstract fold theorem, in any complete lattice -/

namespace Fold

variable {L : Type*} [CompleteLattice L]

/-- the Kleene iterates of `R` from `⊥` -/
def iter (R : L → L) : ℕ → L
  | 0 => ⊥
  | n + 1 => R (iter R n)

/-- the Kleene supremum -/
def kleene (R : L → L) : L := ⨆ n, iter R n

/-- ω-continuity in a complete lattice: `R` commutes with the supremum of an ascending chain -/
def OmegaContL (R : L → L) : Prop := ∀ A : ℕ → L, Monotone A → R (⨆ n, A n) = ⨆ n, R (A n)

theorem iter_mono {R : L → L} (hR : Monotone R) : Monotone (iter R) := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero => exact bot_le
  | succ n ih => exact hR ih

theorem iter_le_of_prefixpoint {R : L → L} (hR : Monotone R) {y : L} (hy : R y ≤ y) :
    ∀ n, iter R n ≤ y
  | 0 => bot_le
  | n + 1 => (hR (iter_le_of_prefixpoint hR hy n)).trans hy

/-- the Kleene supremum of a monotone ω-continuous operator is its least fixpoint -/
theorem kleene_is_lfp {R : L → L} (hR : Monotone R) (hc : OmegaContL R) :
    R (kleene R) = kleene R ∧ ∀ y, R y ≤ y → kleene R ≤ y := by
  refine ⟨?_, fun y hy => iSup_le (iter_le_of_prefixpoint hR hy)⟩
  unfold kleene
  rw [hc _ (iter_mono hR)]
  apply le_antisymm
  · exact iSup_le fun n => le_iSup_of_le (n + 1) le_rfl
  · exact iSup_le fun n => le_iSup_of_le n (iter_mono hR (Nat.le_succ n))

/-- THE PREMISES THE IMPLEMENTATION OWES.  See this file's header for what each is, and which
executable invariant in `Supercompiler.scala` corresponds to it. -/
structure FoldPremises (R : L → L) (t : L) (tn : ℕ → L) : Prop where
  /-- the original meaning is a fixpoint of the residual system (laws + unfold + instance fold) -/
  fix : R t = t
  /-- one unfold per node: depth `n+1` of the original is reached by one residual step from depth `n` -/
  productive : ∀ n, tn (n + 1) ≤ R (tn n)
  /-- the approximants start at `⊥` and ascend to `t` -/
  zero : tn 0 = ⊥
  mono : Monotone tn
  sup : (⨆ n, tn n) = t

/-- **THE FOLD THEOREM.**  Under the premises, the residual system's least fixpoint is exactly the
original meaning `t`. -/
theorem fold_correct {R : L → L} (hR : Monotone R) (hc : OmegaContL R) {t : L} {tn : ℕ → L}
    (h : FoldPremises R t tn) : kleene R = t := by
  obtain ⟨hfix, hleast⟩ := kleene_is_lfp hR hc
  apply le_antisymm
  · -- leastness: `t` is a fixpoint, hence a pre-fixpoint
    exact hleast t h.fix.le
  · -- every approximant is below the least fixpoint, by productivity and induction
    rw [← h.sup]
    refine iSup_le fun n => ?_
    induction n with
    | zero => rw [h.zero]; exact bot_le
    | succ n ih => exact (h.productive n).trans ((hR ih).trans hfix.le)

end Fold

/-! ### The residual system built from actual bodies

`Resid.sys bodies` reads every residual body under a valuation of the residual routines.  The
valuation type is `RoutineEnv` itself — a residual routine, like an original one, is a function of
its argument values — ordered pointwise, which is a complete lattice (`Pi` of `Set`).  The
`Fold` theorem is then instantiated at `L := RoutineEnv`. -/

namespace Resid

/-- a residual routine table: parameter names and a body, per residual name -/
structure Table where
  refs : Name → List Name
  ments : Name → List Name
  body : Name → Space

/-- bind positional arguments to parameter names, over a base environment -/
def bindR (ρ : Env) : List Name → List PathV → Env
  | [], _ => ρ
  | _, [] => ρ
  | n :: ns, v :: vs => (bindR ρ ns vs).setR n v
def bindM (ρ : Env) : List Name → List SpaceV → Env
  | [], _ => ρ
  | _, [] => ρ
  | n :: ns, x :: xs => (bindM ρ ns xs).setM n x

/-- the base environment: every path variable `[]`, every space variable `∅` -/
def Env.base : Env := ⟨fun _ => [], fun _ => ∅⟩

/-- the environment a call's body is read in -/
def argEnv (T : Table) (g : Name) (ps : List PathV) (xs : List SpaceV) : Env :=
  bindM (bindR Env.base (T.refs g) ps) (T.ments g) xs

/-- the residual system: one step reads every body under the valuation `V` -/
def sys (T : Table) (V : RoutineEnv) : RoutineEnv :=
  fun g ps xs => (T.body g).denT V (argEnv T g ps xs)

/-- pointwise `⊆` on routine environments is the lattice order of `RoutineEnv` -/
theorem le_iff (δ δ' : RoutineEnv) : δ ≤ δ' ↔ RoutineEnv.le δ δ' := by
  constructor
  · intro h r ps xs; exact h r ps xs
  · intro h r ps xs; exact h r ps xs

theorem iSup_eq (Δ : ℕ → RoutineEnv) : (⨆ n, Δ n) = RoutineEnv.iSup Δ := by
  funext r ps xs
  simp only [RoutineEnv.iSup]
  ext e
  simp [iSup_apply, Set.mem_iUnion]

/-- every body call-positive -/
def Positive (T : Table) : Prop := ∀ g, (T.body g).callPosB = true

/-- the residual system is monotone -/
theorem sys_mono (T : Table) (hT : Positive T) : Monotone (sys T) := by
  intro V V' h g ps xs
  exact Space.denT_mono_delta ((le_iff V V').mp h) (T.body g) _ (hT g)

/-- the residual system commutes with the supremum of a chain -/
theorem sys_cont (T : Table) (hT : Positive T) : Fold.OmegaContL (sys T) := by
  intro Δ hΔ
  have hch : RoutineChain Δ := fun k => (le_iff _ _).mp (hΔ (Nat.le_succ k))
  rw [iSup_eq]
  funext g ps xs
  rw [iSup_apply]
  simp only [sys]
  rw [Space.denT_cont_delta hch (T.body g) _ (hT g)]
  ext e
  simp [sys, iSup_apply, Set.mem_iUnion]

end Resid

/-! ### The original system, and the unfold clause

The original program is a routine table too, read by the same `sys`.  Its least fixpoint is the
meaning `eval`'s `Call` rule computes by unfolding; its Kleene approximants are what `Fold.iter`
gives, and the ONE-STEP UNFOLD IS A CLAUSE OF THE DEFINITION — `unfold_def` is `rfl`.  This is the
part of a fold-soundness proof that is usually stated as "unfolding is meaning-preserving"; here
there is nothing to assume. -/

namespace Orig

/-- reading `call r refs ms` at depth `n+1` IS reading `r`'s body at depth `n` with the argument
values bound — `eval`'s `Call` rule, one level. -/
theorem unfold_def (T : Resid.Table) (n : ℕ) (ρ : Env) (r : Name) (refs : List Path)
    (ms : List Space) :
    (Space.call r refs ms).denT (Fold.iter (Resid.sys T) (n + 1)) ρ
      = (T.body r).denT (Fold.iter (Resid.sys T) n)
          (Resid.argEnv T r (Path.denTs ρ refs)
            (Space.denTs (Fold.iter (Resid.sys T) (n + 1)) ρ ms)) := rfl

end Orig

/-! ### THE INSTANTIATION — the fold theorem for actual residual tables -/

namespace Fold

/-- **O12b, at the residual system.**  For a call-positive residual table `T`, if the original meaning
`t` (per node, as a function of the node's arguments) is a fixpoint of `Resid.sys T` and the
original depth approximants are productive through it, then the residual system's least fixpoint
IS `t`.  `hT` is `SC.State.residualPositive`; the premises are the correspondence table in this
file's header. -/
theorem resid_lfp_eq_orig (T : Resid.Table) (hT : Resid.Positive T) {t : RoutineEnv}
    {tn : ℕ → RoutineEnv} (h : FoldPremises (Resid.sys T) t tn) :
    kleene (Resid.sys T) = t :=
  fold_correct (Resid.sys_mono T hT) (Resid.sys_cont T hT) h

/-- and the least fixpoint is a fixpoint of the system: reading every residual body under it gives
it back — which is what makes "the residual routine `g` computes `t g`" a statement about a
PROGRAM and not only about a lattice element. -/
theorem resid_is_fixpoint (T : Resid.Table) (hT : Resid.Positive T) :
    Resid.sys T (kleene (Resid.sys T)) = kleene (Resid.sys T) :=
  (kleene_is_lfp (Resid.sys_mono T hT) (Resid.sys_cont T hT)).1

end Fold

end Zippy
