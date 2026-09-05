/-
==================================================================================================
SEMANTIC SUBSTITUTION — O6a AS A THEOREM (tasks.md C1).

`Subst.lean` defines the production substitution (`substS`/`substP`: simultaneous in both sorts,
capture-avoiding, total) and proves its HYGIENE.  `terminating/REGISTRY.tsv` row O6a — the
beta-soundness of capture-avoiding inlining, `[[Call r(a; s)]] = [[B[x := a, m := s]]]` — needs the
SEMANTIC half: substituting into a term denotes the same as evaluating the term in the environment
that binds every substituted name to its replacement's meaning.  That is `substS_denT` below, for
every constructor of the certified language, `Call`, `Iteration` and `Fixpoint` included:

    (substS F σm σp s).denT δ ρ = s.denT δ (Env.extend δ ρ σm σp)

where `Env.extend δ ρ σm σp` is `ρ` with each `m ∈ dom σm` rebound to `⟦σm m⟧δρ` and each
`r ∈ dom σp` to `⟦σp r⟧ρ`.  The proof is the standard substitution lemma; its whole difficulty is
the three binder forms, where the bound name may have been alpha-renamed to a fresh one.  The
argument there is exactly the one `Subst.lean`'s capture-avoidance theorem makes syntactically,
read semantically: the fresh name is outside every replacement's free names and outside the body's,
so rebinding it disturbs nothing the body or a replacement reads (`extend_bindM_agree`,
`extend_bindR_agree`), and the denotation depends only on the free names (`Space.denT_congr_rm`,
a two-sort strengthening of `Positive.lean`'s `Space.denT_congr`).

The side conditions C1 names are corollaries: `fixpoint_alpha` (alpha-renaming a bound name to a
fresh one preserves the denotation), `fixpoint_shadow` / `iteration_shadow` (a substitution for a
bound name does not enter the body), `instance_denT` (the fold-site lemma: an instance `gc·θ`
denotes `gc` under the extended environment — the `fix` premise's substitution half in
`Supercompile.lean`), and the simultaneous-versus-sequential distinction is the theorem's very
shape (one environment extension; `Subst.lean`'s `seq_ne_simul_gyx` is the syntactic witness).

`FreshSupply` is a parameter throughout: the theorem holds for EVERY fresh-name policy, so the
Scala's counter is covered by the correspondence trace (`Trace.lean`, generated) exactly as the
hygiene theorems are.  Grounded forms, `Fold` and `Range` denote `∅` on both sides (outside the
fragment, `Positive.lean`'s header) — the theorem is stated for the whole grammar and is trivial
there.
==================================================================================================
-/
import Zippy.Subst
import Zippy.Positive

namespace Zippy

/-! ### Agreement on the free names of BOTH sorts -/

/-- two environments agreeing on the refs in `R` and the mentions in `M` -/
def Env.AgreeRM (R M : Finset Name) (ρ ρ' : Env) : Prop :=
  (∀ r ∈ R, ρ.refs r = ρ'.refs r) ∧ (∀ m ∈ M, ρ.spaces m = ρ'.spaces m)

namespace Env.AgreeRM

theorem mono {R M R' M' : Finset Name} {ρ ρ' : Env} (h : Env.AgreeRM R M ρ ρ')
    (hR : R' ⊆ R) (hM : M' ⊆ M) : Env.AgreeRM R' M' ρ ρ' :=
  ⟨fun r hr => h.1 r (hR hr), fun m hm => h.2 m (hM hm)⟩

theorem trans {R M : Finset Name} {ρ₁ ρ₂ ρ₃ : Env} (h₁ : Env.AgreeRM R M ρ₁ ρ₂)
    (h₂ : Env.AgreeRM R M ρ₂ ρ₃) : Env.AgreeRM R M ρ₁ ρ₃ :=
  ⟨fun r hr => (h₁.1 r hr).trans (h₂.1 r hr), fun m hm => (h₁.2 m hm).trans (h₂.2 m hm)⟩

/-- rebinding a ref on both sides: agreement on `R` from agreement on `R.erase b` -/
theorem setR {R M : Finset Name} {ρ ρ' : Env} (b : Name) (h : Env.AgreeRM (R.erase b) M ρ ρ')
    (v : PathV) : Env.AgreeRM R M (ρ.setR b v) (ρ'.setR b v) := by
  refine ⟨fun r hr => ?_, fun m hm => h.2 m hm⟩
  by_cases hrb : r = b
  · subst hrb; simp [Env.setR]
  · simp only [Env.setR, Function.update_of_ne hrb]
    exact h.1 r (Finset.mem_erase.mpr ⟨hrb, hr⟩)

/-- rebinding a mention on both sides -/
theorem setM {R M : Finset Name} {ρ ρ' : Env} (b : Name) (h : Env.AgreeRM R (M.erase b) ρ ρ')
    (X : SpaceV) : Env.AgreeRM R M (ρ.setM b X) (ρ'.setM b X) := by
  refine ⟨fun r hr => h.1 r hr, fun m hm => ?_⟩
  by_cases hmb : m = b
  · subst hmb; simp
  · rw [Env.setM_spaces_ne _ _ hmb, Env.setM_spaces_ne _ _ hmb]
    exact h.2 m (Finset.mem_erase.mpr ⟨hmb, hm⟩)

end Env.AgreeRM

/-- a path denotes the same in two environments agreeing on its free refs -/
theorem Path.denT_congr_rm {ρ ρ' : Env} :
    ∀ p : Path, (∀ r ∈ p.freeR, ρ.refs r = ρ'.refs r) → p.denT ρ = p.denT ρ'
  | .deref r, h => by simp only [Path.denT]; exact h r (by simp [Path.freeR])
  | .const _, _ => rfl
  | .concat l r, h => by
      simp only [Path.freeR] at h
      simp [Path.denT, Path.denT_congr_rm l (fun x hx => h x (Finset.mem_union_left _ hx)),
            Path.denT_congr_rm r (fun x hx => h x (Finset.mem_union_right _ hx))]
  | .groundedPP _ _, _ => rfl
  | .groundedSP _ _, _ => rfl

theorem Path.denTs_congr_rm {ρ ρ' : Env} :
    ∀ ps : List Path, (∀ r ∈ Path.freeRs ps, ρ.refs r = ρ'.refs r) →
      Path.denTs ρ ps = Path.denTs ρ' ps
  | [], _ => rfl
  | p :: rest, h => by
      simp only [Path.freeRs] at h
      simp [Path.denTs, Path.denT_congr_rm p (fun x hx => h x (Finset.mem_union_left _ hx)),
            Path.denTs_congr_rm rest (fun x hx => h x (Finset.mem_union_right _ hx))]

mutual
/-- THE DENOTATION DEPENDS ONLY ON THE FREE NAMES, both sorts -/
theorem Space.denT_congr_rm (δ : RoutineEnv) :
    ∀ (s : Space) (ρ ρ' : Env), Env.AgreeRM s.freeR s.freeM ρ ρ' → s.denT δ ρ = s.denT δ ρ'
  | .empty, _, _, _ => rfl
  | .lit _, _, _, _ => rfl
  | .mention v, ρ, ρ', h => h.2 v (by simp [Space.freeM])
  | .singleton p, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      simp [Space.denT, Path.denT_congr_rm p h.1]
  | .union x y, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      simp [Space.denT, Space.denT_congr_rm δ x ρ ρ' (h.mono Finset.subset_union_left Finset.subset_union_left),
            Space.denT_congr_rm δ y ρ ρ' (h.mono Finset.subset_union_right Finset.subset_union_right)]
  | .inter x y, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      simp [Space.denT, Space.denT_congr_rm δ x ρ ρ' (h.mono Finset.subset_union_left Finset.subset_union_left),
            Space.denT_congr_rm δ y ρ ρ' (h.mono Finset.subset_union_right Finset.subset_union_right)]
  | .sub x y, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      simp [Space.denT, Space.denT_congr_rm δ x ρ ρ' (h.mono Finset.subset_union_left Finset.subset_union_left),
            Space.denT_congr_rm δ y ρ ρ' (h.mono Finset.subset_union_right Finset.subset_union_right)]
  | .restriction x y, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      simp [Space.denT, Space.denT_congr_rm δ x ρ ρ' (h.mono Finset.subset_union_left Finset.subset_union_left),
            Space.denT_congr_rm δ y ρ ρ' (h.mono Finset.subset_union_right Finset.subset_union_right)]
  | .raffination x y, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      simp [Space.denT, Space.denT_congr_rm δ x ρ ρ' (h.mono Finset.subset_union_left Finset.subset_union_left),
            Space.denT_congr_rm δ y ρ ρ' (h.mono Finset.subset_union_right Finset.subset_union_right)]
  | .composition x y, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      simp [Space.denT, Space.denT_congr_rm δ x ρ ρ' (h.mono Finset.subset_union_left Finset.subset_union_left),
            Space.denT_congr_rm δ y ρ ρ' (h.mono Finset.subset_union_right Finset.subset_union_right)]
  | .wrap s p, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      simp [Space.denT, Space.denT_congr_rm δ s ρ ρ' (h.mono Finset.subset_union_left Finset.subset_union_left),
            Path.denT_congr_rm p (fun x hx => h.1 x (Finset.mem_union_right _ hx))]
  | .unwrap s p, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      simp [Space.denT, Space.denT_congr_rm δ s ρ ρ' (h.mono Finset.subset_union_left Finset.subset_union_left),
            Path.denT_congr_rm p (fun x hx => h.1 x (Finset.mem_union_right _ hx))]
  | .tailsUnion s, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      simp [Space.denT, Space.denT_congr_rm δ s ρ ρ' h]
  | .tailsInter s, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      simp [Space.denT, Space.denT_congr_rm δ s ρ ρ' h]
  | .range _ _ _, _, _, _ => rfl
  | .call r refs ms, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      simp [Space.denT, Path.denTs_congr_rm refs (fun x hx => h.1 x (Finset.mem_union_left _ hx)),
            Space.denTs_congr_rm δ ms ρ ρ' (h.mono Finset.subset_union_right Finset.subset_union_right)]
  | .iteration src sym rest t, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      have hsrc := Space.denT_congr_rm δ src ρ ρ' (h.mono Finset.subset_union_left Finset.subset_union_left)
      have ht : ∀ hd : Name,
          t.denT δ (((ρ.setR sym [hd]).setM rest (tailsAt hd (src.denT δ ρ'))))
            = t.denT δ (((ρ'.setR sym [hd]).setM rest (tailsAt hd (src.denT δ ρ')))) := fun hd =>
        Space.denT_congr_rm δ t _ _
          (((h.mono Finset.subset_union_right Finset.subset_union_right).setR sym [hd]).setM rest _)
      simp only [Space.denT, hsrc]
      exact Set.iUnion_congr fun hd => Set.iUnion_congr fun _ => ht hd
  | .fixpoint i r b, ρ, ρ', h => by
      simp only [Space.freeR, Space.freeM] at h
      have hi := Space.denT_congr_rm δ i ρ ρ' (h.mono Finset.subset_union_left Finset.subset_union_left)
      have hb : ∀ X, b.denT δ (ρ.setM r X) = b.denT δ (ρ'.setM r X) := fun X =>
        Space.denT_congr_rm δ b _ _ ((h.mono Finset.subset_union_right Finset.subset_union_right).setM r X)
      simp only [Space.denT]
      exact Set.iUnion_congr fun n =>
        Kleene.chain_congr (F := fixOp (i.denT δ ρ) fun X => b.denT δ (ρ.setM r X))
          (fun X => by simp [fixOp, hi, hb X]) hi n
  | .fold _ _ _ _ _ _ _, _, _, _ => rfl
  | .groundedPS _ _, _, _, _ => rfl
  | .groundedSS _ _, _, _, _ => rfl

theorem Space.denTs_congr_rm (δ : RoutineEnv) :
    ∀ (ms : List Space) (ρ ρ' : Env), Env.AgreeRM (Space.freeRs ms) (Space.freeMs ms) ρ ρ' →
      Space.denTs δ ρ ms = Space.denTs δ ρ' ms
  | [], _, _, _ => rfl
  | s :: rest, ρ, ρ', h => by
      simp only [Space.freeRs, Space.freeMs] at h
      simp [Space.denTs, Space.denT_congr_rm δ s ρ ρ' (h.mono Finset.subset_union_left Finset.subset_union_left),
            Space.denTs_congr_rm δ rest ρ ρ' (h.mono Finset.subset_union_right Finset.subset_union_right)]
end

/-! ### The environment a substitution denotes -/

/-- `ρ` with every substituted name bound to the meaning of its replacement (under `ρ`) -/
def Env.extend (δ : RoutineEnv) (ρ : Env) (σm : List (Name × Space)) (σp : List (Name × Path)) : Env :=
  ⟨fun r => match lookupR σp r with | some p => p.denT ρ | none => ρ.refs r,
   fun m => match lookupM σm m with | some t => t.denT δ ρ | none => ρ.spaces m⟩

theorem Env.extend_refs_some (δ : RoutineEnv) (ρ : Env) (σm : List (Name × Space)) {σp : List (Name × Path)}
    {r : Name} {p : Path} (h : lookupR σp r = some p) : (Env.extend δ ρ σm σp).refs r = p.denT ρ := by
  simp [Env.extend, h]
theorem Env.extend_refs_none (δ : RoutineEnv) (ρ : Env) (σm : List (Name × Space)) {σp : List (Name × Path)}
    {r : Name} (h : lookupR σp r = none) : (Env.extend δ ρ σm σp).refs r = ρ.refs r := by
  simp [Env.extend, h]
theorem Env.extend_spaces_some (δ : RoutineEnv) (ρ : Env) {σm : List (Name × Space)} (σp : List (Name × Path))
    {m : Name} {t : Space} (h : lookupM σm m = some t) : (Env.extend δ ρ σm σp).spaces m = t.denT δ ρ := by
  simp [Env.extend, h]
theorem Env.extend_spaces_none (δ : RoutineEnv) (ρ : Env) {σm : List (Name × Space)} (σp : List (Name × Path))
    {m : Name} (h : lookupM σm m = none) : (Env.extend δ ρ σm σp).spaces m = ρ.spaces m := by
  simp [Env.extend, h]

/-! ### Lookup, drop and range: the ref-side twins of `Subst.lean`'s lemmas -/

theorem lookupM_dropM_self : ∀ (σ : List (Name × Space)) (b : Name), lookupM (dropM σ b) b = none
  | [], _ => rfl
  | e :: σ, b => by
      simp only [dropM]
      split
      · exact lookupM_dropM_self σ b
      · rename_i hne
        simp only [lookupM, hne, if_false]
        exact lookupM_dropM_self σ b

theorem lookupR_dropR_self : ∀ (σ : List (Name × Path)) (b : Name), lookupR (dropR σ b) b = none
  | [], _ => rfl
  | e :: σ, b => by
      simp only [dropR]
      split
      · exact lookupR_dropR_self σ b
      · rename_i hne
        simp only [lookupR, hne, if_false]
        exact lookupR_dropR_self σ b

theorem lookupR_dropR_ne :
    ∀ (σ : List (Name × Path)) (r b : Name), r ≠ b → lookupR (dropR σ b) r = lookupR σ r
  | [], _, _, _ => rfl
  | e :: σ, r, b, hne => by
      simp only [dropR]
      split
      · rename_i heb
        have : ¬ (e.1 = r) := by rw [heb]; exact fun h => hne h.symm
        simp only [lookupR, this, if_false]
        exact lookupR_dropR_ne σ r b hne
      · simp only [lookupR]
        split
        · rfl
        · exact lookupR_dropR_ne σ r b hne

theorem lookupR_cons_ne (σ : List (Name × Path)) (r b : Name) (v : Path) (hne : r ≠ b) :
    lookupR ((b, v) :: σ) r = lookupR σ r := by
  have : ¬ (b = r) := fun h => hne h.symm
  simp only [lookupR, this, if_false]

theorem freeR_subset_rangeRP :
    ∀ (σ : List (Name × Path)) (r : Name) (p : Path), lookupR σ r = some p → p.freeR ⊆ rangeRP σ
  | [], _, _, h => by simp [lookupR] at h
  | e :: σ, r, p, h => by
      simp only [lookupR] at h
      split at h
      · cases h; simp [rangeRP]
      · exact (freeR_subset_rangeRP σ r p h).trans (by simp [rangeRP])

theorem freeR_subset_rangeRM :
    ∀ (σ : List (Name × Space)) (m : Name) (t : Space), lookupM σ m = some t → t.freeR ⊆ rangeRM σ
  | [], _, _, h => by simp [lookupM] at h
  | e :: σ, m, t, h => by
      simp only [lookupM] at h
      split at h
      · cases h; simp [rangeRM]
      · exact (freeR_subset_rangeRM σ m t h).trans (by simp [rangeRM])

theorem freeR_subset_rangeR_ofM (σm : List (Name × Space)) (σp : List (Name × Path)) (m : Name) (t : Space)
    (h : lookupM σm m = some t) : t.freeR ⊆ rangeR σm σp :=
  (freeR_subset_rangeRM σm m t h).trans (by simp [rangeR])

theorem freeR_subset_rangeR_ofP (σm : List (Name × Space)) (σp : List (Name × Path)) (r : Name) (p : Path)
    (h : lookupR σp r = some p) : p.freeR ⊆ rangeR σm σp :=
  (freeR_subset_rangeRP σp r p h).trans (by simp [rangeR])

/-! ### What a binder decided, as a disjunction -/

theorem bindM_cases (F : FreshSupply) (σm : List (Name × Space)) (σp : List (Name × Path)) (b : Name)
    (avoid : Finset Name) :
    (b ∉ rangeM (dropM σm b) σp ∧ (bindM F σm σp b avoid).1 = b ∧ (bindM F σm σp b avoid).2 = dropM σm b) ∨
    ((bindM F σm σp b avoid).1 ∉ rangeM (dropM σm b) σp ∪ avoid ∧
      (bindM F σm σp b avoid).2 = (b, Space.mention (bindM F σm σp b avoid).1) :: dropM σm b) := by
  unfold bindM
  split
  · right; exact ⟨F.spec _, rfl⟩
  · left; rename_i hnot; exact ⟨hnot, rfl, rfl⟩

theorem bindR_cases (F : FreshSupply) (σm : List (Name × Space)) (σp : List (Name × Path)) (b : Name)
    (avoid : Finset Name) :
    (b ∉ rangeR σm (dropR σp b) ∧ (bindR F σm σp b avoid).1 = b ∧ (bindR F σm σp b avoid).2 = dropR σp b) ∨
    ((bindR F σm σp b avoid).1 ∉ rangeR σm (dropR σp b) ∪ avoid ∧
      (bindR F σm σp b avoid).2 = (b, Path.deref (bindR F σm σp b avoid).1) :: dropR σp b) := by
  unfold bindR
  split
  · right; exact ⟨F.spec _, rfl⟩
  · left; rename_i hnot; exact ⟨hnot, rfl, rfl⟩

/-- a path's denotation ignores space variables (rebinding a mention changes no ref) -/
theorem Path.denT_setM' (ρ : Env) (m : Name) (X : SpaceV) (p : Path) : p.denT (ρ.setM m X) = p.denT ρ :=
  Path.denT_setM ρ m X p

/-- a path whose free refs avoid `n` denotes the same after rebinding `n` -/
theorem Path.denT_setR_of_notFree (ρ : Env) (n : Name) (v : PathV) (p : Path) (h : n ∉ p.freeR) :
    p.denT (ρ.setR n v) = p.denT ρ :=
  Path.denT_congr_rm p (fun r hr => by
    have : r ≠ n := fun heq => h (heq ▸ hr)
    simp [Env.setR, Function.update_of_ne this])

/-- a space whose free refs avoid `n` denotes the same after rebinding `n` -/
theorem Space.denT_setR_of_notFree (δ : RoutineEnv) (s : Space) (ρ : Env) (n : Name) (v : PathV)
    (h : n ∉ s.freeR) : s.denT δ (ρ.setR n v) = s.denT δ ρ :=
  Space.denT_congr_rm δ s _ _ ⟨fun r hr => by
      have : r ≠ n := fun heq => h (heq ▸ hr)
      simp [Env.setR, Function.update_of_ne this], fun _ _ => rfl⟩

/-! ### THE BINDER LEMMAS

Rebinding the (possibly fresh) name a binder chose, then extending by the substitution the body is
descended with, agrees on the body's free names with extending first and rebinding the ORIGINAL name.
This is the semantic content of capture avoidance and shadowing at once. -/

theorem extend_bindM_agree (δ : RoutineEnv) (F : FreshSupply) (σm : List (Name × Space)) (σp : List (Name × Path))
    (b : Name) (avoid : Finset Name) (ρ : Env) (X : SpaceV) (R M : Finset Name) (hM : M ⊆ avoid) :
    Env.AgreeRM R M
      (Env.extend δ (ρ.setM (bindM F σm σp b avoid).1 X) (bindM F σm σp b avoid).2 σp)
      ((Env.extend δ ρ σm σp).setM b X) := by
  set nb := (bindM F σm σp b avoid).1 with hnb
  set σm₂ := (bindM F σm σp b avoid).2 with hσm₂
  clear_value nb σm₂
  refine ⟨fun r _ => ?_, fun m hm => ?_⟩
  · -- refs: the same lookup on both sides, and a path never reads a space variable
    simp only [Env.extend, Env.setM_refs]
    cases lookupR σp r with
    | none => rfl
    | some p => exact Path.denT_setM ρ nb X p
  · rcases bindM_cases F σm σp b avoid with ⟨hnot, h1, h2⟩ | ⟨hfresh, h2⟩
    · -- NOT RENAMED: the binder shadows its own name; other names keep their replacements
      rw [← hnb] at h1; rw [← hσm₂] at h2
      by_cases hmb : m = b
      · subst hmb
        rw [Env.extend_spaces_none δ _ σp (by rw [h2]; exact lookupM_dropM_self σm m), h1]
        simp
      · have hl : lookupM σm₂ m = lookupM σm m := by rw [h2]; exact lookupM_dropM_ne σm m b hmb
        rw [Env.setM_spaces_ne _ _ hmb]
        cases hlm : lookupM σm m with
        | none =>
          rw [Env.extend_spaces_none δ _ σp (hl.trans hlm), Env.extend_spaces_none δ _ σp hlm, h1]
          exact Env.setM_spaces_ne ρ X hmb
        | some t =>
          rw [Env.extend_spaces_some δ _ σp (hl.trans hlm), Env.extend_spaces_some δ _ σp hlm, h1]
          -- `b` is free in no replacement (the `if` was false)
          have hbt : b ∉ t.freeM := fun hin => hnot
            (freeM_subset_rangeM (dropM σm b) σp m t (by rw [lookupM_dropM_ne σm m b hmb]; exact hlm) hin)
          exact Space.denT_setM_of_notFree δ t ρ b X hbt
    · -- RENAMED to a fresh `nb`: `b ↦ mention nb` in the body, `nb` read nowhere else
      rw [← hnb] at hfresh h2
      rw [← hσm₂] at h2
      have hnbR : nb ∉ rangeM (dropM σm b) σp := fun h => hfresh (Finset.mem_union_left _ h)
      have hnbA : nb ∉ avoid := fun h => hfresh (Finset.mem_union_right _ h)
      by_cases hmb : m = b
      · subst hmb
        have hl : lookupM σm₂ m = some (Space.mention nb) := by rw [h2]; simp [lookupM]
        rw [Env.extend_spaces_some δ _ σp hl]
        simp [Space.denT]
      · have hl : lookupM σm₂ m = lookupM σm m := by
          rw [h2, lookupM_cons_ne _ m b _ hmb]; exact lookupM_dropM_ne σm m b hmb
        rw [Env.setM_spaces_ne _ _ hmb]
        have hmnb : m ≠ nb := fun heq => hnbA (heq ▸ hM hm)
        cases hlm : lookupM σm m with
        | none =>
          rw [Env.extend_spaces_none δ _ σp (hl.trans hlm), Env.extend_spaces_none δ _ σp hlm]
          exact Env.setM_spaces_ne ρ X hmnb
        | some t =>
          rw [Env.extend_spaces_some δ _ σp (hl.trans hlm), Env.extend_spaces_some δ _ σp hlm]
          have hnt : nb ∉ t.freeM := fun hin => hnbR
            (freeM_subset_rangeM (dropM σm b) σp m t (by rw [lookupM_dropM_ne σm m b hmb]; exact hlm) hin)
          exact Space.denT_setM_of_notFree δ t ρ nb X hnt

theorem extend_bindR_agree (δ : RoutineEnv) (F : FreshSupply) (σm : List (Name × Space)) (σp : List (Name × Path))
    (b : Name) (avoid : Finset Name) (ρ : Env) (v : PathV) (R M : Finset Name) (hR : R ⊆ avoid) :
    Env.AgreeRM R M
      (Env.extend δ (ρ.setR (bindR F σm σp b avoid).1 v) σm (bindR F σm σp b avoid).2)
      ((Env.extend δ ρ σm σp).setR b v) := by
  set ns := (bindR F σm σp b avoid).1 with hns
  set σp₂ := (bindR F σm σp b avoid).2 with hσp₂
  clear_value ns σp₂
  -- `ns` is outside every replacement's free refs, in both branches
  have hnsR : ns ∉ rangeR σm (dropR σp b) := by
    rcases bindR_cases F σm σp b avoid with ⟨hnot, h1, _⟩ | ⟨hfresh, _⟩
    · rw [← hns] at h1; rw [h1]; exact hnot
    · rw [← hns] at hfresh; exact fun h => hfresh (Finset.mem_union_left _ h)
  refine ⟨fun r hr => ?_, fun m _ => ?_⟩
  · rcases bindR_cases F σm σp b avoid with ⟨hnot, h1, h2⟩ | ⟨hfresh, h2⟩
    · rw [← hns] at h1; rw [← hσp₂] at h2
      by_cases hrb : r = b
      · subst hrb
        rw [Env.extend_refs_none δ _ σm (by rw [h2]; exact lookupR_dropR_self σp r), h1]
        simp [Env.setR]
      · have hl : lookupR σp₂ r = lookupR σp r := by rw [h2]; exact lookupR_dropR_ne σp r b hrb
        simp only [Env.setR]
        rw [Function.update_of_ne hrb]
        cases hlr : lookupR σp r with
        | none =>
          rw [Env.extend_refs_none δ _ σm (hl.trans hlr), Env.extend_refs_none δ _ σm hlr, h1]
          exact Function.update_of_ne hrb _ _
        | some p =>
          rw [Env.extend_refs_some δ _ σm (hl.trans hlr), Env.extend_refs_some δ _ σm hlr, h1]
          have hbp : b ∉ p.freeR := fun hin => hnot
            (freeR_subset_rangeR_ofP σm (dropR σp b) r p (by rw [lookupR_dropR_ne σp r b hrb]; exact hlr) hin)
          exact Path.denT_setR_of_notFree ρ b v p hbp
    · rw [← hns] at hfresh h2
      rw [← hσp₂] at h2
      have hnsA : ns ∉ avoid := fun h => hfresh (Finset.mem_union_right _ h)
      by_cases hrb : r = b
      · subst hrb
        have hl : lookupR σp₂ r = some (Path.deref ns) := by rw [h2]; simp [lookupR]
        rw [Env.extend_refs_some δ _ σm hl]
        simp [Path.denT, Env.setR]
      · have hl : lookupR σp₂ r = lookupR σp r := by
          rw [h2, lookupR_cons_ne _ r b _ hrb]; exact lookupR_dropR_ne σp r b hrb
        simp only [Env.setR]
        rw [Function.update_of_ne hrb]
        have hrns : r ≠ ns := fun heq => hnsA (heq ▸ hR hr)
        cases hlr : lookupR σp r with
        | none =>
          rw [Env.extend_refs_none δ _ σm (hl.trans hlr), Env.extend_refs_none δ _ σm hlr]
          exact Function.update_of_ne hrns _ _
        | some p =>
          rw [Env.extend_refs_some δ _ σm (hl.trans hlr), Env.extend_refs_some δ _ σm hlr]
          have hnp : ns ∉ p.freeR := fun hin => hnsR
            (freeR_subset_rangeR_ofP σm (dropR σp b) r p (by rw [lookupR_dropR_ne σp r b hrb]; exact hlr) hin)
          exact Path.denT_setR_of_notFree ρ ns v p hnp
  · -- spaces: the same lookup on both sides; a replacement never reads the fresh ref
    simp only [Env.extend, Env.setR_spaces]
    cases hlm : lookupM σm m with
    | none => rfl
    | some t =>
      have hnt : ns ∉ t.freeR := fun hin => hnsR (freeR_subset_rangeR_ofM σm (dropR σp b) m t hlm hin)
      exact Space.denT_setR_of_notFree δ t ρ ns v hnt

/-! ### THE THEOREM -/

variable (F : FreshSupply)

mutual

theorem substP_denT (δ : RoutineEnv) :
    ∀ (p : Path) (σm : List (Name × Space)) (σp : List (Name × Path)) (ρ : Env),
      (substP F σm σp p).denT ρ = p.denT (Env.extend δ ρ σm σp)
  | .deref r, σm, σp, ρ => by
      simp only [substP]
      cases h : lookupR σp r with
      | none => simp [Path.denT, Env.extend_refs_none δ ρ σm h]
      | some q => simp [Path.denT, Env.extend_refs_some δ ρ σm h]
  | .const _, _, _, _ => rfl
  | .concat l r, σm, σp, ρ => by
      simp [substP, Path.denT, substP_denT δ l σm σp ρ, substP_denT δ r σm σp ρ]
  | .groundedPP _ _, _, _, _ => rfl
  | .groundedSP _ _, _, _, _ => rfl

theorem substPList_denTs (δ : RoutineEnv) :
    ∀ (ps : List Path) (σm : List (Name × Space)) (σp : List (Name × Path)) (ρ : Env),
      Path.denTs ρ (substPList F σm σp ps) = Path.denTs (Env.extend δ ρ σm σp) ps
  | [], _, _, _ => rfl
  | p :: rest, σm, σp, ρ => by
      simp [substPList, Path.denTs, substP_denT δ p σm σp ρ, substPList_denTs δ rest σm σp ρ]

theorem substList_denTs (δ : RoutineEnv) :
    ∀ (ms : List Space) (σm : List (Name × Space)) (σp : List (Name × Path)) (ρ : Env),
      Space.denTs δ ρ (substList F σm σp ms) = Space.denTs δ (Env.extend δ ρ σm σp) ms
  | [], _, _, _ => rfl
  | s :: rest, σm, σp, ρ => by
      simp [substList, Space.denTs, substS_denT δ s σm σp ρ, substList_denTs δ rest σm σp ρ]

/-- SEMANTIC SUBSTITUTION: substituting into a term denotes evaluating the term in the extended
environment — for every constructor, every substitution, every fresh-name policy. -/
theorem substS_denT (δ : RoutineEnv) :
    ∀ (s : Space) (σm : List (Name × Space)) (σp : List (Name × Path)) (ρ : Env),
      (substS F σm σp s).denT δ ρ = s.denT δ (Env.extend δ ρ σm σp)
  | .empty, _, _, _ => rfl
  | .lit _, _, _, _ => rfl
  | .mention m, σm, σp, ρ => by
      simp only [substS]
      cases h : lookupM σm m with
      | none => simp [Space.denT, Env.extend_spaces_none δ ρ σp h]
      | some t => simp [Space.denT, Env.extend_spaces_some δ ρ σp h]
  | .singleton p, σm, σp, ρ => by simp [substS, Space.denT, substP_denT δ p σm σp ρ]
  | .union x y, σm, σp, ρ => by
      simp [substS, Space.denT, substS_denT δ x σm σp ρ, substS_denT δ y σm σp ρ]
  | .inter x y, σm, σp, ρ => by
      simp [substS, Space.denT, substS_denT δ x σm σp ρ, substS_denT δ y σm σp ρ]
  | .sub x y, σm, σp, ρ => by
      simp [substS, Space.denT, substS_denT δ x σm σp ρ, substS_denT δ y σm σp ρ]
  | .restriction x y, σm, σp, ρ => by
      simp [substS, Space.denT, substS_denT δ x σm σp ρ, substS_denT δ y σm σp ρ]
  | .raffination x y, σm, σp, ρ => by
      simp [substS, Space.denT, substS_denT δ x σm σp ρ, substS_denT δ y σm σp ρ]
  | .composition x y, σm, σp, ρ => by
      simp [substS, Space.denT, substS_denT δ x σm σp ρ, substS_denT δ y σm σp ρ]
  | .wrap s p, σm, σp, ρ => by
      simp [substS, Space.denT, substS_denT δ s σm σp ρ, substP_denT δ p σm σp ρ]
  | .unwrap s p, σm, σp, ρ => by
      simp [substS, Space.denT, substS_denT δ s σm σp ρ, substP_denT δ p σm σp ρ]
  | .tailsUnion s, σm, σp, ρ => by simp [substS, Space.denT, substS_denT δ s σm σp ρ]
  | .tailsInter s, σm, σp, ρ => by simp [substS, Space.denT, substS_denT δ s σm σp ρ]
  | .range x _ _, σm, σp, ρ => by simp [substS, Space.denT]
  | .call r refs ms, σm, σp, ρ => by
      simp [substS, Space.denT, substPList_denTs δ refs σm σp ρ, substList_denTs δ ms σm σp ρ]
  | .iteration src sym rest t, σm, σp, ρ => by
      simp only [substS, Space.denT]
      have hsrc := substS_denT δ src σm σp ρ
      -- the two binders, in the order `substS` resolves them: the ref binder first, the mention
      -- binder against the substitution it produced
      have ht : ∀ (hd : Name) (T : SpaceV),
          (substS F (bindM F σm (bindR F σm σp sym t.freeR).2 rest t.freeM).2 (bindR F σm σp sym t.freeR).2 t).denT δ
              ((ρ.setR (bindR F σm σp sym t.freeR).1 [hd]).setM (bindM F σm (bindR F σm σp sym t.freeR).2 rest t.freeM).1 T)
            = t.denT δ (((Env.extend δ ρ σm σp).setR sym [hd]).setM rest T) := fun hd T => by
        rw [substS_denT δ t _ _ _]
        apply Space.denT_congr_rm δ t
        refine Env.AgreeRM.trans
          (extend_bindM_agree δ F σm (bindR F σm σp sym t.freeR).2 rest t.freeM (ρ.setR (bindR F σm σp sym t.freeR).1 [hd]) T
            t.freeR t.freeM (le_refl _)) ?_
        exact Env.AgreeRM.setM rest
          (extend_bindR_agree δ F σm σp sym t.freeR ρ [hd] t.freeR (t.freeM.erase rest) (le_refl _)) T
      rw [hsrc]
      exact Set.iUnion_congr fun hd => Set.iUnion_congr fun _ => ht hd _
  | .fixpoint i r b, σm, σp, ρ => by
      simp only [substS, Space.denT]
      have hi := substS_denT δ i σm σp ρ
      have hb : ∀ X, (substS F (bindM F σm σp r b.freeM).2 σp b).denT δ (ρ.setM (bindM F σm σp r b.freeM).1 X)
          = b.denT δ ((Env.extend δ ρ σm σp).setM r X) := fun X => by
        rw [substS_denT δ b _ _ _]
        exact Space.denT_congr_rm δ b _ _
          (extend_bindM_agree δ F σm σp r b.freeM ρ X b.freeR b.freeM (le_refl _))
      rw [hi]
      exact Set.iUnion_congr fun n => Kleene.chain_congr (fun X => by simp [fixOp, hb X]) rfl n
  | .fold _ _ _ _ _ _ _, _, _, _ => by simp [substS, Space.denT]
  | .groundedPS _ _, _, _, _ => by simp [substS, Space.denT]
  | .groundedSS _ _, _, _, _ => by simp [substS, Space.denT]

end

/-! ### The side conditions, as corollaries -/

/-- THE FOLD-SITE LEMMA: an instance `c = gc·θ` denotes `gc` under the environment `θ` denotes — the
substitution half of `Supercompile.lean`'s `fix` premise (O12b), now a theorem rather than a
hypothesis. -/
theorem instance_denT (δ : RoutineEnv) (ρ : Env) {c gc : Space} (θm : List (Name × Space))
    (θp : List (Name × Path)) (h : c = substS F θm θp gc) :
    c.denT δ ρ = gc.denT δ (Env.extend δ ρ θm θp) := by
  subst h; exact substS_denT F δ gc θm θp ρ

/-- ALPHA-RENAMING a `Fixpoint`'s bound name to one not free in its body preserves the denotation -/
theorem fixpoint_alpha (δ : RoutineEnv) (ρ : Env) (i b : Space) (r r' : Name) (hfresh : r' ∉ b.freeM) :
    (Space.fixpoint i r' (substS F [(r, Space.mention r')] [] b)).denT δ ρ
      = (Space.fixpoint i r b).denT δ ρ := by
  simp only [Space.denT]
  have hb : ∀ X, (substS F [(r, Space.mention r')] [] b).denT δ (ρ.setM r' X) = b.denT δ (ρ.setM r X) := fun X => by
    rw [substS_denT F δ b _ _ _]
    apply Space.denT_congr_rm δ b
    refine ⟨fun x _ => ?_, fun m hm => ?_⟩
    · simp [Env.extend, lookupR, Env.setM_refs]
    · by_cases hmr : m = r
      · subst hmr
        simp [Env.extend, lookupM, Space.denT]
      · have hmr' : m ≠ r' := fun heq => hfresh (heq ▸ hm)
        have hrm : ¬ (r = m) := fun h => hmr h.symm
        have hl : lookupM [(r, Space.mention r')] m = none := by simp [lookupM, hrm]
        rw [Env.extend_spaces_none δ _ _ hl, Env.setM_spaces_ne _ _ hmr', Env.setM_spaces_ne _ _ hmr]
  exact Set.iUnion_congr fun n =>
    Kleene.chain_congr (F := fixOp (i.denT δ ρ) fun X => (substS F [(r, Space.mention r')] [] b).denT δ (ρ.setM r' X))
      (fun X => by simp [fixOp, hb X]) rfl n

/-- SHADOWING: a substitution for a `Fixpoint`'s own bound name does not enter its body -/
theorem fixpoint_shadow (i b t : Space) (r : Name) :
    substS F [(r, t)] [] (Space.fixpoint i r b) = Space.fixpoint (substS F [(r, t)] [] i) r b := by
  simp [substS, bindM, dropM, rangeM, rangeMM, rangeMP, substS_nil]

/-- SHADOWING at an `Iteration`: substitutions for its two bound names do not enter its templates
(when the mention's replacement does not mention the ref binder — otherwise the ref binder is
alpha-renamed, which `substS_denT` covers) -/
theorem iteration_shadow (src t x : Space) (p : Path) (sym rest : Name) (hx : sym ∉ x.freeR) :
    substS F [(rest, x)] [(sym, p)] (Space.iteration src sym rest t)
      = Space.iteration (substS F [(rest, x)] [(sym, p)] src) sym rest t := by
  simp [substS, bindR, bindM, dropR, dropM, rangeR, rangeRM, rangeRP, rangeM, rangeMM, rangeMP, hx, substS_nil]

end Zippy
