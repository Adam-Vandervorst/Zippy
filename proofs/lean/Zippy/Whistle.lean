/-
==================================================================================================
THE WHISTLE IS A WELL-QUASI-ORDER  — KRUSKAL'S TREE THEOREM FROM HIGMAN'S LEMMA.

`docs/TRUSTED.md` T3 / `terminating/REGISTRY.tsv` O12d: "the homeomorphic embedding on the
configuration signature is a well-quasi-order, hence driving terminates."  ADMITTED, because the
standard proof is Kruskal's tree theorem and there was no checked library boundary to import it
from. The toolchain probe — "Kruskal in Mathlib; otherwise prove it from
Higman" — was answered by `scripts/check_lean.sh --probe-kruskal` on 2026-09-04:
Mathlib has HIGMAN'S LEMMA (`Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`) and
the minimal-bad-sequence machinery it is proved with, and does NOT have Kruskal (its `Kruskal` files
are Kruskal–Katona, a shadow theorem). This file therefore supplies the proof from Higman's lemma.

==THE THEOREM==
`Emb r` is homeomorphic embedding on finitely branching trees over a label type `L` with a relation
`r` on labels: `a ⊴ b` when `a` embeds into a child of `b` (DIVE), or the roots are `r`-related and
the children embed pointwise (COUPLE).  `kruskal` proves: if `r` is a well-quasi-order on `L`, and
`r` respects arity, then `Emb r` is a well-quasi-order on trees — every infinite sequence of trees
has `i < j` with `tᵢ ⊴ tⱼ`.  That is exactly the statement the whistle needs: along any infinite
driving path some ancestor embeds in a descendant, so the whistle blows and the path is cut off by
generalization.  Termination of the implemented transition system is `whistle_terminates`.

COUPLE IS POINTWISE (`List.Forall₂`), NOT SUBSEQUENCE (`List.SublistForall₂`), because that is what
`Matching.embedsS` does: `coupledS(a, b) && childrenS(a).lazyZip(childrenS(b)).forall(embed)`.
The standard Kruskal statement couples along a subsequence of the children; the two agree when the
label determines the arity, which is the `harity` hypothesis below, and MORKL's signature has it:
every constructor has a fixed arity except `Call`, whose label carries both argument counts.

==THE ALPHABET — what 2E.3's "decide and engineer each" decided==
Kruskal needs the LABEL relation to be a WQO.  Over a finite alphabet, equality is one
(`Finite.wellQuasiOrdered`).  `Matching.coupledS`/`coupledP` as they stood compared four things by
an equality over an UNBOUNDED set, so the relation was not a WQO at all — an infinite antichain was
easy to write (nested `Iteration`s whose innermost `Mention` carries a different canonical bound
name at each depth).  `Matching.labelOf` (Supercompiler.scala) now fixes the alphabet, and this file
mirrors it in `Label`:

  * `Mention` / `Deref` — ONE label each, for every variable, bound or free.  Two variables of a
    sort always couple.  (Was: canonical bound names compared by equality.)
  * `Call` — the ORIGINAL routine's name plus both arities.  A residual name `f_sc7` is labelled by
    its base `f`, so driving cannot mint new labels.  (Was: the full `RoutinePtr`.)
  * `Literal` / `Constant` — one atom each (`litAtoms = true`, the default and the one this theorem
    covers).  With `litAtoms = false` they are labelled by value and the alphabet is not finite.
  * `Range` — its bounds.  Finite per run only because no law manufactures new bounds, which is what
    `SC.State.alphabetWithin` checks at run time (every label seen during the drive is a label of
    the input program or its routine table).
  * `Grounded*` — the closure's identity.  Finite per run for the same reason.

So the theorem is applied PER RUN to the finite label set `Λ₀` of the inputs, and the executable
invariant is that the drive never left `Λ₀`.  `WhistleTrace.lean` (GENERATED, `Matching.toLabel`)
re-checks the Scala `embeds` verdicts against `embedsS` below on the pairs a run actually compared.

    proofs/lean/Zippy/Whistle.lean#Zippy.Whistle.kruskal
    proofs/lean/Zippy/Whistle.lean#Zippy.Whistle.whistle_terminates
==================================================================================================
-/
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.WellQuasiOrder
import Mathlib.Data.List.Forall2
import Zippy.Syntax

namespace Zippy.Whistle

/-! ### Finitely branching trees and homeomorphic embedding -/

/-- a finitely branching tree with labels in `L` -/
inductive Tree (L : Type*) where
  | node (label : L) (kids : List (Tree L))

variable {L : Type*}

namespace Tree

def label : Tree L → L
  | node l _ => l
def kids : Tree L → List (Tree L)
  | node _ ks => ks

/-- the number of nodes -/
def size : Tree L → ℕ
  | node _ ks => 1 + sizes ks
where
  sizes : List (Tree L) → ℕ
    | [] => 0
    | t :: ts => size t + sizes ts

theorem size_pos : ∀ t : Tree L, 0 < t.size
  | node _ _ => by simp only [size]; omega

theorem sizes_ge_of_mem : ∀ {ks : List (Tree L)} {t : Tree L}, t ∈ ks → t.size ≤ size.sizes ks
  | k :: rest, t, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp [size.sizes]
      · simp only [size.sizes]
        exact Nat.le_add_left _ _ |>.trans' (sizes_ge_of_mem h)

/-- a child is strictly smaller -/
theorem size_lt_of_mem_kids {t : Tree L} {c : Tree L} (h : c ∈ t.kids) : c.size < t.size := by
  cases t with
  | node l ks =>
    simp only [kids] at h
    simp only [size]
    have := sizes_ge_of_mem h
    omega

end Tree

/-- HOMEOMORPHIC EMBEDDING: dive into a child, or couple the roots and embed the children
pointwise.  `Matching.embedsS`'s `dive || couple`. -/
inductive Emb (r : L → L → Prop) : Tree L → Tree L → Prop
  | dive {a : Tree L} {l : L} {ks : List (Tree L)} {c : Tree L} (hc : c ∈ ks) (h : Emb r a c) :
      Emb r a (.node l ks)
  | couple {l l' : L} {ks ks' : List (Tree L)} (hl : r l l') (h : List.Forall₂ (Emb r) ks ks') :
      Emb r (.node l ks) (.node l' ks')

theorem Emb.refl (r : L → L → Prop) [Std.Refl r] : ∀ t : Tree L, Emb r t t
  | .node l ks => Emb.couple (Std.Refl.refl l) (refl_kids ks)
where
  refl_kids : ∀ ks : List (Tree L), List.Forall₂ (Emb r) ks ks
    | [] => List.Forall₂.nil
    | k :: rest => List.Forall₂.cons (Emb.refl r k) (refl_kids rest)

/-- embedding into a child embeds into the parent -/
theorem Emb.of_mem_kids {r : L → L → Prop} {a c t : Tree L} (hc : c ∈ t.kids) (h : Emb r a c) :
    Emb r a t := by
  cases t with
  | node l ks => exact Emb.dive hc h

/-- a child embeds into its parent -/
theorem Emb.kid_le (r : L → L → Prop) [Std.Refl r] {c t : Tree L} (hc : c ∈ t.kids) : Emb r c t :=
  Emb.of_mem_kids hc (Emb.refl r c)

/-- a member of the left list of a `Forall₂` has a related member on the right -/
theorem forall₂_exists_of_mem_left {α β : Type*} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {a : α}, a ∈ as → ∃ b ∈ bs, R a b
  | _, _, .nil, a, h => by simp at h
  | _, _, .cons hab hrest, a, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨_, List.mem_cons_self, hab⟩
      · obtain ⟨b, hb, hr⟩ := forall₂_exists_of_mem_left hrest h
        exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- pointwise transitivity, given transitivity at every member of the third list -/
theorem forall₂_trans_of {α : Type*} {R : α → α → Prop} :
    ∀ {ks as bs : List α}, (∀ k ∈ ks, ∀ a b, R a b → R b k → R a k) →
      List.Forall₂ R as bs → List.Forall₂ R bs ks → List.Forall₂ R as ks
  | [], _, _, _, h1, h2 => by cases h2; cases h1; exact List.Forall₂.nil
  | k :: rest, _, _, H, h1, h2 => by
      cases h2 with
      | cons hbk hrest =>
        cases h1 with
        | cons hab hrest' =>
          exact List.Forall₂.cons (H k List.mem_cons_self _ _ hab hbk)
            (forall₂_trans_of (fun k' hk' => H k' (List.mem_cons_of_mem _ hk')) hrest' hrest)

/-- TRANSITIVITY, by strong induction on the size of the third tree.  The one non-trivial case is
couple-then-dive: `a` couples with `b`, and `b` dives into a child `c'` of `c`; then `a` embeds into
`c'` by the induction hypothesis (on `c'`, which is smaller than `c`), so `a` dives into `c`. -/
theorem Emb.trans (r : L → L → Prop) [IsTrans L r] :
    ∀ (c a b : Tree L), Emb r a b → Emb r b c → Emb r a c := by
  suffices H : ∀ n, ∀ c : Tree L, c.size ≤ n → ∀ a b, Emb r a b → Emb r b c → Emb r a c from
    fun c => H c.size c le_rfl
  intro n
  induction n with
  | zero => intro c hc; exact absurd (Tree.size_pos c) (by omega)
  | succ n ih =>
    intro c hc a b hab hbc
    cases c with
    | node l ks =>
      have hkid : ∀ k ∈ ks, k.size ≤ n := fun k hk => by
        have := Tree.size_lt_of_mem_kids (t := .node l ks) (by simpa [Tree.kids] using hk)
        omega
      cases hbc with
      | dive hc' h =>
        exact Emb.dive hc' (ih _ (hkid _ hc') a b hab h)
      | couple hl h =>
        cases hab with
        | dive hcb hab' =>
          obtain ⟨c', hc', hbc'⟩ := forall₂_exists_of_mem_left h hcb
          exact Emb.dive hc' (ih c' (hkid _ hc') a _ hab' hbc')
        | couple hl' h' =>
          exact Emb.couple (_root_.trans hl' hl)
            (forall₂_trans_of (fun k hk a b => ih k (hkid k hk) a b) h' h)

instance Emb.isPreorder (r : L → L → Prop) [Std.Refl r] [IsTrans L r] : IsPreorder (Tree L) (Emb r) where
  refl := Emb.refl r
  trans := fun a b c hab hbc => Emb.trans r c a b hab hbc


/-- coupling stated on the projections, for trees not in constructor form -/
theorem Emb.couple' {r : L → L → Prop} {a b : Tree L} (hl : r a.label b.label)
    (h : List.Forall₂ (Emb r) a.kids b.kids) : Emb r a b := by
  cases a; cases b
  exact Emb.couple hl h

/-! ### Well-formed trees: the label determines the arity -/

/-- every node has exactly `ar label` children, and every label is drawn from the alphabet `S` -/
inductive WF (ar : L → ℕ) (S : Set L) : Tree L → Prop
  | node {l : L} {ks : List (Tree L)} (hl : l ∈ S) (hlen : ks.length = ar l) (hks : ∀ k ∈ ks, WF ar S k) :
      WF ar S (.node l ks)

theorem WF.kids_length {ar : L → ℕ} {S : Set L} {t : Tree L} (h : WF ar S t) :
    t.kids.length = ar t.label := by
  cases h; simpa [Tree.kids, Tree.label]

theorem WF.label_mem {ar : L → ℕ} {S : Set L} {t : Tree L} (h : WF ar S t) : t.label ∈ S := by
  cases h; simpa [Tree.label]

theorem WF.of_mem_kids {ar : L → ℕ} {S : Set L} {t c : Tree L} (h : WF ar S t) (hc : c ∈ t.kids) :
    WF ar S c := by
  cases h with
  | node _ _ hks => exact hks c (by simpa [Tree.kids] using hc)

/-- a subsequence embedding between lists of EQUAL length is a pointwise embedding -/
theorem forall₂_of_sublistForall₂_of_length {α β : Type*} {R : α → β → Prop} {l₁ : List α}
    {l₂ : List β} (h : List.SublistForall₂ R l₁ l₂) (hlen : l₁.length = l₂.length) :
    List.Forall₂ R l₁ l₂ := by
  obtain ⟨l, hf, hs⟩ := List.sublistForall₂_iff.mp h
  have : l = l₂ := hs.eq_of_length (by rw [← hf.length_eq, hlen])
  exact this ▸ hf

/-! ### KRUSKAL'S TREE THEOREM, from Higman's lemma by Nash-Williams' minimal bad sequence

Suppose a bad sequence of well-formed trees exists.  Take a MINIMAL one, `f` (Mathlib's
`iff_not_exists_isMinBadSeq`, with `Tree.size` as the rank).  Then:

  1. THE CHILDREN ARE WELL-QUASI-ORDERED.  A bad sequence `g` of children, `g i ∈ kids (f (φ i))`,
     spliced into `f` at the smallest parent index `n₀ = φ i₀` — `f 0, …, f (n₀-1), g i₀, g (i₀+1), …`
     — is again bad (a child embedding into a later parent would embed into the parent by `dive`),
     agrees with `f` below `n₀`, and is strictly smaller at `n₀`.  That contradicts minimality.
  2. HIGMAN: the children LISTS are therefore well-quasi-ordered under subsequence embedding.
  3. RAMSEY: pass to a subsequence along which the labels are `r`-monotone
     (`WellQuasiOrdered.exists_monotone_subseq`), then apply 2 to the children lists along it: some
     `m < n` has `r`-related labels AND subsequence-embedded children.
  4. ARITY: the labels are related, so the arities agree, so the children lists have equal length,
     so the subsequence embedding is pointwise — and `f (φ m)` COUPLES with `f (φ n)`, contradicting
     badness of `f`. -/
theorem kruskal (r : L → L → Prop) [IsPreorder L r] (S : Set L) (hr : S.PartiallyWellOrderedOn r)
    (ar : L → ℕ) (harity : ∀ l l', r l l' → ar l = ar l') :
    {t : Tree L | WF ar S t}.PartiallyWellOrderedOn (Emb r) := by
  classical
  rw [Set.PartiallyWellOrderedOn.iff_not_exists_isMinBadSeq Tree.size]
  rintro ⟨f, hf, hmin⟩
  -- ---- 1. the children of the minimal bad sequence are well-quasi-ordered ----
  let C : Set (Tree L) := {c | ∃ n, c ∈ (f n).kids}
  have hCwf : ∀ c ∈ C, WF ar S c := fun c ⟨n, hn⟩ => WF.of_mem_kids (hf.1 n) hn
  have hC : C.PartiallyWellOrderedOn (Emb r) := by
    rw [Set.partiallyWellOrderedOn_iff_exists_lt]
    intro g hg
    by_contra hbad
    push Not at hbad
    choose φ hφ using hg
    -- the smallest parent index and a child that attains it
    have hex : ∃ k, ∃ i, φ i = k := ⟨φ 0, 0, rfl⟩
    obtain ⟨i₀, hi₀⟩ := Nat.find_spec hex
    have hleast : ∀ i, Nat.find hex ≤ φ i := fun i => Nat.find_min' hex ⟨i, rfl⟩
    set n₀ := Nat.find hex with hn₀
    -- the spliced sequence
    let h : ℕ → Tree L := fun m => if m < n₀ then f m else g (m - n₀ + i₀)
    have hagree : ∀ m, m < n₀ → f m = h m := fun m hm => by simp [h, hm]
    have hafter : ∀ m, n₀ ≤ m → h m = g (m - n₀ + i₀) := fun m hm => by
      simp [h, not_lt.mpr hm]
    have hbadseq : Set.PartiallyWellOrderedOn.IsBadSeq (Emb r) {t | WF ar S t} h := by
      refine ⟨fun m => ?_, fun m n hmn => ?_⟩
      · by_cases hm : m < n₀
        · rw [← hagree m hm]; exact hf.1 m
        · rw [hafter m (not_lt.mp hm)]; exact hCwf _ ⟨_, hφ _⟩
      · by_cases hm : m < n₀
        · by_cases hn : n < n₀
          · rw [← hagree m hm, ← hagree n hn]; exact hf.2 m n hmn
          · rw [← hagree m hm, hafter n (not_lt.mp hn)]
            intro hemb
            -- `f m` embeds into a child of `f (φ k)`, hence into `f (φ k)`, with `m < φ k`
            have hk := hφ (n - n₀ + i₀)
            have hlt : m < φ (n - n₀ + i₀) := lt_of_lt_of_le hm (hleast _)
            exact hf.2 m _ hlt (Emb.of_mem_kids hk hemb)
        · have hn : ¬ n < n₀ := fun hn => hm (hmn.trans hn)
          rw [hafter m (not_lt.mp hm), hafter n (not_lt.mp hn)]
          exact hbad _ _ (by omega)
    have hsmall : (h n₀).size < (f n₀).size := by
      rw [hafter n₀ le_rfl, Nat.sub_self, Nat.zero_add]
      exact Tree.size_lt_of_mem_kids (hi₀ ▸ hφ i₀)
    exact hmin n₀ h hagree hsmall hbadseq
  -- ---- 2. Higman on the children lists ----
  have hL := hC.partiallyWellOrderedOn_sublistForall₂ (Emb r)
  rw [Set.partiallyWellOrderedOn_iff_exists_lt] at hL
  -- ---- 3. a label-monotone subsequence ----
  obtain ⟨φ, hφ⟩ := hr.exists_monotone_subseq (f := fun n => (f n).label) (fun n => (hf.1 n).label_mem)
  obtain ⟨m, n, hmn, hsub⟩ := hL (fun k => (f (φ k)).kids) (fun k x hx => ⟨φ k, hx⟩)
  -- ---- 4. equal arities, hence a coupling ----
  have hlen : (f (φ m)).kids.length = (f (φ n)).kids.length := by
    rw [(hf.1 _).kids_length, (hf.1 _).kids_length]
    exact harity _ _ (hφ m n hmn.le)
  have hemb : Emb r (f (φ m)) (f (φ n)) :=
    Emb.couple' (hφ m n hmn.le) (forall₂_of_sublistForall₂_of_length hsub hlen)
  exact hf.2 (φ m) (φ n) (φ.strictMono hmn) hemb

/-- the same, as the statement the whistle uses: EVERY infinite sequence of well-formed
configurations has an ancestor that embeds into a descendant -/
theorem exists_embed (r : L → L → Prop) [IsPreorder L r] (S : Set L) (hr : S.PartiallyWellOrderedOn r)
    (ar : L → ℕ) (harity : ∀ l l', r l l' → ar l = ar l') (f : ℕ → Tree L) (hf : ∀ n, WF ar S (f n)) :
    ∃ i j, i < j ∧ Emb r (f i) (f j) :=
  (Set.partiallyWellOrderedOn_iff_exists_lt.mp (kruskal r S hr ar harity)) f hf

/-- the unrestricted form: a well-quasi-ordered label TYPE -/
theorem kruskal_univ (r : L → L → Prop) [IsPreorder L r] (hr : WellQuasiOrdered r)
    (ar : L → ℕ) (harity : ∀ l l', r l l' → ar l = ar l') :
    {t : Tree L | WF ar Set.univ t}.PartiallyWellOrderedOn (Emb r) :=
  kruskal r Set.univ (Set.partiallyWellOrderedOn_univ_iff.mpr hr) ar harity

/-! ### Termination of the implemented transition system

The driver keeps the PATH of configurations from the root to the current node and, before creating
a node for configuration `c`, asks whether some ancestor embeds into `c`
(`path.collectFirst { case (pc, _) if Matching.embeds(pc, c, …) }`).  If none does, `c` is appended
and driving continues below it.  So the transition system whose termination is at stake extends a
whistle-free path by one configuration at a time: `BadExt q p` says `q` is `p` plus one more
well-formed configuration that no member of `p` embeds into.  Its well-foundedness says every
whistle-free path is finite — an infinite one would be an infinite bad sequence, which `kruskal`
forbids.  (Finite branching, and hence a finite process tree, is `Config.maxNodes`' business and the
finiteness of `childrenS`; the whistle's job is the depth, which is this.) -/

/-- extend a whistle-free path by one configuration -/
def BadExt (r : L → L → Prop) (ar : L → ℕ) (S : Set L) (q p : List (Tree L)) : Prop :=
  ∃ t, WF ar S t ∧ (∀ s ∈ p, ¬ Emb r s t) ∧ q = p ++ [t]

theorem whistle_terminates (r : L → L → Prop) [IsPreorder L r] (S : Set L) (hr : S.PartiallyWellOrderedOn r)
    (ar : L → ℕ) (harity : ∀ l l', r l l' → ar l = ar l') :
    WellFounded (BadExt r ar S) := by
  classical
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨e, hp⟩ => ?_⟩
  -- `e (n+1)` extends `e n` by `t n`
  choose t ht using hp
  -- `t i` is on every later path
  have hmem : ∀ i j, i < j → t i ∈ e j := by
    intro i j hij
    induction j with
    | zero => exact absurd hij (Nat.not_lt_zero _)
    | succ j ih =>
      rw [(ht j).2.2]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact List.mem_append_left _ (ih h)
      · subst h; exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨i, j, hij, hemb⟩ := exists_embed r S hr ar harity t (fun n => (ht n).1)
  exact (ht j).2.1 (t i) (hmem i j hij) hemb


/-! ### The alphabet, and the executable embedding it labels

`Label` is `Matching.Label` (Supercompiler.scala) constructor for constructor; `embedsB` is
`Matching.embedsS`/`embedsP` on label trees — dive or couple, coupling by label EQUALITY and pointwise
on the children.  `embedsB_iff` says the executable relation IS `Emb (· = ·)`, so `kruskal` applies to
what the Scala computes; `WhistleTrace.lean` (GENERATED by `Matching.toLabel`) re-checks the Scala
verdicts on the pairs a run compared against `embedsB`. -/

inductive Label where
  | ctor (name : String)
  | litAtom | litVal | constAtom | constVal
  | mentionVar | derefVar
  | call (base : String) (refs mentions : Nat)
  | range (lo hi : Int)
  | grounded (kind : String)
  deriving DecidableEq, Repr

/-! `Matching.embedsS`, on label trees: dive into a child, or couple by equal labels and embed the
children pointwise (`lazyZip(...).forall`, which is `false` on unequal lengths). -/
mutual
def embedsB (a b : Tree Label) : Bool :=
  match a, b with
  | .node l' ks', .node l ks =>
      ks.attach.any (fun ⟨c, _⟩ => embedsB (.node l' ks') c) || (decide (l' = l) && zipAll ks' ks)
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
def zipAll (xs ys : List (Tree Label)) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => embedsB x y && zipAll xs' ys'
  | _, _ => false
termination_by sizeOf xs + sizeOf ys
decreasing_by
  all_goals simp_wf
  all_goals omega
end


/-- inversion of `Emb` at two nodes: dive into a child, or couple -/
theorem Emb.node_iff {r : L → L → Prop} (l' l : L) (ks' ks : List (Tree L)) :
    Emb r (.node l' ks') (.node l ks) ↔
      (∃ c ∈ ks, Emb r (.node l' ks') c) ∨ (r l' l ∧ List.Forall₂ (Emb r) ks' ks) := by
  constructor
  · intro h
    cases h with
    | dive hc h => exact Or.inl ⟨_, hc, h⟩
    | couple hl h => exact Or.inr ⟨hl, h⟩
  · rintro (⟨c, hc, h⟩ | ⟨hl, h⟩)
    · exact Emb.dive hc h
    · exact Emb.couple hl h

/-- THE CORRESPONDENCE: the executable embedding is the relation the theorem is about.  Strong
induction on the combined size, mirroring the recursion of `embedsB`/`zipAll`. -/
theorem embedsB_iff_aux : ∀ n : ℕ,
    (∀ a b : Tree Label, sizeOf a + sizeOf b ≤ n → (embedsB a b = true ↔ Emb (· = ·) a b)) ∧
    (∀ xs ys : List (Tree Label), sizeOf xs + sizeOf ys ≤ n →
      (zipAll xs ys = true ↔ List.Forall₂ (Emb (· = ·)) xs ys)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun a b h => ?_, fun xs ys h => ?_⟩
    · cases a; cases b; simp at h
    · cases xs <;> cases ys <;> simp at h
  | succ n ih =>
    refine ⟨fun a b hab => ?_, fun xs ys hxy => ?_⟩
    · cases a with
      | node l' ks' =>
        cases b with
        | node l ks =>
          rw [embedsB, Emb.node_iff]
          simp only [Bool.or_eq_true, List.any_eq_true, List.mem_attach, true_and, Subtype.exists,
                     exists_prop, Bool.and_eq_true, decide_eq_true_eq]
          have hks : sizeOf ks' + sizeOf ks ≤ n := by
            simp only [Tree.node.sizeOf_spec] at hab; omega
          rw [(ih.2 ks' ks hks)]
          constructor
          · rintro (⟨c, hc, h⟩ | ⟨hl, h⟩)
            · have hc' : sizeOf (Tree.node l' ks') + sizeOf c ≤ n := by
                have := List.sizeOf_lt_of_mem hc
                simp only [Tree.node.sizeOf_spec] at hab ⊢; omega
              exact Or.inl ⟨c, hc, (ih.1 _ _ hc').mp h⟩
            · exact Or.inr ⟨hl, h⟩
          · rintro (⟨c, hc, h⟩ | ⟨hl, h⟩)
            · have hc' : sizeOf (Tree.node l' ks') + sizeOf c ≤ n := by
                have := List.sizeOf_lt_of_mem hc
                simp only [Tree.node.sizeOf_spec] at hab ⊢; omega
              exact Or.inl ⟨c, hc, (ih.1 _ _ hc').mpr h⟩
            · exact Or.inr ⟨hl, h⟩
    · cases xs with
      | nil =>
        cases ys with
        | nil => simp [zipAll]
        | cons y ys => simp [zipAll]
      | cons x xs =>
        cases ys with
        | nil => simp [zipAll]
        | cons y ys =>
          rw [zipAll]
          simp only [Bool.and_eq_true, List.forall₂_cons]
          have h1 : sizeOf x + sizeOf y ≤ n := by
            simp only [List.cons.sizeOf_spec] at hxy; omega
          have h2 : sizeOf xs + sizeOf ys ≤ n := by
            simp only [List.cons.sizeOf_spec] at hxy; omega
          rw [ih.1 x y h1, ih.2 xs ys h2]

theorem embedsB_iff (a b : Tree Label) : embedsB a b = true ↔ Emb (· = ·) a b :=
  (embedsB_iff_aux _).1 a b le_rfl

/-- and over a FINITE label alphabet — every run's, by `SC.State.alphabetEscapes` — the EXECUTABLE
whistle is a well-quasi-order: `kruskal` at `r := (· = ·)` on the alphabet, transported along
`embedsB_iff`.  `harity` is immediate: a label's arity is a function of the label. -/
theorem embedsB_wqo (Λ : Finset Label) (ar : Label → ℕ) :
    {t : Tree Label | WF ar (↑Λ : Set Label) t}.PartiallyWellOrderedOn
      (fun a b => embedsB a b = true) := by
  have hΛ : (↑Λ : Set Label).PartiallyWellOrderedOn (· = ·) :=
    (Λ.finite_toSet).partiallyWellOrderedOn
  have hk := kruskal (L := Label) (· = ·) (↑Λ) hΛ ar (fun l l' h => by rw [h])
  rw [Set.partiallyWellOrderedOn_iff_exists_lt] at hk ⊢
  intro f hf
  obtain ⟨m, n, hmn, h⟩ := hk f hf
  exact ⟨m, n, hmn, (embedsB_iff _ _).mpr h⟩

/-- the executable whistle terminates on every run whose configurations stay inside its alphabet -/
theorem embedsB_terminates (Λ : Finset Label) (ar : Label → ℕ) :
    WellFounded (BadExt (· = ·) ar (↑Λ : Set Label)) :=
  whistle_terminates (· = ·) (↑Λ) (Λ.finite_toSet).partiallyWellOrderedOn ar (fun l l' h => by rw [h])

end Zippy.Whistle
