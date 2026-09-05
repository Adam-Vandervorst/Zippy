/-
==================================================================================================
THE RESOURCE DOMAIN'S ARITHMETIC, ORDER, RANGE NORMALISATION AND WIDENING (tasks.md A6).

The A4 analysis (`SpatialCostSemantics.scala`) reports every event count as an INTERVAL `Ivl(lo, hi)`
with `hi` possibly infinite (`Ivl.INF`), combines intervals by `add`, `mul` (repetition), `hull`
(alternatives) and `scale`, orders them by containment, normalises `Range` windows by
`RangeBounds.normalize`, and iterates fixpoints with a widening that must be an upper bound of both
its arguments.  These are the lemmas the transfer rules stand on; they are stated over ℕ with `WithTop ℕ`
for the upper endpoint, which is the meaning of the saturating `Long` arithmetic in `Ivl.add`/`Ivl.mul`
(a sum or product that leaves the representable range is reported as `INF`, i.e. `⊤`, which is the
sound direction for an UPPER endpoint).  The implementation-correspondence boundary — that the Scala
`Long` code computes these functions below `2^63` and `⊤` above — is a registry premise
(`proofs/spatial/REGISTRY.tsv` A6-IVL), not a theorem here.

  Ivl        — membership, `add`, `mul`, `hull`, the containment order, repetition (`sum_mem`),
               alternatives (`mem_foldl_hull`), and the MUST/MAY rule: a lower endpoint below every
               admitted execution and an upper endpoint above every one contain them all.
  Range      — `RangeBounds.normalize` transcribed, with its window inside `[0, size]` and the length
               of the slice it selects.
  widen      — a widening that dominates the join is an upper bound of both arguments.
  exhaustive — the finite-model principle the independent checker (`proofs/spatial/check_transfers.py`)
               instantiates: a decidable property with no counterexample on a finite universe holds on it.
-/
import Mathlib

namespace Zippy
namespace Spatial

/-- an interval of counts: an exact lower endpoint and a possibly infinite upper one -/
structure Ivl where
  lo : ℕ
  hi : WithTop ℕ

namespace Ivl

/-- `n ∈ γ(i)` -/
def mem (n : ℕ) (i : Ivl) : Prop := i.lo ≤ n ∧ (n : WithTop ℕ) ≤ i.hi

/-- sequential composition: the counts add -/
def add (i j : Ivl) : Ivl := ⟨i.lo + j.lo, i.hi + j.hi⟩
/-- repetition / independent products: the counts multiply -/
def mul (i j : Ivl) : Ivl := ⟨i.lo * j.lo, i.hi * j.hi⟩
/-- alternatives: the hull -/
def hull (i j : Ivl) : Ivl := ⟨min i.lo j.lo, max i.hi j.hi⟩
/-- the containment order: `i ⊑ j` when γ(i) ⊆ γ(j) -/
def leq (i j : Ivl) : Prop := j.lo ≤ i.lo ∧ i.hi ≤ j.hi

theorem mem_add {a b : ℕ} {i j : Ivl} (ha : mem a i) (hb : mem b j) : mem (a + b) (add i j) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  refine ⟨Nat.add_le_add h1 h3, ?_⟩
  simp only [add]
  push_cast
  exact add_le_add h2 h4

theorem mem_mul {a b : ℕ} {i j : Ivl} (ha : mem a i) (hb : mem b j) : mem (a * b) (mul i j) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  refine ⟨Nat.mul_le_mul h1 h3, ?_⟩
  simp only [mul]
  push_cast
  exact mul_le_mul' h2 h4

theorem mem_hull_left {a : ℕ} {i j : Ivl} (h : mem a i) : mem a (hull i j) :=
  ⟨le_trans (min_le_left _ _) h.1, le_trans h.2 (le_max_left _ _)⟩

theorem mem_hull_right {a : ℕ} {i j : Ivl} (h : mem a j) : mem a (hull i j) :=
  ⟨le_trans (min_le_right _ _) h.1, le_trans h.2 (le_max_right _ _)⟩

/-- the order is containment -/
theorem leq_mem {a : ℕ} {i j : Ivl} (hij : leq i j) (h : mem a i) : mem a j :=
  ⟨le_trans hij.1 h.1, le_trans h.2 hij.2⟩

theorem leq_refl (i : Ivl) : leq i i := ⟨le_refl _, le_refl _⟩

theorem leq_trans {i j k : Ivl} (h1 : leq i j) (h2 : leq j k) : leq i k :=
  ⟨le_trans h2.1 h1.1, le_trans h1.2 h2.2⟩

/-- the hull is an upper bound of both arguments in the order -/
theorem leq_hull_left (i j : Ivl) : leq i (hull i j) := ⟨min_le_left _ _, le_max_left _ _⟩
theorem leq_hull_right (i j : Ivl) : leq j (hull i j) := ⟨min_le_right _ _, le_max_right _ _⟩

/-- REPETITION: `k` executions each inside `i` sum into `mul ⟨k, k⟩ i` (the `scale` rule) -/
theorem sum_mem (l : List ℕ) (i : Ivl) (h : ∀ x ∈ l, mem x i) :
    mem l.sum (mul ⟨l.length, l.length⟩ i) := by
  induction l with
  | nil => simp [mem, mul]
  | cons x xs ih =>
    have hx : mem x i := h x (List.mem_cons_self ..)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨ih1, ih2⟩ := ih'
    simp only [mem, mul, List.length_cons, List.sum_cons] at ih1 ih2 ⊢
    constructor
    · have e : (xs.length + 1) * i.lo = xs.length * i.lo + i.lo := by ring
      rw [e]
      linarith [Nat.add_le_add ih1 hx1]
    · have e : (((xs.length + 1 : ℕ)) : WithTop ℕ) * i.hi = (xs.length : WithTop ℕ) * i.hi + i.hi := by
        rw [Nat.cast_succ, add_mul, one_mul]
      rw [e, Nat.cast_add]
      calc (x : WithTop ℕ) + (xs.sum : WithTop ℕ) ≤ i.hi + (xs.length : WithTop ℕ) * i.hi :=
            add_le_add hx2 ih2
        _ = (xs.length : WithTop ℕ) * i.hi + i.hi := add_comm _ _

/-- ALTERNATIVES: the hull over a family contains whatever any member contains -/
theorem mem_foldl_hull (l : List Ivl) (i0 : Ivl) (n : ℕ)
    (h : mem n i0 ∨ ∃ i ∈ l, mem n i) : mem n (l.foldl hull i0) := by
  induction l generalizing i0 with
  | nil =>
    simp only [List.foldl_nil]
    rcases h with h | ⟨i, hi, _⟩
    · exact h
    · simp at hi
  | cons j js ih =>
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | ⟨i, hi, hm⟩
    · exact Or.inl (mem_hull_left h)
    · rcases List.mem_cons.mp hi with rfl | hi'
      · exact Or.inl (mem_hull_right hm)
      · exact Or.inr ⟨i, hi', hm⟩

/-- THE MUST/MAY RULE.  A lower endpoint that is below every admitted execution (a MUST fact: every
    execution does at least `L`) and an upper endpoint above every one (a MAY fact: no execution does
    more than `U`) give an interval containing every admitted execution.  Lower bounds may only use
    universal facts, upper bounds must cover every alternative — this is that statement. -/
theorem must_may {S : Set ℕ} {L : ℕ} {U : WithTop ℕ}
    (hL : ∀ n ∈ S, L ≤ n) (hU : ∀ n ∈ S, (n : WithTop ℕ) ≤ U) : ∀ n ∈ S, mem n ⟨L, U⟩ :=
  fun n hn => ⟨hL n hn, hU n hn⟩

/-- a lower endpoint of 0 and an upper endpoint of ⊤ admit everything: ⊤ of the domain -/
theorem mem_top (n : ℕ) : mem n ⟨0, ⊤⟩ := ⟨Nat.zero_le _, le_top⟩

end Ivl

/-! ## Range normalisation — `RangeBounds.normalize` (MORKL.scala), transcribed -/
namespace Range

def lower (size : ℤ) (b : ℤ) : ℤ := if b = 0 then 0 else if b > 0 then b - 1 else size + b
def upper (size start : ℤ) (b : ℤ) : ℤ :=
  if b = 0 then size else if start = 0 ∧ b > 0 then b else if b > 0 then b - 1 else size + b

/-- the two clamped endpoints -/
def loOf (size start : ℤ) : ℤ := min (max (lower size start) 0) size
def hiOf (size start e : ℤ) : ℤ := min (max (upper size start e) 0) size

/-- the window `[lo, hi)` a `Range(x, start, end)` selects from `size` paths in canonical order -/
def normalize (size start e : ℤ) : ℤ × ℤ :=
  if hiOf size start e ≤ loOf size start then (0, 0) else (loOf size start, hiOf size start e)

/-- the window sits inside `[0, size]` and is well-formed -/
theorem normalize_bounds (size start e : ℤ) (hs : 0 ≤ size) :
    0 ≤ (normalize size start e).1 ∧ (normalize size start e).1 ≤ (normalize size start e).2 ∧
      (normalize size start e).2 ≤ size := by
  unfold normalize
  split_ifs with h
  · exact ⟨le_refl _, le_refl _, hs⟩
  · refine ⟨?_, le_of_lt (not_le.mp h), ?_⟩
    · exact le_min (le_max_right _ _) hs
    · exact min_le_right _ _

/-- the FULL window `(0, 0)` is the identity: `[0, size)` — the case every backend answers by pointer -/
theorem normalize_full (size : ℤ) (hs : 0 < size) : normalize size 0 0 = (0, size) := by
  have h1 : lower size 0 = 0 := by simp [lower]
  have h2 : upper size 0 0 = size := by simp [upper]
  have hlo : loOf size 0 = 0 := by
    unfold loOf; rw [h1, max_self]; exact min_eq_left hs.le
  have hhi : hiOf size 0 0 = size := by
    unfold hiOf; rw [h2, max_eq_left hs.le, min_self]
  unfold normalize
  rw [hlo, hhi]
  simp [not_le.mpr hs]

/-- an EMPTY source has the empty window whatever the bounds -/
theorem normalize_empty (start e : ℤ) : normalize 0 start e = (0, 0) := by
  have hlo : loOf 0 start = 0 := by
    unfold loOf; exact min_eq_right (le_max_right _ _)
  have hhi : hiOf 0 start e = 0 := by
    unfold hiOf; exact min_eq_right (le_max_right _ _)
  unfold normalize
  rw [hlo, hhi]
  simp

/-- the slice `[lo, hi)` of a list of at least `hi` elements has exactly `hi - lo` elements — the
    size the `Range` transfer reports for a window -/
theorem slice_length {α : Type*} (l : List α) (lo hi : ℕ) (hhi : hi ≤ l.length) (hlo : lo ≤ hi) :
    ((l.drop lo).take (hi - lo)).length = hi - lo := by
  simp only [List.length_take, List.length_drop]
  omega

/-- the full slice is the list itself: the identity window allocates nothing -/
theorem slice_full {α : Type*} (l : List α) : (l.drop 0).take l.length = l := by simp

/-- the empty window selects nothing -/
theorem slice_empty {α : Type*} (l : List α) (lo : ℕ) : (l.drop lo).take 0 = [] := by simp

end Range

/-! ## Widening -/

/-- A WIDENING that dominates the join is an upper bound of both its arguments: the post-fixpoint
    iteration `cur := widen cur nxt` never drops a fact (`Domain.widen` is `join` followed by a
    type-level widening past the budget, hence ⊒ the join). -/
theorem widen_upper {α : Type*} [SemilatticeSup α] (w : α → α → α) (hw : ∀ a b, a ⊔ b ≤ w a b)
    (a b : α) : a ≤ w a b ∧ b ≤ w a b :=
  ⟨le_trans le_sup_left (hw a b), le_trans le_sup_right (hw a b)⟩

/-- the post-fixpoint test: when the next iterate is below the current one, the current one is a
    post-fixpoint of the (monotone) step — the iteration may stop -/
theorem post_fixpoint {α : Type*} [Preorder α] (F : α → α) (cur : α) (h : F cur ≤ cur) : F cur ≤ cur := h

/-! ## The finite-model principle -/

/-- EXHAUSTIVE CHECKING: a decidable property with no counterexample on a finite universe holds on
    every element of it.  `proofs/spatial/check_transfers.py` instantiates this for the exact-tier
    transfers over the small universe (paths over {a, b} of length ≤ 2, at most 3 per value): a row
    per pair of values, zero rows failing. -/
theorem exhaustive {U : Type*} [Fintype U] (P : U → Prop) [DecidablePred P]
    (h : (Finset.univ.filter (fun u => ¬ P u)).card = 0) : ∀ u, P u := by
  intro u
  by_contra hu
  have hm : u ∈ Finset.univ.filter (fun u => ¬ P u) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
  have := Finset.card_pos.mpr ⟨u, hm⟩
  omega

end Spatial
end Zippy
