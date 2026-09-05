/-
==================================================================================================
THE POSITIVE FRAGMENT, MECHANIZED.

`terminating/REGISTRY.tsv` row O10b is "k-unrolling equivalence for ALL k plus omega-continuity
implies lfp equivalence", and it was OPEN for two reasons the row states: nothing in the tree said
which terms denote omega-continuous operators, and the pipeline's residual-cut cells emit k = 1 and
k = 2 only, so even with the lemma the antecedent "for all k" was never established.

This module supplies both halves that a Lean theorem can supply:

  1. A DECISION PROCEDURE for the positive fragment: `Space.posB m s` decides, syntactically, whether
     `s` is positive in the space variable `m`.  It is the Lean twin of
     `AgnosticPipeline.monotoneInMention` (EquivPipeline.scala) constructor for constructor, with
     the ONE deliberate strengthening `posB_fixpoint` documents.
  2. The two semantic theorems per constructor, proved at once by induction over the whole grammar:
       `denT_mono`  — a positive term denotes a MONOTONE function of the variable;
       `denT_cont`  — a positive term denotes an OMEGA-CONTINUOUS function of the variable
                      (it commutes with the union of an ascending chain).
     Closure under composition is `cont_comp`; closure under calls is the `call` arm of the
     induction, under the hypothesis that every routine in scope is itself monotone and continuous
     in its space arguments (`RoutineEnv.Good`).
  3. THE ALL-k APPROXIMANT THEOREM, `Kleene.iUnion_chain_is_lfp`: for a monotone omega-continuous
     operator the union of the Kleene chain IS the least fixpoint above `init`.  With `denT_cont`
     this is what turns a fixpoint body's positivity into "the Kleene union the executors compute
     is the least post-fixpoint".  `Kleene.chain_congr_of_step_eq` / `fixpoint_denT_eq_of_step_eq`
     are its consumer-facing forms: if two bodies agree on EVERY value of the recursion variable
     (which is exactly what a residual-cut cell with a FREE cut states), then every approximant
     agrees and so do the two fixpoints.

==WHY A SECOND DENOTATION, AND WHAT IT IS FAITHFUL TO==
`Pointwise.lean`'s `Space.den` is `Option`-valued and `none` at `fixpoint`/`iteration`/`call`,
deliberately: the header there defers those to this task.  A least fixpoint is an infinite union, so
the natural home for it is a TOTAL set-valued semantics, `Space.denT` below.  The two agree on the
pointwise fragment — `denT_eq_den` proves `den ρ s = some (denT δ ρ s)` wherever `den` is defined —
so no theorem here is about a different language than the one `Pointwise.lean` and the SMT tier
speak.  Where `den` is `none` for a reason OTHER than deferral (`range` → T5, `grounded*` → T6,
`fold` → its own order-independence obligation), `denT` returns `∅` and `Space.inFrag` is `false`.
EVERY THEOREM BELOW HYPOTHESISES `inFrag`, so the placeholder value is never consulted by anything
this module proves; it exists only so the function is total and structurally recursive.

==THE VARIABLE, THE ENVIRONMENT, THE CHAIN==
Positivity is a property of a term in ONE named space variable `m`, as it is in the Scala.  Joint
monotonicity in several variables follows by chaining single-variable steps, and joint continuity
follows from separate continuity plus monotonicity (`cont_two`) — which is how the `iteration` case
of the induction gets continuity in `rest` and in `m` at the same time from the single-variable
induction hypothesis.  An ascending chain is a `Monotone` sequence `ℕ → SpaceV`; its supremum is
`⋃ k, A k`.

    proofs/lean/Zippy/Positive.lean#Zippy.Kleene.iUnion_chain_is_lfp
    proofs/lean/Zippy/Positive.lean#Zippy.Space.denT_cont
    proofs/lean/Zippy/Positive.lean#Zippy.Space.fixpoint_denT_eq_of_step_eq
==================================================================================================
-/
import Zippy.Pointwise
import Zippy.Fixpoint
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Monotone.Basic

namespace Zippy

/-! ### Environments: updating one variable -/

/-- `ρ` with the space variable `m` rebound to `X` — `sc.grown(Map(m -> X))` in MORKL.scala. -/
def Env.setM (ρ : Env) (m : Name) (X : SpaceV) : Env :=
  { ρ with spaces := Function.update ρ.spaces m X }

/-- `ρ` with the path variable `r` rebound to `v`. -/
def Env.setR (ρ : Env) (r : Name) (v : PathV) : Env :=
  { ρ with refs := Function.update ρ.refs r v }

@[simp] theorem Env.setM_spaces_same (ρ : Env) (m : Name) (X : SpaceV) :
    (ρ.setM m X).spaces m = X := by simp [Env.setM]
@[simp] theorem Env.setM_refs (ρ : Env) (m : Name) (X : SpaceV) :
    (ρ.setM m X).refs = ρ.refs := rfl
@[simp] theorem Env.setR_spaces (ρ : Env) (r : Name) (v : PathV) :
    (ρ.setR r v).spaces = ρ.spaces := rfl
theorem Env.setM_spaces_ne (ρ : Env) {m v : Name} (X : SpaceV) (h : v ≠ m) :
    (ρ.setM m X).spaces v = ρ.spaces v := by simp [Env.setM, Function.update_of_ne h]
theorem Env.setM_setM_comm (ρ : Env) {m n : Name} (X Y : SpaceV) (h : m ≠ n) :
    (ρ.setM m X).setM n Y = (ρ.setM n Y).setM m X := by
  simp only [Env.setM]
  congr 1
  exact Function.update_comm h _ _ _
theorem Env.setM_setM_same (ρ : Env) (m : Name) (X Y : SpaceV) :
    (ρ.setM m X).setM m Y = ρ.setM m Y := by
  simp [Env.setM]
theorem Env.setR_setM (ρ : Env) (r m : Name) (v : PathV) (X : SpaceV) :
    (ρ.setR r v).setM m X = (ρ.setM m X).setR r v := rfl

/-! ### The semantic routine environment

A `Call` names a GLOBAL routine.  Its semantics here is a function of the argument values — which is
what `eval`'s `Call` rule computes after binding the parameters — and NOT a recursive unfolding:
recursion through calls is `2E.2`'s subject (`Supercompile.lean`), where the routine table is itself
a least fixpoint.  For THIS module a routine is an opaque semantic function, and "closure under
calls" is the statement that positivity survives a call whenever every routine in scope is monotone
and continuous in its space arguments (`RoutineEnv.Good`). -/
abbrev RoutineEnv := Name → List PathV → List SpaceV → SpaceV

/-- pointwise `⊆` on argument lists of equal length -/
def ListLE (xs ys : List SpaceV) : Prop := List.Forall₂ (· ⊆ ·) xs ys

/-- monotone and omega-continuous in the space arguments.  Continuity is stated over a list of
ascending chains: the supremum is taken argument-wise. -/
structure RoutineEnv.Good (δ : RoutineEnv) : Prop where
  mono : ∀ r ps xs ys, ListLE xs ys → δ r ps xs ⊆ δ r ps ys
  cont : ∀ r ps (xs : List (ℕ → SpaceV)), (∀ x ∈ xs, Monotone x) →
    δ r ps (xs.map (fun x => ⋃ k, x k)) = ⋃ k, δ r ps (xs.map (fun x => x k))

/-! ### The total denotation -/

/-- the HEADS of a set of paths: the first items -/
def heads (A : SpaceV) : Set Name := {h | ∃ t, h :: t ∈ A}
/-- the TAILS of a set of paths under one head — what `Iteration` binds `rest` to -/
def tailsAt (h : Name) (A : SpaceV) : SpaceV := {t | h :: t ∈ A}

/-- the total path denotation.  `[]` at the two grounded forms, which `inFrag` excludes. -/
def Path.denT (ρ : Env) : Path → PathV
  | .deref r => ρ.refs r
  | .const items => items
  | .concat l r => l.denT ρ ++ r.denT ρ
  | .groundedPP _ _ => []
  | .groundedSP _ _ => []

/-- `Path.den` agrees with `Path.denT` wherever it is defined. -/
theorem Path.denT_eq_den (ρ : Env) : ∀ (p : Path) (v : PathV), p.den ρ = some v → p.denT ρ = v
  | .deref _, v, h => by simpa [Path.den, Path.denT] using h
  | .const _, v, h => by simpa [Path.den, Path.denT] using h
  | .concat l r, v, h => by
      simp only [Path.den] at h
      cases hl : l.den ρ with
      | none => simp [hl, optP2] at h
      | some a =>
        cases hr : r.den ρ with
        | none => simp [hl, hr, optP2] at h
        | some b =>
          simp only [hl, hr, optP2, Option.some.injEq] at h
          simp [Path.denT, Path.denT_eq_den ρ l a hl, Path.denT_eq_den ρ r b hr, h]
  | .groundedPP _ _, v, h => by simp [Path.den] at h
  | .groundedSP _ _, v, h => by simp [Path.den] at h

/-- the argument list of a `Call`, denoted -/
def Path.denTs (ρ : Env) : List Path → List PathV
  | [] => []
  | p :: rest => p.denT ρ :: Path.denTs ρ rest

/-- the Kleene operator a `Fixpoint` iterates: `X ↦ init ∪ body[rec := X]` — "THE ITERATED OPERATOR
IS `X |-> X u F(X)`, NOT `F`" (MORKL.scala, `eval`'s `Fixpoint` rule). -/
def fixOp (I : SpaceV) (B : SpaceV → SpaceV) : SpaceV → SpaceV := fun X => I ∪ B X

mutual
  /-- the total space denotation.  Every pointwise clause is `Pointwise.lean`'s; the three
  deferred constructors are given their meaning here; `∅` where `inFrag` is `false`. -/
  def Space.denT (δ : RoutineEnv) (ρ : Env) : Space → SpaceV
    | .empty => ∅
    | .lit ps => {e | e ∈ ps}
    | .mention m => ρ.spaces m
    | .singleton p => {p.denT ρ}
    | .union x y => x.denT δ ρ ∪ y.denT δ ρ
    | .inter x y => x.denT δ ρ ∩ y.denT δ ρ
    | .sub x y => x.denT δ ρ \ y.denT δ ρ
    | .restriction x y => {e ∈ x.denT δ ρ | ∃ q ∈ y.denT δ ρ, q <+: e}
    | .raffination x y => x.denT δ ρ \ {e ∈ x.denT δ ρ | ∃ q ∈ y.denT δ ρ, q <+: e}
    | .composition x y => {e | ∃ u ∈ x.denT δ ρ, ∃ v ∈ y.denT δ ρ, e = u ++ v}
    | .wrap s p => {e | ∃ u ∈ s.denT δ ρ, e = p.denT ρ ++ u}
    | .unwrap s p => {e | p.denT ρ ++ e ∈ s.denT δ ρ}
    | .tailsUnion s => {t | ∃ h, h :: t ∈ s.denT δ ρ}
    | .tailsInter s => {t | ∀ h, (∃ t', h :: t' ∈ s.denT δ ρ) → h :: t ∈ s.denT δ ρ}
    -- `Iteration`: group the source by head; bind `symbol` to the one-item path and `rest` to that
    -- head's tail set; union the bodies.  `eval`'s rule, and `EquivPipeline.expand`'s.
    | .iteration src sym rest t =>
        ⋃ h ∈ heads (src.denT δ ρ),
          t.denT δ ((ρ.setR sym [h]).setM rest (tailsAt h (src.denT δ ρ)))
    -- `Fixpoint`: the union of the Kleene chain of `X ↦ init ∪ body[rec := X]` from `init`.  This
    -- is what the executors compute (they stop at the stationary index, which on a finite universe
    -- is where the union stops growing); `Kleene.iUnion_chain_is_lfp` says it is the least
    -- post-fixpoint above `init` whenever the body is positive in `rec`.
    | .fixpoint i r b =>
        ⋃ n, Kleene.chain (fixOp (i.denT δ ρ) (fun X => b.denT δ (ρ.setM r X))) (i.denT δ ρ) n
    | .call r refs ms => δ r (Path.denTs ρ refs) (Space.denTs δ ρ ms)
    -- outside the fragment; see this file's header
    | .fold _ _ _ _ _ _ _ => ∅
    | .range _ _ _ => ∅
    | .groundedPS _ _ => ∅
    | .groundedSS _ _ => ∅
  def Space.denTs (δ : RoutineEnv) (ρ : Env) : List Space → List SpaceV
    | [] => []
    | s :: rest => s.denT δ ρ :: Space.denTs δ ρ rest
end

theorem Space.denTs_eq_map (δ : RoutineEnv) (ρ : Env) :
    ∀ ms : List Space, Space.denTs δ ρ ms = ms.map (Space.denT δ ρ)
  | [] => rfl
  | s :: rest => by simp [Space.denTs, Space.denTs_eq_map δ ρ rest]

/-! ### The fragment -/

mutual
  /-- the terms `denT` is faithful on: no `range` (T5), no `fold`, no grounded form (T6). -/
  def Space.inFrag : Space → Bool
    | .empty | .lit _ | .mention _ => true
    | .singleton p => p.inFrag
    | .union x y | .inter x y | .sub x y
    | .restriction x y | .raffination x y | .composition x y => x.inFrag && y.inFrag
    | .wrap s p | .unwrap s p => s.inFrag && p.inFrag
    | .tailsUnion s | .tailsInter s => s.inFrag
    | .call _ refs ms => Path.inFrags refs && Space.inFrags ms
    | .iteration src _ _ t => src.inFrag && t.inFrag
    | .fixpoint i _ b => i.inFrag && b.inFrag
    | .fold _ _ _ _ _ _ _ => false
    | .range _ _ _ => false
    | .groundedPS _ _ => false
    | .groundedSS _ _ => false
  def Space.inFrags : List Space → Bool
    | [] => true
    | s :: rest => s.inFrag && Space.inFrags rest
  def Path.inFrag : Path → Bool
    | .deref _ | .const _ => true
    | .concat l r => l.inFrag && r.inFrag
    | .groundedPP _ _ => false
    | .groundedSP _ _ => false
  def Path.inFrags : List Path → Bool
    | [] => true
    | p :: rest => p.inFrag && Path.inFrags rest
end

/-! ### The decision procedure

`AgnosticPipeline.monotoneInMention(s, m)` (EquivPipeline.scala), constructor for constructor.  Its
`free(x)` is `usesMention(x, m)`, i.e. `m ∈ x.freeM` here.

THE ONE STRENGTHENING — `fixpoint`.  The Scala arm is `go(init) && (rec == m || go(body))`: it does
not ask the body to be positive in ITS OWN recursion variable, because the renderers refuse a
non-monotone `Fixpoint` body separately (`formalOf`, `AgSmt.fixSym`).  The denotation of a fixpoint
is monotone in an OUTER variable only if each approximant is, and `chain (n+1) = init ∪ body[rec :=
chain n]` is monotone in the outer variable only when `body` is monotone in `rec` as well.  So this
definition requires it, and the Scala arm is tightened to match (a strictly more conservative
check).  Every other arm is the Scala arm verbatim. -/
mutual
  def Space.posB (m : Name) : Space → Bool
    | .empty | .lit _ | .mention _ => true
    | .singleton p => decide (m ∉ p.freeM)
    | .union x y | .inter x y | .restriction x y | .composition x y => x.posB m && y.posB m
    | .sub x y | .raffination x y => x.posB m && decide (m ∉ y.freeM)
    | .wrap s p | .unwrap s p => s.posB m && decide (m ∉ p.freeM)
    | .tailsUnion s => s.posB m
    | .tailsInter s => decide (m ∉ s.freeM)
    -- monotone in `src` only if the body is monotone in the tails it binds (a bigger source yields
    -- bigger tail-sets as well as more head groups)
    | .iteration src _ rest t =>
        (decide (m ∉ src.freeM) || (src.posB m && t.posB rest)) && (decide (rest = m) || t.posB m)
    | .fixpoint i r b =>
        decide (m ∉ (Space.fixpoint i r b).freeM)
          || (i.posB m && b.posB r && (decide (r = m) || b.posB m))
    -- closure under calls: positive arguments, under `RoutineEnv.Good`.  The Scala arm is
    -- `!free(other)` (unknown variance), which IMPLIES this one — see `posB_of_notFree`.
    | .call _ refs ms => decide (m ∉ Path.freeMs refs) && Space.posBs m ms
    -- Range / Fold / grounded: unknown variance — `!free(other)`
    | .fold src ini acc sym rest t upd =>
        decide (m ∉ (Space.fold src ini acc sym rest t upd).freeM)
    | .range x _ _ => decide (m ∉ x.freeM)
    | .groundedPS p _ => decide (m ∉ p.freeM)
    | .groundedSS s _ => decide (m ∉ s.freeM)
  def Space.posBs (m : Name) : List Space → Bool
    | [] => true
    | s :: rest => s.posB m && Space.posBs m rest
end


/-! ### Path denotations do not see space variables -/

theorem Path.denT_setM (ρ : Env) (m : Name) (X : SpaceV) :
    ∀ p : Path, p.denT (ρ.setM m X) = p.denT ρ
  | .deref _ => rfl
  | .const _ => rfl
  | .concat l r => by simp [Path.denT, Path.denT_setM ρ m X l, Path.denT_setM ρ m X r]
  | .groundedPP _ _ => rfl
  | .groundedSP _ _ => rfl

theorem Path.denTs_setM (ρ : Env) (m : Name) (X : SpaceV) :
    ∀ ps : List Path, Path.denTs (ρ.setM m X) ps = Path.denTs ρ ps
  | [] => rfl
  | p :: rest => by simp [Path.denTs, Path.denT_setM, Path.denTs_setM ρ m X rest]

/-- a path denotes the same thing in two environments with the same `refs` -/
theorem Path.denT_congr {ρ ρ' : Env} (h : ρ.refs = ρ'.refs) :
    ∀ p : Path, p.denT ρ = p.denT ρ'
  | .deref r => by simp [Path.denT, h]
  | .const _ => rfl
  | .concat l r => by simp [Path.denT, Path.denT_congr h l, Path.denT_congr h r]
  | .groundedPP _ _ => rfl
  | .groundedSP _ _ => rfl

theorem Path.denTs_congr {ρ ρ' : Env} (h : ρ.refs = ρ'.refs) :
    ∀ ps : List Path, Path.denTs ρ ps = Path.denTs ρ' ps
  | [] => rfl
  | p :: rest => by simp [Path.denTs, Path.denT_congr h, Path.denTs_congr h rest]

/-! ### The denotation depends only on the free variables

`Space.denT_congr`: two environments that agree on `s`'s free space variables (and on all path
variables) give `s` the same denotation.  This is what makes `decide (m ∉ y.freeM)` the right side
condition on a negative operand — the operand's value does not move with `m` at all — and it is the
lemma every binder case below needs to push an update past a binder. -/

/-- agreement on a finite set of space variables, with equal `refs` -/
def Env.AgreeOn (V : Finset Name) (ρ ρ' : Env) : Prop :=
  ρ.refs = ρ'.refs ∧ ∀ v ∈ V, ρ.spaces v = ρ'.spaces v

theorem Env.AgreeOn.mono {V W : Finset Name} {ρ ρ' : Env} (h : Env.AgreeOn W ρ ρ') (hVW : V ⊆ W) :
    Env.AgreeOn V ρ ρ' := ⟨h.1, fun v hv => h.2 v (hVW hv)⟩

theorem Env.AgreeOn.setR {V : Finset Name} {ρ ρ' : Env} (h : Env.AgreeOn V ρ ρ') (r : Name) (v : PathV) :
    Env.AgreeOn V (ρ.setR r v) (ρ'.setR r v) :=
  ⟨by simp [Env.setR, h.1], fun x hx => h.2 x hx⟩

/-- rebinding `b` on both sides: the environments then agree on `insert b V` given agreement on
`V.erase b` — the binder case. -/
theorem Env.AgreeOn.setM {V : Finset Name} {ρ ρ' : Env} (b : Name)
    (h : Env.AgreeOn (V.erase b) ρ ρ') (X : SpaceV) :
    Env.AgreeOn V (ρ.setM b X) (ρ'.setM b X) := by
  refine ⟨h.1, fun v hv => ?_⟩
  by_cases hvb : v = b
  · subst hvb; simp
  · rw [Env.setM_spaces_ne _ _ hvb, Env.setM_spaces_ne _ _ hvb]
    exact h.2 v (Finset.mem_erase.mpr ⟨hvb, hv⟩)

theorem Kleene.chain_congr {α : Type*} {F G : Set α → Set α} {I J : Set α}
    (hF : ∀ X, F X = G X) (hI : I = J) : ∀ n, Kleene.chain F I n = Kleene.chain G J n
  | 0 => hI
  | n + 1 => by simp [Kleene.chain, hF, Kleene.chain_congr hF hI n]

mutual
theorem Space.denT_congr (δ : RoutineEnv) :
    ∀ (s : Space) (ρ ρ' : Env), Env.AgreeOn s.freeM ρ ρ' → s.denT δ ρ = s.denT δ ρ'
  | .empty, _, _, _ => rfl
  | .lit _, _, _, _ => rfl
  | .mention v, ρ, ρ', h => h.2 v (by simp [Space.freeM])
  | .singleton p, ρ, ρ', h => by simp [Space.denT, Path.denT_congr h.1 p]
  | .union x y, ρ, ρ', h => by
      simp only [Space.freeM] at h
      simp [Space.denT, Space.denT_congr δ x ρ ρ' (h.mono Finset.subset_union_left),
            Space.denT_congr δ y ρ ρ' (h.mono Finset.subset_union_right)]
  | .inter x y, ρ, ρ', h => by
      simp only [Space.freeM] at h
      simp [Space.denT, Space.denT_congr δ x ρ ρ' (h.mono Finset.subset_union_left),
            Space.denT_congr δ y ρ ρ' (h.mono Finset.subset_union_right)]
  | .sub x y, ρ, ρ', h => by
      simp only [Space.freeM] at h
      simp [Space.denT, Space.denT_congr δ x ρ ρ' (h.mono Finset.subset_union_left),
            Space.denT_congr δ y ρ ρ' (h.mono Finset.subset_union_right)]
  | .restriction x y, ρ, ρ', h => by
      simp only [Space.freeM] at h
      simp [Space.denT, Space.denT_congr δ x ρ ρ' (h.mono Finset.subset_union_left),
            Space.denT_congr δ y ρ ρ' (h.mono Finset.subset_union_right)]
  | .raffination x y, ρ, ρ', h => by
      simp only [Space.freeM] at h
      simp [Space.denT, Space.denT_congr δ x ρ ρ' (h.mono Finset.subset_union_left),
            Space.denT_congr δ y ρ ρ' (h.mono Finset.subset_union_right)]
  | .composition x y, ρ, ρ', h => by
      simp only [Space.freeM] at h
      simp [Space.denT, Space.denT_congr δ x ρ ρ' (h.mono Finset.subset_union_left),
            Space.denT_congr δ y ρ ρ' (h.mono Finset.subset_union_right)]
  | .wrap s p, ρ, ρ', h => by
      simp only [Space.freeM] at h
      simp [Space.denT, Space.denT_congr δ s ρ ρ' (h.mono Finset.subset_union_left),
            Path.denT_congr h.1 p]
  | .unwrap s p, ρ, ρ', h => by
      simp only [Space.freeM] at h
      simp [Space.denT, Space.denT_congr δ s ρ ρ' (h.mono Finset.subset_union_left),
            Path.denT_congr h.1 p]
  | .tailsUnion s, ρ, ρ', h => by
      simp only [Space.freeM] at h
      simp [Space.denT, Space.denT_congr δ s ρ ρ' h]
  | .tailsInter s, ρ, ρ', h => by
      simp only [Space.freeM] at h
      simp [Space.denT, Space.denT_congr δ s ρ ρ' h]
  | .range _ _ _, _, _, _ => rfl
  | .call r refs ms, ρ, ρ', h => by
      simp only [Space.freeM] at h
      simp [Space.denT, Path.denTs_congr h.1 refs,
            Space.denTs_congr δ ms ρ ρ' (h.mono Finset.subset_union_right)]
  | .iteration src sym rest t, ρ, ρ', h => by
      simp only [Space.freeM] at h
      have hsrc := Space.denT_congr δ src ρ ρ' (h.mono Finset.subset_union_left)
      have ht : ∀ hd : Name,
          t.denT δ (((ρ.setR sym [hd]).setM rest (tailsAt hd (src.denT δ ρ'))))
            = t.denT δ (((ρ'.setR sym [hd]).setM rest (tailsAt hd (src.denT δ ρ')))) := fun hd =>
        Space.denT_congr δ t _ _
          ((h.mono Finset.subset_union_right).setR sym [hd] |>.setM rest _)
      simp only [Space.denT, hsrc]
      exact Set.iUnion_congr fun hd => Set.iUnion_congr fun _ => ht hd
  | .fixpoint i r b, ρ, ρ', h => by
      simp only [Space.freeM] at h
      have hi := Space.denT_congr δ i ρ ρ' (h.mono Finset.subset_union_left)
      have hb : ∀ X, b.denT δ (ρ.setM r X) = b.denT δ (ρ'.setM r X) := fun X =>
        Space.denT_congr δ b _ _ ((h.mono Finset.subset_union_right).setM r X)
      simp only [Space.denT]
      exact Set.iUnion_congr fun n =>
        Kleene.chain_congr (F := fixOp (i.denT δ ρ) fun X => b.denT δ (ρ.setM r X))
          (fun X => by simp [fixOp, hi, hb X]) hi n
  | .fold _ _ _ _ _ _ _, _, _, _ => rfl
  | .groundedPS _ _, _, _, _ => rfl
  | .groundedSS _ _, _, _, _ => rfl
theorem Space.denTs_congr (δ : RoutineEnv) :
    ∀ (ms : List Space) (ρ ρ' : Env), Env.AgreeOn (Space.freeMs ms) ρ ρ' →
      Space.denTs δ ρ ms = Space.denTs δ ρ' ms
  | [], _, _, _ => rfl
  | s :: rest, ρ, ρ', h => by
      simp only [Space.freeMs] at h
      simp [Space.denTs, Space.denT_congr δ s ρ ρ' (h.mono Finset.subset_union_left),
            Space.denTs_congr δ rest ρ ρ' (h.mono Finset.subset_union_right)]
end

/-- `denT` is unchanged by rebinding a space variable the term does not mention. -/
theorem Space.denT_setM_of_notFree (δ : RoutineEnv) (s : Space) (ρ : Env) (m : Name) (X : SpaceV)
    (hm : m ∉ s.freeM) : s.denT δ (ρ.setM m X) = s.denT δ ρ :=
  Space.denT_congr δ s _ _ ⟨rfl, fun _ hv => Env.setM_spaces_ne ρ X (fun h => hm (h ▸ hv))⟩

theorem Space.denTs_setM_of_notFree (δ : RoutineEnv) (ms : List Space) (ρ : Env) (m : Name)
    (X : SpaceV) (hm : m ∉ Space.freeMs ms) : Space.denTs δ (ρ.setM m X) ms = Space.denTs δ ρ ms :=
  Space.denTs_congr δ ms _ _ ⟨rfl, fun _ hv => Env.setM_spaces_ne ρ X (fun h => hm (h ▸ hv))⟩

/-! ### Environment algebra for the binder cases -/

/-- pushing an outer update past a binder that rebinds the SAME name: the outer update vanishes -/
theorem Env.setR_setM_setM_same (ρ : Env) (sym m : Name) (v : PathV) (X T : SpaceV) :
    ((ρ.setM m X).setR sym v).setM m T = (ρ.setR sym v).setM m T := by
  simp [Env.setM, Env.setR]
/-- pushing an outer update past a binder with a DIFFERENT name -/
theorem Env.setR_setM_setM_comm (ρ : Env) {rest m : Name} (sym : Name) (v : PathV) (X T : SpaceV)
    (h : rest ≠ m) :
    ((ρ.setM m X).setR sym v).setM rest T = ((ρ.setR sym v).setM rest T).setM m X := by
  simp only [Env.setM, Env.setR]
  congr 1
  exact Function.update_comm h.symm _ _ _

/-! ### THEOREM 1 — monotonicity, per constructor

`denT_mono`: a term positive in `m` denotes a monotone function of `m`'s value.  Each arm of the
induction is the soundness of the corresponding arm of `monotoneInMention`; the `sub`,
`raffination` and `tailsInter` arms are where the side condition `m ∉ freeM` is spent, through
`denT_setM_of_notFree`. -/

theorem heads_mono {A B : SpaceV} (h : A ⊆ B) : heads A ⊆ heads B :=
  fun _ ⟨t, ht⟩ => ⟨t, h ht⟩
theorem tailsAt_mono (hd : Name) {A B : SpaceV} (h : A ⊆ B) : tailsAt hd A ⊆ tailsAt hd B :=
  fun _ ht => h ht

mutual
theorem Space.denT_mono (δ : RoutineEnv) (hδ : δ.Good) :
    ∀ (s : Space) (ρ : Env) (m : Name) (X Y : SpaceV), s.posB m = true → X ⊆ Y →
      s.denT δ (ρ.setM m X) ⊆ s.denT δ (ρ.setM m Y)
  | .empty, _, _, _, _, _, _ => subset_rfl
  | .lit _, _, _, _, _, _, _ => subset_rfl
  | .mention v, ρ, m, X, Y, _, hXY => by
      by_cases hv : v = m
      · subst hv; simpa [Space.denT] using hXY
      · simp [Space.denT, Env.setM_spaces_ne _ _ hv]
  | .singleton p, ρ, m, X, Y, _, _ => by simp [Space.denT, Path.denT_setM]
  | .union x y, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      exact Set.union_subset_union (Space.denT_mono δ hδ x ρ m X Y hp.1 hXY)
        (Space.denT_mono δ hδ y ρ m X Y hp.2 hXY)
  | .inter x y, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      exact Set.inter_subset_inter (Space.denT_mono δ hδ x ρ m X Y hp.1 hXY)
        (Space.denT_mono δ hδ y ρ m X Y hp.2 hXY)
  | .sub x y, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posB, Bool.and_eq_true, decide_eq_true_eq] at hp
      simp only [Space.denT, Space.denT_setM_of_notFree δ y ρ m X hp.2,
                 Space.denT_setM_of_notFree δ y ρ m Y hp.2]
      exact Set.sdiff_subset_sdiff_left (Space.denT_mono δ hδ x ρ m X Y hp.1 hXY)
  | .restriction x y, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      have hx := Space.denT_mono δ hδ x ρ m X Y hp.1 hXY
      have hy := Space.denT_mono δ hδ y ρ m X Y hp.2 hXY
      simp only [Space.denT]
      rintro e ⟨he, q, hq, hqe⟩
      exact ⟨hx he, q, hy hq, hqe⟩
  | .raffination x y, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posB, Bool.and_eq_true, decide_eq_true_eq] at hp
      have hx := Space.denT_mono δ hδ x ρ m X Y hp.1 hXY
      simp only [Space.denT, Space.denT_setM_of_notFree δ y ρ m X hp.2,
                 Space.denT_setM_of_notFree δ y ρ m Y hp.2]
      rintro e ⟨he, hne⟩
      exact ⟨hx he, fun ⟨_, hq⟩ => hne ⟨he, hq⟩⟩
  | .composition x y, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      have hx := Space.denT_mono δ hδ x ρ m X Y hp.1 hXY
      have hy := Space.denT_mono δ hδ y ρ m X Y hp.2 hXY
      simp only [Space.denT]
      rintro e ⟨u, hu, v, hv, rfl⟩
      exact ⟨u, hx hu, v, hy hv, rfl⟩
  | .wrap s p, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      have hs := Space.denT_mono δ hδ s ρ m X Y hp.1 hXY
      simp only [Space.denT, Path.denT_setM]
      rintro e ⟨u, hu, rfl⟩
      exact ⟨u, hs hu, rfl⟩
  | .unwrap s p, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      have hs := Space.denT_mono δ hδ s ρ m X Y hp.1 hXY
      simp only [Space.denT, Path.denT_setM]
      intro e he
      exact hs he
  | .tailsUnion s, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posB] at hp
      have hs := Space.denT_mono δ hδ s ρ m X Y hp hXY
      simp only [Space.denT]
      rintro t ⟨hd, ht⟩
      exact ⟨hd, hs ht⟩
  | .tailsInter s, ρ, m, X, Y, hp, _ => by
      simp only [Space.posB, decide_eq_true_eq] at hp
      simp [Space.denT, Space.denT_setM_of_notFree δ s ρ m X hp,
            Space.denT_setM_of_notFree δ s ρ m Y hp]
  | .range _ _ _, _, _, _, _, _, _ => subset_rfl
  | .call r refs ms, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      simp only [Space.denT, Path.denTs_setM]
      exact hδ.mono r _ _ _ (Space.denTs_mono δ hδ ms ρ m X Y hp.2 hXY)
  | .iteration src sym rest t, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hp
      obtain ⟨hsrc, hbody⟩ := hp
      -- the body under one head, at a given source value and tail set
      simp only [Space.denT]
      -- ONE STEP for the body: at a fixed head and tail set, the body is monotone in `m`
      -- (or constant in it, when `rest` shadows `m`).
      have hbodyM : ∀ (hd : Name) (T : SpaceV),
          t.denT δ (((ρ.setM m X).setR sym [hd]).setM rest T)
            ⊆ t.denT δ (((ρ.setM m Y).setR sym [hd]).setM rest T) := by
        intro hd T
        rcases hbody with hrm | hpos
        · subst hrm
          rw [Env.setR_setM_setM_same, Env.setR_setM_setM_same]
        · by_cases hrm : rest = m
          · subst hrm
            rw [Env.setR_setM_setM_same, Env.setR_setM_setM_same]
          · rw [Env.setR_setM_setM_comm ρ sym [hd] X T hrm,
                Env.setR_setM_setM_comm ρ sym [hd] Y T hrm]
            exact Space.denT_mono δ hδ t _ m X Y hpos hXY
      rcases hsrc with hnf | ⟨hps, hpr⟩
      · -- the source does not mention `m`: same heads, same tails, monotone body
        rw [Space.denT_setM_of_notFree δ src ρ m X hnf, Space.denT_setM_of_notFree δ src ρ m Y hnf]
        exact Set.iUnion_mono fun hd => Set.iUnion_mono fun _ => hbodyM hd _
      · -- the source grows: more heads, bigger tails (body monotone in `rest`), monotone body
        have hA := Space.denT_mono δ hδ src ρ m X Y hps hXY
        intro e he
        simp only [Set.mem_iUnion] at he ⊢
        obtain ⟨hd, hhd, he⟩ := he
        refine ⟨hd, heads_mono hA hhd, ?_⟩
        have h1 : t.denT δ (((ρ.setM m X).setR sym [hd]).setM rest (tailsAt hd (src.denT δ (ρ.setM m X))))
            ⊆ t.denT δ (((ρ.setM m X).setR sym [hd]).setM rest (tailsAt hd (src.denT δ (ρ.setM m Y)))) :=
          Space.denT_mono δ hδ t _ rest _ _ hpr (tailsAt_mono hd hA)
        exact hbodyM hd _ (h1 he)
  | .fixpoint i r b, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hp
      rcases hp with hnf | ⟨⟨hi, hr⟩, hbm⟩
      · rw [Space.denT_setM_of_notFree δ _ ρ m X hnf, Space.denT_setM_of_notFree δ _ ρ m Y hnf]
      simp only [Space.denT]
      have hI := Space.denT_mono δ hδ i ρ m X Y hi hXY
      -- the body step is monotone in the recursion variable AND in `m`
      have hstep : ∀ (U V : SpaceV), U ⊆ V →
          b.denT δ ((ρ.setM m X).setM r U) ⊆ b.denT δ ((ρ.setM m Y).setM r V) := by
        intro U V hUV
        have h1 : b.denT δ ((ρ.setM m X).setM r U) ⊆ b.denT δ ((ρ.setM m X).setM r V) :=
          Space.denT_mono δ hδ b _ r U V hr hUV
        refine h1.trans ?_
        by_cases hrm : r = m
        · subst hrm; rw [Env.setM_setM_same, Env.setM_setM_same]
        · rw [Env.setM_setM_comm ρ X V (Ne.symm hrm), Env.setM_setM_comm ρ Y V (Ne.symm hrm)]
          rcases hbm with hrm' | hpos
          · exact absurd hrm' hrm
          · exact Space.denT_mono δ hδ b _ m X Y hpos hXY
      have hchain : ∀ n,
          Kleene.chain (fixOp (i.denT δ (ρ.setM m X)) fun U => b.denT δ ((ρ.setM m X).setM r U))
              (i.denT δ (ρ.setM m X)) n
          ⊆ Kleene.chain (fixOp (i.denT δ (ρ.setM m Y)) fun U => b.denT δ ((ρ.setM m Y).setM r U))
              (i.denT δ (ρ.setM m Y)) n := by
        intro n
        induction n with
        | zero => simpa using hI
        | succ n ih =>
          simp only [Kleene.chain_succ, fixOp]
          exact Set.union_subset_union hI (hstep _ _ ih)
      exact Set.iUnion_mono hchain
  | .fold _ _ _ _ _ _ _, _, _, _, _, _, _ => subset_rfl
  | .groundedPS _ _, _, _, _, _, _, _ => subset_rfl
  | .groundedSS _ _, _, _, _, _, _, _ => subset_rfl
theorem Space.denTs_mono (δ : RoutineEnv) (hδ : δ.Good) :
    ∀ (ms : List Space) (ρ : Env) (m : Name) (X Y : SpaceV), Space.posBs m ms = true → X ⊆ Y →
      ListLE (Space.denTs δ (ρ.setM m X) ms) (Space.denTs δ (ρ.setM m Y) ms)
  | [], _, _, _, _, _, _ => List.Forall₂.nil
  | s :: rest, ρ, m, X, Y, hp, hXY => by
      simp only [Space.posBs, Bool.and_eq_true] at hp
      exact List.Forall₂.cons (Space.denT_mono δ hδ s ρ m X Y hp.1 hXY)
        (Space.denTs_mono δ hδ rest ρ m X Y hp.2 hXY)
end


/-! ### THEOREM 2 — omega-continuity, per constructor

`denT_cont`: a term positive in `m` commutes with the union of an ASCENDING chain of values of `m`.
The direction `⊇` is monotonicity; the direction `⊆` is where each constructor's finitary character
is used — a path is in a binary operation's result because of ONE member of each operand, and both
members are already present at some common index of the two chains.  The `iteration` and `fixpoint`
arms are the ones O10b is about. -/

/-- the common-index lemma behind every binary arm: two members of two ascending chains are both
present at the larger index -/
theorem mem_chain_max {A B : ℕ → SpaceV} (hA : Monotone A) (hB : Monotone B) {a b : PathV}
    {i j : ℕ} (ha : a ∈ A i) (hb : b ∈ B j) : a ∈ A (max i j) ∧ b ∈ B (max i j) :=
  ⟨hA (le_max_left i j) ha, hB (le_max_right i j) hb⟩

/-- a two-argument set operation that is monotone and "finitary in each member" commutes with the
join of two ascending chains — the shape shared by `inter`, `restriction` and `composition` -/
theorem iUnion_binary {A B : ℕ → SpaceV} (hA : Monotone A) (hB : Monotone B)
    (op : SpaceV → SpaceV → SpaceV)
    (hmono : ∀ a a' b b', a ⊆ a' → b ⊆ b' → op a b ⊆ op a' b')
    (hfin : ∀ (S : ℕ → SpaceV) (T : ℕ → SpaceV) e, e ∈ op (⋃ k, S k) (⋃ k, T k) →
      ∃ i j, e ∈ op (S i) (T j)) :
    op (⋃ k, A k) (⋃ k, B k) = ⋃ k, op (A k) (B k) := by
  ext e
  constructor
  · intro he
    obtain ⟨i, j, hij⟩ := hfin A B e he
    exact Set.mem_iUnion.mpr ⟨max i j,
      hmono _ _ _ _ (hA (le_max_left i j)) (hB (le_max_right i j)) hij⟩
  · intro he
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp he
    exact hmono _ _ _ _ (Set.subset_iUnion A k) (Set.subset_iUnion B k) hk

theorem Space.posBs_mem {m : Name} {ms : List Space} (h : Space.posBs m ms = true) {s : Space}
    (hs : s ∈ ms) : s.posB m = true := by
  induction ms with
  | nil => simp at hs
  | cons a rest ih =>
    simp only [Space.posBs, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hs with rfl | hs
    · exact h.1
    · exact ih h.2 hs

theorem Kleene.chain_mono_of_mono {α : Type*} {F : Set α → Set α} {I : Set α}
    (hF : ∀ x y : Set α, x ⊆ y → F x ⊆ F y) (hinfl : I ⊆ F I) :
    Monotone (Kleene.chain F I) :=
  monotone_nat_of_le_succ (Kleene.chain_ascends F I hF hinfl)

mutual
theorem Space.denT_cont (δ : RoutineEnv) (hδ : δ.Good) :
    ∀ (s : Space) (ρ : Env) (m : Name) (A : ℕ → SpaceV), s.posB m = true → Monotone A →
      s.denT δ (ρ.setM m (⋃ k, A k)) = ⋃ k, s.denT δ (ρ.setM m (A k))
  | .empty, _, _, _, _, _ => by simp [Space.denT]
  | .lit _, _, _, _, _, _ => by simp only [Space.denT]; exact (Set.iUnion_const _).symm
  | .mention v, ρ, m, A, _, _ => by
      by_cases hv : v = m
      · subst hv; simp [Space.denT]
      · simp only [Space.denT, Env.setM_spaces_ne _ _ hv]; exact (Set.iUnion_const _).symm
  | .singleton p, ρ, m, A, _, _ => by
      simp only [Space.denT, Path.denT_setM]; exact (Set.iUnion_const _).symm
  | .union x y, ρ, m, A, hp, hA => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      simp only [Space.denT, Space.denT_cont δ hδ x ρ m A hp.1 hA,
                 Space.denT_cont δ hδ y ρ m A hp.2 hA]
      exact (Set.iUnion_union_distrib _ _).symm
  | .inter x y, ρ, m, A, hp, hA => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      simp only [Space.denT, Space.denT_cont δ hδ x ρ m A hp.1 hA,
                 Space.denT_cont δ hδ y ρ m A hp.2 hA]
      refine iUnion_binary (fun i j hij => Space.denT_mono δ hδ x ρ m _ _ hp.1 (hA hij))
        (fun i j hij => Space.denT_mono δ hδ y ρ m _ _ hp.2 (hA hij)) (· ∩ ·)
        (fun _ _ _ _ h1 h2 => Set.inter_subset_inter h1 h2) ?_
      intro S T e he
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := he
      simp only [Set.mem_range] at hi hj
      obtain ⟨i, rfl⟩ := hi.1
      obtain ⟨j, rfl⟩ := hj.1
      exact ⟨i, j, hi.2, hj.2⟩
  | .sub x y, ρ, m, A, hp, hA => by
      simp only [Space.posB, Bool.and_eq_true, decide_eq_true_eq] at hp
      simp only [Space.denT, Space.denT_cont δ hδ x ρ m A hp.1 hA,
                 Space.denT_setM_of_notFree δ y ρ m _ hp.2]
      exact Set.iUnion_sdiff _ _
  | .restriction x y, ρ, m, A, hp, hA => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      simp only [Space.denT, Space.denT_cont δ hδ x ρ m A hp.1 hA,
                 Space.denT_cont δ hδ y ρ m A hp.2 hA]
      refine iUnion_binary (fun i j hij => Space.denT_mono δ hδ x ρ m _ _ hp.1 (hA hij))
        (fun i j hij => Space.denT_mono δ hδ y ρ m _ _ hp.2 (hA hij))
        (fun a b => {e ∈ a | ∃ q ∈ b, q <+: e}) ?_ ?_
      · rintro a a' b b' h1 h2 e ⟨he, q, hq, hqe⟩
        exact ⟨h1 he, q, h2 hq, hqe⟩
      · rintro S T e ⟨he, q, hq, hqe⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hq
        exact ⟨i, j, hi, q, hj, hqe⟩
  | .raffination x y, ρ, m, A, hp, hA => by
      simp only [Space.posB, Bool.and_eq_true, decide_eq_true_eq] at hp
      simp only [Space.denT, Space.denT_cont δ hδ x ρ m A hp.1 hA,
                 Space.denT_setM_of_notFree δ y ρ m _ hp.2]
      ext e
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨⟨k, hk⟩, hne⟩
        exact ⟨k, hk, fun ⟨_, hq⟩ => hne ⟨⟨k, hk⟩, hq⟩⟩
      · rintro ⟨k, hk, hne⟩
        exact ⟨⟨k, hk⟩, fun ⟨_, hq⟩ => hne ⟨hk, hq⟩⟩
  | .composition x y, ρ, m, A, hp, hA => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      simp only [Space.denT, Space.denT_cont δ hδ x ρ m A hp.1 hA,
                 Space.denT_cont δ hδ y ρ m A hp.2 hA]
      refine iUnion_binary (fun i j hij => Space.denT_mono δ hδ x ρ m _ _ hp.1 (hA hij))
        (fun i j hij => Space.denT_mono δ hδ y ρ m _ _ hp.2 (hA hij))
        (fun a b => {e | ∃ u ∈ a, ∃ v ∈ b, e = u ++ v}) ?_ ?_
      · rintro a a' b b' h1 h2 e ⟨u, hu, v, hv, rfl⟩
        exact ⟨u, h1 hu, v, h2 hv, rfl⟩
      · rintro S T e ⟨u, hu, v, hv, rfl⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hv
        exact ⟨i, j, u, hi, v, hj, rfl⟩
  | .wrap s p, ρ, m, A, hp, hA => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      simp only [Space.denT, Space.denT_cont δ hδ s ρ m A hp.1 hA, Path.denT_setM]
      ext e
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨u, ⟨k, hk⟩, rfl⟩; exact ⟨k, u, hk, rfl⟩
      · rintro ⟨k, u, hk, rfl⟩; exact ⟨u, ⟨k, hk⟩, rfl⟩
  | .unwrap s p, ρ, m, A, hp, hA => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      simp only [Space.denT, Space.denT_cont δ hδ s ρ m A hp.1 hA, Path.denT_setM]
      ext e
      simp [Set.mem_iUnion]
  | .tailsUnion s, ρ, m, A, hp, hA => by
      simp only [Space.posB] at hp
      simp only [Space.denT, Space.denT_cont δ hδ s ρ m A hp hA]
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨hd, k, hk⟩; exact ⟨k, hd, hk⟩
      · rintro ⟨k, hd, hk⟩; exact ⟨hd, k, hk⟩
  | .tailsInter s, ρ, m, A, hp, _ => by
      simp only [Space.posB, decide_eq_true_eq] at hp
      simp only [Space.denT, Space.denT_setM_of_notFree δ s ρ m _ hp]
      exact (Set.iUnion_const _).symm
  | .range _ _ _, _, _, _, _, _ => by simp [Space.denT]
  | .call r refs ms, ρ, m, A, hp, hA => by
      simp only [Space.posB, Bool.and_eq_true] at hp
      simp only [Space.denT, Path.denTs_setM]
      have hxs : ∀ x ∈ ms.map (fun s k => s.denT δ (ρ.setM m (A k))), Monotone x := by
        intro x hx
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
        intro i j hij
        exact Space.denT_mono δ hδ s ρ m _ _ (Space.posBs_mem hp.2 hs) (hA hij)
      have hc := hδ.cont r (Path.denTs ρ refs) _ hxs
      rw [Space.denTs_cont δ hδ ms ρ m A hp.2 hA, hc]
      congr 1; ext k
      rw [Space.denTs_eq_map, List.map_map]
      rfl
  | .iteration src sym rest t, ρ, m, A, hp, hA => by
      simp only [Space.posB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hp
      obtain ⟨hsrc, hbody⟩ := hp
      simp only [Space.denT]
      -- the body under one head is continuous in `m` at a fixed tail set (or constant in it)
      have hbodyC : ∀ (hd : Name) (T : SpaceV),
          t.denT δ (((ρ.setM m (⋃ k, A k)).setR sym [hd]).setM rest T)
            = ⋃ k, t.denT δ (((ρ.setM m (A k)).setR sym [hd]).setM rest T) := by
        intro hd T
        by_cases hrm : rest = m
        · subst hrm
          simp only [Env.setR_setM_setM_same]
          exact (Set.iUnion_const _).symm
        · simp only [Env.setR_setM_setM_comm ρ sym [hd] _ T hrm]
          rcases hbody with hrm' | hpos
          · exact absurd hrm' hrm
          · exact Space.denT_cont δ hδ t _ m A hpos hA
      -- and monotone in `m` at a fixed tail set
      have hbodyM : ∀ (hd : Name) (T : SpaceV) {i j : ℕ}, i ≤ j →
          t.denT δ (((ρ.setM m (A i)).setR sym [hd]).setM rest T)
            ⊆ t.denT δ (((ρ.setM m (A j)).setR sym [hd]).setM rest T) := by
        intro hd T i j hij
        by_cases hrm : rest = m
        · subst hrm; simp only [Env.setR_setM_setM_same]; exact subset_rfl
        · simp only [Env.setR_setM_setM_comm ρ sym [hd] _ T hrm]
          rcases hbody with hrm' | hpos
          · exact absurd hrm' hrm
          · exact Space.denT_mono δ hδ t _ m _ _ hpos (hA hij)
      rcases hsrc with hnf | ⟨hps, hpr⟩
      · -- constant source: swap the two unions
        simp only [Space.denT_setM_of_notFree δ src ρ m _ hnf, hbodyC]
        ext e
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨hd, hhd, k, hk⟩; exact ⟨k, hd, hhd, hk⟩
        · rintro ⟨k, hd, hhd, hk⟩; exact ⟨hd, hhd, k, hk⟩
      · -- growing source: heads and tails are unions too, and everything is directed
        have hAsrc := Space.denT_cont δ hδ src ρ m A hps hA
        have hAmono : Monotone fun k => src.denT δ (ρ.setM m (A k)) :=
          fun i j hij => Space.denT_mono δ hδ src ρ m _ _ hps (hA hij)
        rw [hAsrc]
        ext e
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨hd, ⟨tl, htl⟩, he⟩
          -- the head is present at some index i; the tail set at the union is the union of the
          -- tail sets, so the body is a union over j (continuity in `rest`); pick max i j.
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp htl
          have htails : tailsAt hd (⋃ k, src.denT δ (ρ.setM m (A k)))
              = ⋃ k, tailsAt hd (src.denT δ (ρ.setM m (A k))) := by
            ext t'; simp [tailsAt, Set.mem_iUnion]
          rw [htails, Space.denT_cont δ hδ t _ rest _ hpr
                (fun a b hab => tailsAt_mono hd (hAmono hab))] at he
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp he
          rw [hbodyC] at hj
          obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hj
          refine ⟨max i (max j l), hd, ⟨tl, hAmono (le_max_left _ _) hi⟩, ?_⟩
          have h1 := hbodyM hd _ (le_trans (le_max_right j l) (le_max_right i _)) hl
          exact Space.denT_mono δ hδ t _ rest _ _ hpr
            (tailsAt_mono hd (hAmono (le_trans (le_max_left j l) (le_max_right i _)))) h1
        · rintro ⟨k, hd, ⟨tl, htl⟩, he⟩
          refine ⟨hd, ⟨tl, Set.mem_iUnion.mpr ⟨k, htl⟩⟩, ?_⟩
          rw [hbodyC]
          have h1 : t.denT δ (((ρ.setM m (A k)).setR sym [hd]).setM rest
                        (tailsAt hd (src.denT δ (ρ.setM m (A k)))))
              ⊆ t.denT δ (((ρ.setM m (A k)).setR sym [hd]).setM rest
                        (tailsAt hd (⋃ k, src.denT δ (ρ.setM m (A k))))) :=
            Space.denT_mono δ hδ t _ rest _ _ hpr
              (tailsAt_mono hd (Set.subset_iUnion (fun k => src.denT δ (ρ.setM m (A k))) k))
          exact Set.mem_iUnion.mpr ⟨k, h1 he⟩
  | .fixpoint i r b, ρ, m, A, hp, hA => by
      simp only [Space.posB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hp
      rcases hp with hnf | ⟨⟨hi, hr⟩, hbm⟩
      · simp only [Space.denT_setM_of_notFree δ _ ρ m _ hnf]
        exact (Set.iUnion_const _).symm
      simp only [Space.denT]
      -- notation: the operator and seed at index k, and at the union
      set Ik := fun k => i.denT δ (ρ.setM m (A k)) with hIk
      set Fk := fun k (U : SpaceV) => b.denT δ ((ρ.setM m (A k)).setM r U) with hFk
      have hIc : i.denT δ (ρ.setM m (⋃ k, A k)) = ⋃ k, Ik k := Space.denT_cont δ hδ i ρ m A hi hA
      have hImono : Monotone Ik := fun a c hac => Space.denT_mono δ hδ i ρ m _ _ hi (hA hac)
      -- the body step is monotone in `r`, and in the index
      have hFr : ∀ k (U V : SpaceV), U ⊆ V → Fk k U ⊆ Fk k V := fun k U V hUV =>
        Space.denT_mono δ hδ b _ r U V hr hUV
      have hFm : ∀ {a c : ℕ}, a ≤ c → ∀ U, Fk a U ⊆ Fk c U := by
        intro a c hac U
        by_cases hrm : r = m
        · subst hrm; simp only [hFk, Env.setM_setM_same]; exact subset_rfl
        · simp only [hFk, Env.setM_setM_comm ρ _ U (Ne.symm hrm)]
          rcases hbm with hrm' | hpos
          · exact absurd hrm' hrm
          · exact Space.denT_mono δ hδ b _ m _ _ hpos (hA hac)
      -- the body step at the union of an ascending chain of BOTH the index and the argument
      have hFc : ∀ (U : ℕ → SpaceV), Monotone U →
          b.denT δ ((ρ.setM m (⋃ k, A k)).setM r (⋃ k, U k)) = ⋃ k, Fk k (U k) := by
        intro U hU
        -- continuity in `r` first (at the union of A), then in `m`
        rw [Space.denT_cont δ hδ b _ r U hr hU]
        ext e
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨j, hj⟩
          by_cases hrm : r = m
          · subst hrm
            rw [Env.setM_setM_same] at hj
            exact ⟨j, by simpa [hFk, Env.setM_setM_same] using hj⟩
          · rw [Env.setM_setM_comm ρ _ _ (Ne.symm hrm),
                Space.denT_cont δ hδ b _ m A (by rcases hbm with h | h; exact absurd h hrm; exact h) hA] at hj
            obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hj
            refine ⟨max j l, ?_⟩
            have h1 : Fk l (U j) ⊆ Fk (max j l) (U j) := hFm (le_max_right j l) (U j)
            have h2 : Fk (max j l) (U j) ⊆ Fk (max j l) (U (max j l)) :=
              hFr _ _ _ (hU (le_max_left j l))
            apply h2; apply h1
            simpa [hFk, Env.setM_setM_comm ρ _ _ (Ne.symm hrm)] using hl
        · rintro ⟨k, hk⟩
          refine ⟨k, ?_⟩
          have : Fk k (U k) ⊆ b.denT δ ((ρ.setM m (⋃ k, A k)).setM r (U k)) := by
            by_cases hrm : r = m
            · subst hrm; simp only [hFk, Env.setM_setM_same]; exact subset_rfl
            · simp only [hFk, Env.setM_setM_comm ρ _ _ (Ne.symm hrm)]
              exact Space.denT_mono δ hδ b _ m _ _
                (by rcases hbm with h | h; exact absurd h hrm; exact h) (Set.subset_iUnion A k)
          exact this hk
      -- every approximant is continuous in the index
      have hchainMono : ∀ k, Monotone (Kleene.chain (fixOp (Ik k) (Fk k)) (Ik k)) := fun k =>
        Kleene.chain_mono_of_mono (fun x y hxy => Set.union_subset_union subset_rfl (hFr k x y hxy))
          Set.subset_union_left
      have hchainIdx : ∀ n, Monotone fun k => Kleene.chain (fixOp (Ik k) (Fk k)) (Ik k) n := by
        intro n
        induction n with
        | zero => intro a c hac; simpa using hImono hac
        | succ n ih =>
          intro a c hac
          simp only [Kleene.chain_succ, fixOp]
          exact Set.union_subset_union (hImono hac) ((hFr a _ _ (ih hac)).trans (hFm hac _))
      have happrox : ∀ n,
          Kleene.chain (fixOp (i.denT δ (ρ.setM m (⋃ k, A k)))
              fun U => b.denT δ ((ρ.setM m (⋃ k, A k)).setM r U)) (i.denT δ (ρ.setM m (⋃ k, A k))) n
            = ⋃ k, Kleene.chain (fixOp (Ik k) (Fk k)) (Ik k) n := by
        intro n
        induction n with
        | zero => simpa using hIc
        | succ n ih =>
          simp only [Kleene.chain_succ, fixOp]
          rw [ih, hIc, hFc _ (hchainIdx n)]
          exact (Set.iUnion_union_distrib _ _).symm
      simp only [happrox]
      -- swap the two unions
      ext e
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨n, k, h⟩ => ⟨k, n, h⟩, fun ⟨k, n, h⟩ => ⟨n, k, h⟩⟩
  | .fold _ _ _ _ _ _ _, _, _, _, _, _ => by simp [Space.denT]
  | .groundedPS _ _, _, _, _, _, _ => by simp [Space.denT]
  | .groundedSS _ _, _, _, _, _, _ => by simp [Space.denT]
theorem Space.denTs_cont (δ : RoutineEnv) (hδ : δ.Good) :
    ∀ (ms : List Space) (ρ : Env) (m : Name) (A : ℕ → SpaceV), Space.posBs m ms = true →
      Monotone A →
      Space.denTs δ (ρ.setM m (⋃ k, A k)) ms
        = (ms.map (fun s k => s.denT δ (ρ.setM m (A k)))).map (fun x => ⋃ k, x k)
  | [], _, _, _, _, _ => rfl
  | s :: rest, ρ, m, A, hp, hA => by
      simp only [Space.posBs, Bool.and_eq_true] at hp
      simp [Space.denTs, Space.denT_cont δ hδ s ρ m A hp.1 hA,
            Space.denTs_cont δ hδ rest ρ m A hp.2 hA]
end


/-! ### THEOREM 3 — the all-k approximant theorem

`Kleene.iUnion_chain_is_lfp`: for a monotone, omega-continuous operator `F` with `init ⊆ F init`,
the union of ALL the approximants `chain F init k` is a fixpoint of `F`, contains `init`, and is
below every pre-fixpoint above `init` — it IS `lfp_{⊇init} F`.  `Fixpoint.lean`'s
`stationary_is_lfp` says the same thing at a stationary index; this says it without one, which is
what a claim about the recursion (rather than about its first `k` unrollings) needs. -/

/-- omega-continuity of a set operator: it commutes with the union of an ascending chain -/
def OmegaCont {α : Type*} (F : Set α → Set α) : Prop :=
  ∀ A : ℕ → Set α, Monotone A → F (⋃ k, A k) = ⋃ k, F (A k)

theorem Kleene.iUnion_chain_is_lfp {α : Type*} (F : Set α → Set α) (init : Set α)
    (hmono : ∀ x y : Set α, x ⊆ y → F x ⊆ F y) (hcont : OmegaCont F) (hinfl : init ⊆ F init) :
    F (⋃ n, Kleene.chain F init n) = ⋃ n, Kleene.chain F init n
    ∧ init ⊆ ⋃ n, Kleene.chain F init n
    ∧ ∀ y : Set α, init ⊆ y → F y ⊆ y → (⋃ n, Kleene.chain F init n) ⊆ y := by
  have hasc : Monotone (Kleene.chain F init) := Kleene.chain_mono_of_mono hmono hinfl
  refine ⟨?_, ?_, ?_⟩
  · -- `F (⋃ C n) = ⋃ F (C n) = ⋃ C (n+1) = ⋃ C n`
    rw [hcont _ hasc]
    apply Set.Subset.antisymm
    · exact Set.iUnion_mono' fun n => ⟨n + 1, subset_rfl⟩
    · exact Set.iUnion_mono' fun n => ⟨n, Kleene.chain_ascends F init hmono hinfl n⟩
  · exact Set.subset_iUnion (Kleene.chain F init) 0
  · intro y hy hFy
    exact Set.iUnion_subset fun n => Kleene.chain_below_prefixpoint F init hmono n y hy hFy

/-- the composite `X ↦ init ∪ B X` is monotone and continuous whenever `B` is -/
theorem fixOp_mono {I : SpaceV} {B : SpaceV → SpaceV} (hB : ∀ x y : SpaceV, x ⊆ y → B x ⊆ B y) :
    ∀ x y : SpaceV, x ⊆ y → fixOp I B x ⊆ fixOp I B y :=
  fun x y hxy => Set.union_subset_union subset_rfl (hB x y hxy)
theorem fixOp_cont {I : SpaceV} {B : SpaceV → SpaceV} (hB : OmegaCont B) : OmegaCont (fixOp I B) := by
  intro A hA
  simp only [fixOp, hB A hA]
  ext e
  simp only [Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro (h | ⟨k, hk⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨k, Or.inr hk⟩
  · rintro ⟨k, h | hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, hk⟩
theorem fixOp_infl (I : SpaceV) (B : SpaceV → SpaceV) : I ⊆ fixOp I B I := Set.subset_union_left

/-- THE FIXPOINT CONSTRUCTOR DENOTES THE LEAST POST-FIXPOINT, whenever its body is positive in the
recursion variable — the statement every lowering pass and every first-class `Fix` axiom cites
(`AgSmt.fixSym` emits exactly these three clauses).  Here it is a theorem about `denT`, so the side
condition the Scala renderers check (`monotoneInMention(body, rec)`) is exactly what makes the
axioms they emit true. -/
theorem Space.fixpoint_is_lfp (δ : RoutineEnv) (hδ : δ.Good) (ρ : Env) (i : Space) (r : Name)
    (b : Space) (hr : b.posB r = true) :
    let F := fixOp (i.denT δ ρ) (fun X => b.denT δ (ρ.setM r X))
    let L := (Space.fixpoint i r b).denT δ ρ
    F L = L ∧ i.denT δ ρ ⊆ L ∧ ∀ y : SpaceV, i.denT δ ρ ⊆ y → F y ⊆ y → L ⊆ y := by
  intro F L
  have hB : ∀ x y : SpaceV, x ⊆ y → b.denT δ (ρ.setM r x) ⊆ b.denT δ (ρ.setM r y) :=
    fun x y hxy => Space.denT_mono δ hδ b ρ r x y hr hxy
  have hBc : OmegaCont fun X => b.denT δ (ρ.setM r X) :=
    fun A hA => Space.denT_cont δ hδ b ρ r A hr hA
  exact Kleene.iUnion_chain_is_lfp F (i.denT δ ρ) (fixOp_mono hB) (fixOp_cont hBc)
    (fixOp_infl _ _)

/-! ### The consumer-facing forms

A residual-cut cell (`AgnosticPipeline.unrollControl`, `EquivPipelineTest.agnosticLegs`) states that
two bodies agree FOR EVERY VALUE of a free cut standing for the recursive call.  That is the
hypothesis `hstep` below.  From it every approximant agrees (`chain_congr_of_step_eq`), and so do the
two fixpoint denotations (`fixpoint_denT_eq_of_step_eq`) — with NO positivity needed for the
equality itself.  Positivity enters only through `fixpoint_is_lfp`: it is what makes the common
value the LEAST post-fixpoint rather than merely the Kleene union the executors compute. -/

theorem Kleene.chain_congr_of_step_eq {α : Type*} {F G : Set α → Set α} {I : Set α}
    (hstep : ∀ X, F X = G X) : ∀ n, Kleene.chain F I n = Kleene.chain G I n :=
  Kleene.chain_congr hstep rfl

theorem Space.fixpoint_denT_eq_of_step_eq (δ : RoutineEnv) (ρ : Env) {i i' : Space} (r : Name)
    {b b' : Space} (hinit : i.denT δ ρ = i'.denT δ ρ)
    (hstep : ∀ X : SpaceV, b.denT δ (ρ.setM r X) = b'.denT δ (ρ.setM r X)) :
    (Space.fixpoint i r b).denT δ ρ = (Space.fixpoint i' r b').denT δ ρ := by
  simp only [Space.denT]
  exact Set.iUnion_congr fun n =>
    Kleene.chain_congr (fun X => by simp [fixOp, hinit, hstep X]) hinit n

/-- closure under composition: monotone continuous operators compose -/
theorem OmegaCont.comp {α : Type*} {F G : Set α → Set α} (hF : OmegaCont F) (hG : OmegaCont G)
    (hGm : ∀ x y : Set α, x ⊆ y → G x ⊆ G y) : OmegaCont (F ∘ G) := by
  intro A hA
  simp only [Function.comp]
  rw [hG A hA, hF (fun k => G (A k)) (fun a c hac => hGm _ _ (hA hac))]

/-! ### Agreement with the pointwise semantics

`denT` restricted to where `Pointwise.den` is defined IS `den`.  Stated as: whenever `den` returns
`some v`, `denT` returns `v`.  This is what lets the SMT tier's pointwise laws (certified against
`den`'s clauses) and the theorems above (about `denT`) be about one language. -/
private theorem denT_eq_den_binary (δ : RoutineEnv) (ρ : Env) {x y : Space}
    (f : SpaceV → SpaceV → SpaceV)
    (ihx : ∀ v, x.den ρ = some v → x.denT δ ρ = v)
    (ihy : ∀ v, y.den ρ = some v → y.denT δ ρ = v) :
    ∀ v, optS2 f (x.den ρ) (y.den ρ) = some v → f (x.denT δ ρ) (y.denT δ ρ) = v := by
  intro v h
  cases hx : x.den ρ with
  | none => simp [hx, optS2] at h
  | some a =>
    cases hy : y.den ρ with
    | none => simp [hx, hy, optS2] at h
    | some b =>
      simp only [hx, hy, optS2, Option.some.injEq] at h
      rw [ihx a hx, ihy b hy, h]

private theorem denT_eq_den_sp (δ : RoutineEnv) (ρ : Env) {s : Space} {p : Path}
    (f : SpaceV → PathV → SpaceV)
    (ih : ∀ v, s.den ρ = some v → s.denT δ ρ = v) :
    ∀ v, optSP f (s.den ρ) (p.den ρ) = some v → f (s.denT δ ρ) (p.denT ρ) = v := by
  intro v h
  cases hs : s.den ρ with
  | none => simp [hs, optSP] at h
  | some a =>
    cases hp : p.den ρ with
    | none => simp [hs, hp, optSP] at h
    | some w =>
      simp only [hs, hp, optSP, Option.some.injEq] at h
      rw [ih a hs, Path.denT_eq_den ρ p w hp, h]

private theorem denT_eq_den_unary (δ : RoutineEnv) (ρ : Env) {s : Space} (f : SpaceV → SpaceV)
    (ih : ∀ v, s.den ρ = some v → s.denT δ ρ = v) :
    ∀ v, (s.den ρ).map f = some v → f (s.denT δ ρ) = v := by
  intro v h
  cases hs : s.den ρ with
  | none => simp [hs] at h
  | some a =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    rw [ih a hs, h]

theorem Space.denT_eq_den (δ : RoutineEnv) (ρ : Env) :
    ∀ (s : Space) (v : SpaceV), s.den ρ = some v → s.denT δ ρ = v
  | .empty, v, h => by simpa [Space.den, Space.denT] using h
  | .lit _, v, h => by simpa [Space.den, Space.denT] using h
  | .mention _, v, h => by simpa [Space.den, Space.denT] using h
  | .singleton p, v, h => by
      simp only [Space.den] at h
      cases hp : p.den ρ with
      | none => simp [hp] at h
      | some w =>
        simp only [hp, Option.map_some, Option.some.injEq] at h
        simp [Space.denT, Path.denT_eq_den ρ p w hp, h]
  | .union x y, v, h =>
      denT_eq_den_binary δ ρ (· ∪ ·) (Space.denT_eq_den δ ρ x) (Space.denT_eq_den δ ρ y) v h
  | .inter x y, v, h =>
      denT_eq_den_binary δ ρ (· ∩ ·) (Space.denT_eq_den δ ρ x) (Space.denT_eq_den δ ρ y) v h
  | .sub x y, v, h =>
      denT_eq_den_binary δ ρ (· \ ·) (Space.denT_eq_den δ ρ x) (Space.denT_eq_den δ ρ y) v h
  | .restriction x y, v, h =>
      denT_eq_den_binary δ ρ _ (Space.denT_eq_den δ ρ x) (Space.denT_eq_den δ ρ y) v h
  | .raffination x y, v, h =>
      denT_eq_den_binary δ ρ _ (Space.denT_eq_den δ ρ x) (Space.denT_eq_den δ ρ y) v h
  | .composition x y, v, h =>
      denT_eq_den_binary δ ρ _ (Space.denT_eq_den δ ρ x) (Space.denT_eq_den δ ρ y) v h
  | .wrap s p, v, h => denT_eq_den_sp δ ρ _ (Space.denT_eq_den δ ρ s) v h
  | .unwrap s p, v, h => denT_eq_den_sp δ ρ _ (Space.denT_eq_den δ ρ s) v h
  | .tailsUnion s, v, h => denT_eq_den_unary δ ρ _ (Space.denT_eq_den δ ρ s) v h
  | .tailsInter s, v, h => denT_eq_den_unary δ ρ _ (Space.denT_eq_den δ ρ s) v h
  | .range _ _ _, v, h => by simp [Space.den] at h
  | .call _ _ _, v, h => by simp [Space.den] at h
  | .iteration _ _ _ _, v, h => by simp [Space.den] at h
  | .fixpoint _ _ _, v, h => by simp [Space.den] at h
  | .fold _ _ _ _ _ _ _, v, h => by simp [Space.den] at h
  | .groundedPS _ _, v, h => by simp [Space.den] at h
  | .groundedSS _ _, v, h => by simp [Space.den] at h

/-! ### The correspondence with the Scala decision procedure

`monotoneInMention` returns `!free(other)` for every constructor it does not analyse.  That arm is
sound here too: a term that does not mention `m` at all is positive in `m`.  With this lemma every
arm of the Scala procedure either IS the Lean arm or implies it, so `monotoneInMention(s, m) = true`
implies `s.posB m = true` — the direction soundness needs. -/
mutual
theorem Space.posB_of_notFree : ∀ (s : Space) (m : Name), m ∉ s.freeM → s.posB m = true
  | .empty, _, _ => rfl
  | .lit _, _, _ => rfl
  | .mention _, _, _ => rfl
  | .singleton p, m, h => by simpa [Space.posB, Space.freeM] using h
  | .union x y, m, h => by
      simp only [Space.freeM, Finset.mem_union, not_or] at h
      simp [Space.posB, Space.posB_of_notFree x m h.1, Space.posB_of_notFree y m h.2]
  | .inter x y, m, h => by
      simp only [Space.freeM, Finset.mem_union, not_or] at h
      simp [Space.posB, Space.posB_of_notFree x m h.1, Space.posB_of_notFree y m h.2]
  | .sub x y, m, h => by
      simp only [Space.freeM, Finset.mem_union, not_or] at h
      simp [Space.posB, Space.posB_of_notFree x m h.1, h.2]
  | .restriction x y, m, h => by
      simp only [Space.freeM, Finset.mem_union, not_or] at h
      simp [Space.posB, Space.posB_of_notFree x m h.1, Space.posB_of_notFree y m h.2]
  | .raffination x y, m, h => by
      simp only [Space.freeM, Finset.mem_union, not_or] at h
      simp [Space.posB, Space.posB_of_notFree x m h.1, h.2]
  | .composition x y, m, h => by
      simp only [Space.freeM, Finset.mem_union, not_or] at h
      simp [Space.posB, Space.posB_of_notFree x m h.1, Space.posB_of_notFree y m h.2]
  | .wrap s p, m, h => by
      simp only [Space.freeM, Finset.mem_union, not_or] at h
      simp [Space.posB, Space.posB_of_notFree s m h.1, h.2]
  | .unwrap s p, m, h => by
      simp only [Space.freeM, Finset.mem_union, not_or] at h
      simp [Space.posB, Space.posB_of_notFree s m h.1, h.2]
  | .tailsUnion s, m, h => by
      simp only [Space.freeM] at h
      simp [Space.posB, Space.posB_of_notFree s m h]
  | .tailsInter s, m, h => by simpa [Space.posB, Space.freeM] using h
  | .range x _ _, m, h => by simpa [Space.posB, Space.freeM] using h
  | .call _ refs ms, m, h => by
      simp only [Space.freeM, Finset.mem_union, not_or] at h
      simp [Space.posB, h.1, Space.posBs_of_notFree ms m h.2]
  | .iteration src sym rest t, m, h => by
      simp only [Space.freeM, Finset.mem_union, not_or, Finset.mem_erase, not_and] at h
      simp only [Space.posB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      refine ⟨Or.inl h.1, ?_⟩
      by_cases hrm : rest = m
      · exact Or.inl hrm
      · exact Or.inr (Space.posB_of_notFree t m fun hm => h.2 (Ne.symm hrm) hm)
  | .fixpoint i r b, m, h => by
      simp only [Space.posB, Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl h
  | .fold _ _ _ _ _ _ _, m, h => by simpa [Space.posB] using h
  | .groundedPS p _, m, h => by simpa [Space.posB, Space.freeM] using h
  | .groundedSS s _, m, h => by simpa [Space.posB, Space.freeM] using h
theorem Space.posBs_of_notFree : ∀ (ms : List Space) (m : Name), m ∉ Space.freeMs ms →
    Space.posBs m ms = true
  | [], _, _ => rfl
  | s :: rest, m, h => by
      simp only [Space.freeMs, Finset.mem_union, not_or] at h
      simp [Space.posBs, Space.posB_of_notFree s m h.1, Space.posBs_of_notFree rest m h.2]
end

end Zippy
