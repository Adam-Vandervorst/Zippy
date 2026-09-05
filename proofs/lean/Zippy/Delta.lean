/-
==================================================================================================
VARIANCE AND THE DELTA STEP (tasks.md A2).

Two of the five A2 mechanizations live here; `Strata.lean` has the other three.

==PART A — VARIANCE==
`DeltaIR.scala`'s `Variance.of` labels every dependency `+`/`-`/`0`/`·` by a compositional analysis
of the constructors.  `Space.varB` is its Lean twin, arm for arm, over a table `rt` of routine
PARAMETER variances, and `varB_sound` is the theorem the labels mean what they say:

    `+`  the denotation is MONOTONE in the variable
    `-`  it is ANTITONE
    `·`  it is CONSTANT (the variable is not read)
    `0`  nothing is claimed

stated as one relation `Rel v A B` between the denotations at `X ⊆ Y`.  `Var.compose` and
`Var.join` are the composition table; `Rel.binary`/`Rel.binaryAnti`/`Rel.unary` are the lemmas that
make the table correct for a monotone, a mixed, and a unary operator, and the binder cases are proved
by the same chain arguments `Positive.lean` uses for positivity alone.  A routine table is trusted
only through `VarGood`: the hypothesis that a routine's value changes with its arguments as its
table row says (which `Variance.routineTable` derives as a least fixpoint over the routine bodies —
the semantic soundness of that derivation for a RECURSIVE routine is the routine's own fixpoint
theorem and is not re-proved here).

==PART B — THE DELTA STEP==
`Delta.dden` is the differential transfer, rule for rule the one `Delta.dden` in DeltaIR.scala
implements: for environments `old ≤ new` on a set `C` of changing variables,

    (D1)  ⟦s⟧new ⊆ ⟦s⟧old ∪ dden s        (`dden_sound.1`)
    (D2)  dden s ⊆ ⟦s⟧new                  (`dden_sound.2`)

whenever `s` is positive in every changing variable.  From D1 and D2, `delta_step_eq` is the step
equation `A ∪ deltaStep(F, A, lastΔ) = A ∪ F(A)` under the invariant `F(A_prev) ⊆ A`, and
`delta_iteration_eq_naive` is the accumulated-delta / full-iteration equivalence: the semi-naive
recurrence and the naive one produce the SAME accumulator at every round, hence the same stationary
result — which is what `Exec.run(…, verify = true)` re-checks per round and `DeltaIRCheck` asserts.

    proofs/lean/Zippy/Delta.lean#Zippy.Space.varB_sound
    proofs/lean/Zippy/Delta.lean#Zippy.Delta.dden_sound
    proofs/lean/Zippy/Delta.lean#Zippy.Delta.delta_step_eq
    proofs/lean/Zippy/Delta.lean#Zippy.Delta.delta_iteration_eq_naive
==================================================================================================
-/
import Zippy.Positive

namespace Zippy

/-! ## Part A — variance -/

inductive Var where
  | abs | pos | neg | zero
  deriving DecidableEq, Repr

namespace Var

def flip : Var → Var
  | pos => neg
  | neg => pos
  | v => v

/-- both occurrences at once: `+ ⊔ - = 0`, absent is the identity, unknown absorbs -/
def join : Var → Var → Var
  | abs, v => v
  | v, abs => v
  | zero, _ => zero
  | _, zero => zero
  | pos, pos => pos
  | neg, neg => neg
  | _, _ => zero

/-- an argument of variance `v` seen through a position of polarity `pol` -/
def compose : Var → Var → Var
  | _, abs => abs
  | abs, _ => abs
  | pos, v => v
  | neg, v => v.flip
  | zero, _ => zero

def monotone : Var → Bool
  | abs => true
  | pos => true
  | _ => false

def antitone : Var → Bool
  | abs => true
  | neg => true
  | _ => false

@[simp] theorem join_abs_left (v : Var) : join abs v = v := by cases v <;> rfl
@[simp] theorem join_abs_right (v : Var) : join v abs = v := by cases v <;> rfl
@[simp] theorem flip_flip (v : Var) : v.flip.flip = v := by cases v <;> rfl

theorem join_eq_abs {a b : Var} (h : a.join b = abs) : a = abs ∧ b = abs := by
  cases a <;> cases b <;> simp [join] at h ⊢
theorem join_mono {a b : Var} (h : (a.join b).monotone = true) : a.monotone = true ∧ b.monotone = true := by
  cases a <;> cases b <;> simp [join, monotone] at h ⊢
theorem join_anti {a b : Var} (h : (a.join b).antitone = true) : a.antitone = true ∧ b.antitone = true := by
  cases a <;> cases b <;> simp [join, antitone] at h ⊢
/-- a polarity is `pos` or `zero` (the binder rule): a monotone composite has a constant argument or a
positive position with a monotone argument -/
theorem compose_mono {pol v : Var} (hp : pol = pos ∨ pol = zero) (h : (compose pol v).monotone = true) :
    v = abs ∨ (pol = pos ∧ v = pos) := by
  rcases hp with rfl | rfl <;> cases v <;> simp [compose, monotone] at h ⊢
theorem compose_anti {pol v : Var} (hp : pol = pos ∨ pol = zero) (h : (compose pol v).antitone = true) :
    v = abs ∨ (pol = pos ∧ v = neg) := by
  rcases hp with rfl | rfl <;> cases v <;> simp [compose, antitone] at h ⊢
theorem compose_eq_abs {pol v : Var} (hp : pol = pos ∨ pol = zero) (h : compose pol v = abs) : v = abs := by
  rcases hp with rfl | rfl <;> cases v <;> simp [compose] at h ⊢
theorem abs_mono : (abs).monotone = true := rfl
theorem abs_anti : (abs).antitone = true := rfl

end Var

/-- the parameter-variance table of the routines: `none` = an unknown routine -/
abbrev VarTable := Name → Option (List Var)

/-- what a label CLAIMS about two denotations at `X ⊆ Y` -/
def Rel : Var → SpaceV → SpaceV → Prop
  | .pos, A, B => A ⊆ B
  | .neg, A, B => B ⊆ A
  | .abs, A, B => A = B
  | .zero, _, _ => True

/-- what a table ROW demands of two argument lists for the routine's value to grow: a `0` parameter
must not move at all, an unread (`·`) parameter may do anything -/
def ArgRel : Var → SpaceV → SpaceV → Prop
  | .pos, A, B => A ⊆ B
  | .neg, A, B => B ⊆ A
  | .abs, _, _ => True
  | .zero, A, B => A = B

def ArgsRel : List Var → List SpaceV → List SpaceV → Prop
  | [], [], [] => True
  | v :: vs, x :: xs, y :: ys => ArgRel v x y ∧ ArgsRel vs xs ys
  | _, _, _ => False

/-- a routine table is SOUND for `δ` when every routine grows with its arguments as its row says -/
structure VarGood (δ : RoutineEnv) (rt : VarTable) : Prop where
  sound : ∀ r ps xs ys vs, rt r = some vs → ArgsRel vs xs ys → δ r ps xs ⊆ δ r ps ys

theorem ArgRel.refl (v : Var) (A : SpaceV) : ArgRel v A A := by cases v <;> simp [ArgRel]

/-! ### The decision procedure, arm for arm `Variance.of` -/

mutual
  def Space.varB (rt : VarTable) (m : Name) : Space → Var
    | .empty | .lit _ => .abs
    | .mention v => if v = m then .pos else .abs
    | .singleton p => if m ∈ p.freeM then .zero else .abs
    | .union x y | .inter x y | .restriction x y | .composition x y => (x.varB rt m).join (y.varB rt m)
    | .sub x y | .raffination x y => (x.varB rt m).join (y.varB rt m).flip
    | .wrap s p | .unwrap s p => (s.varB rt m).join (if m ∈ p.freeM then .zero else .abs)
    | .tailsUnion s => s.varB rt m
    | .tailsInter s => Var.compose .zero (s.varB rt m)
    | .range x _ _ => Var.compose .zero (x.varB rt m)
    | .iteration src _ rest t =>
        (Var.compose (if (t.varB rt rest).monotone = true then Var.pos else Var.zero) (src.varB rt m)).join
          (if rest = m then Var.abs else t.varB rt m)
    | .fixpoint i r b =>
        Var.compose (if (b.varB rt r).monotone = true then Var.pos else Var.zero)
          ((i.varB rt m).join (if r = m then Var.abs else b.varB rt m))
    | .fold src ini acc sym rest t upd =>
        if m ∈ (Space.fold src ini acc sym rest t upd).freeM then .zero else .abs
    | .call r refs ms =>
        (match rt r with
         | some vs => if vs.length = ms.length then Space.varBs rt m vs ms
                      else Var.compose .zero (Space.varBsAny rt m ms)
         | none => Var.compose .zero (Space.varBsAny rt m ms)).join
          (if m ∈ Path.freeMs refs then Var.zero else Var.abs)
    | .groundedPS p _ => if m ∈ p.freeM then .zero else .abs
    | .groundedSS s _ => Var.compose .zero (s.varB rt m)
  /-- the join over the arguments of a call, each seen through its parameter's polarity -/
  def Space.varBs (rt : VarTable) (m : Name) : List Var → List Space → Var
    | [], [] => .abs
    | v :: vs, s :: ss => (Var.compose v (s.varB rt m)).join (Space.varBs rt m vs ss)
    | [], _ :: _ => .zero            -- unreachable: `varB` calls this on equal lengths only
    | _ :: _, [] => .zero
  /-- the join over a list, every position of unknown polarity -/
  def Space.varBsAny (rt : VarTable) (m : Name) : List Space → Var
    | [] => .abs
    | s :: ss => (s.varB rt m).join (Space.varBsAny rt m ss)
end

/-! ### Lemmas about `Rel` -/

namespace Rel

theorem refl (v : Var) (A : SpaceV) : Rel v A A := by cases v <;> simp [Rel]

theorem of_eq {v : Var} {A B : SpaceV} (h : A = B) : Rel v A B := by cases v <;> simp [Rel, h]

/-- the two-argument composition table for an operator MONOTONE in both arguments -/
theorem binary {f : SpaceV → SpaceV → SpaceV}
    (hf : ∀ a a' b b', a ⊆ a' → b ⊆ b' → f a b ⊆ f a' b')
    {v w : Var} {A A' B B' : SpaceV} (ha : Rel v A A') (hb : Rel w B B') :
    Rel (v.join w) (f A B) (f A' B') := by
  cases v <;> cases w <;> simp only [Rel, Var.join] at *
  all_goals first
    | trivial
    | exact hf _ _ _ _ ha hb
    | (subst ha; exact hf _ _ _ _ subset_rfl hb)
    | (subst hb; exact hf _ _ _ _ ha subset_rfl)
    | (subst ha; subst hb; rfl)

/-- the table for an operator MONOTONE in the first and ANTITONE in the second argument -/
theorem binaryAnti {f : SpaceV → SpaceV → SpaceV}
    (hf : ∀ a a' b b', a ⊆ a' → b' ⊆ b → f a b ⊆ f a' b')
    {v w : Var} {A A' B B' : SpaceV} (ha : Rel v A A') (hb : Rel w B B') :
    Rel (v.join w.flip) (f A B) (f A' B') := by
  cases v <;> cases w <;> simp only [Rel, Var.join, Var.flip] at *
  all_goals first
    | trivial
    | exact hf _ _ _ _ ha hb
    | (subst ha; exact hf _ _ _ _ subset_rfl hb)
    | (subst hb; exact hf _ _ _ _ ha subset_rfl)
    | (subst ha; subst hb; rfl)

/-- a unary operator monotone in its argument preserves every label -/
theorem unary {f : SpaceV → SpaceV} (hf : ∀ a a', a ⊆ a' → f a ⊆ f a') {v : Var} {A A' : SpaceV}
    (ha : Rel v A A') : Rel v (f A) (f A') := by
  cases v with
  | abs => simp only [Rel] at ha ⊢; rw [ha]
  | pos => exact hf _ _ ha
  | neg => exact hf _ _ ha
  | zero => trivial

/-- a position of unknown polarity: constant stays constant, everything else claims nothing -/
theorem composeZero {v : Var} {A A' : SpaceV} (ha : Rel v A A') (f : SpaceV → SpaceV) :
    Rel (Var.compose .zero v) (f A) (f A') := by
  cases v with
  | abs => simp only [Rel, Var.compose] at ha ⊢; rw [ha]
  | pos => trivial
  | neg => trivial
  | zero => trivial

/-- joining with the label of a path (`abs` when it does not read `m`, `zero` when it might) -/
theorem join_pathVar {v : Var} {A B : SpaceV} (ha : Rel v A B) (c : Var) (hc : c = .abs ∨ c = .zero) :
    Rel (v.join c) A B := by
  rcases hc with rfl | rfl
  · simpa using ha
  · cases v <;> simp [Rel, Var.join]

theorem mono_of {v : Var} (hv : v.monotone = true) {A B : SpaceV} (h : Rel v A B) : A ⊆ B := by
  cases v <;> simp [Var.monotone] at hv <;> simp [Rel] at h
  · exact h.le
  · exact h

theorem anti_of {v : Var} (hv : v.antitone = true) {A B : SpaceV} (h : Rel v A B) : B ⊆ A := by
  cases v <;> simp [Var.antitone] at hv <;> simp [Rel] at h
  · exact h.ge
  · exact h

theorem eq_of {A B : SpaceV} (h : Rel .abs A B) : A = B := h

/-- a call argument through its parameter's polarity: a monotone composite yields the argument
relation the row demands, in the growing direction … -/
theorem argRel_of_compose_mono {v w : Var} (h : (Var.compose v w).monotone = true)
    {A B : SpaceV} (hw : Rel w A B) : ArgRel v A B := by
  cases v <;> cases w <;> simp only [Var.compose, Var.monotone, Var.flip, Rel, ArgRel] at h hw ⊢
  all_goals first | trivial | exact hw | exact hw.le | exact hw.ge | exact hw.symm | (cases h)

/-- … and an antitone composite yields it in the shrinking direction -/
theorem argRel_of_compose_anti {v w : Var} (h : (Var.compose v w).antitone = true)
    {A B : SpaceV} (hw : Rel w A B) : ArgRel v B A := by
  cases v <;> cases w <;> simp only [Var.compose, Var.antitone, Var.flip, Rel, ArgRel] at h hw ⊢
  all_goals first | trivial | exact hw | exact hw.le | exact hw.ge | exact hw.symm | (cases h)

end Rel

/-! ### The binder lemmas: chains and unions under a parameter -/

/-- two Kleene chains whose seeds and steps are pointwise ordered are pointwise ordered -/
theorem Kleene.chain_le_chain {I J : SpaceV} {B C : SpaceV → SpaceV} (hI : I ⊆ J)
    (hBC : ∀ Z Z', Z ⊆ Z' → B Z ⊆ C Z') :
    ∀ n, Kleene.chain (fixOp I B) I n ⊆ Kleene.chain (fixOp J C) J n
  | 0 => hI
  | n + 1 => by
      simp only [Kleene.chain, fixOp]
      exact Set.union_subset_union hI (hBC _ _ (Kleene.chain_le_chain hI hBC n))

theorem iUnion_chain_le {I J : SpaceV} {B C : SpaceV → SpaceV} (hI : I ⊆ J)
    (hBC : ∀ Z Z', Z ⊆ Z' → B Z ⊆ C Z') :
    (⋃ n, Kleene.chain (fixOp I B) I n) ⊆ ⋃ n, Kleene.chain (fixOp J C) J n :=
  Set.iUnion_mono fun n => Kleene.chain_le_chain hI hBC n

theorem iUnion_chain_congr {I J : SpaceV} {B C : SpaceV → SpaceV} (hI : I = J)
    (hBC : ∀ Z, B Z = C Z) :
    (⋃ n, Kleene.chain (fixOp I B) I n) = ⋃ n, Kleene.chain (fixOp J C) J n :=
  Set.iUnion_congr fun n => Kleene.chain_congr (fun Z => by simp [fixOp, hI, hBC Z]) hI n

/-- the iteration union as an operator on (source, per-head body) -/
def iterUnion (S : SpaceV) (body : Name → SpaceV → SpaceV) : SpaceV :=
  ⋃ h ∈ heads S, body h (tailsAt h S)

theorem iterUnion_le {S T : SpaceV} {b c : Name → SpaceV → SpaceV} (hST : S ⊆ T)
    (hbc : ∀ h Z Z', Z ⊆ Z' → b h Z ⊆ c h Z') : iterUnion S b ⊆ iterUnion T c := by
  intro e he
  simp only [iterUnion, Set.mem_iUnion] at he ⊢
  obtain ⟨h, hh, hm⟩ := he
  exact ⟨h, heads_mono hST hh, hbc h _ _ (tailsAt_mono h hST) hm⟩

theorem iterUnion_le_same {S : SpaceV} {b c : Name → SpaceV → SpaceV}
    (hbc : ∀ h Z, b h Z ⊆ c h Z) : iterUnion S b ⊆ iterUnion S c := by
  intro e he
  simp only [iterUnion, Set.mem_iUnion] at he ⊢
  obtain ⟨h, hh, hm⟩ := he
  exact ⟨h, hh, hbc h _ hm⟩

theorem iterUnion_congr {S : SpaceV} {b c : Name → SpaceV → SpaceV}
    (hbc : ∀ h Z, b h Z = c h Z) : iterUnion S b = iterUnion S c :=
  Set.iUnion_congr fun h => Set.iUnion_congr fun _ => hbc h _

/-- the pushed environment of an iteration body, at the outer variable's two values -/
private theorem iter_env (ρ : Env) (m sym rest : Name) (X : SpaceV) (h : Name) (T : SpaceV) :
    ((ρ.setM m X).setR sym [h]).setM rest T
      = if rest = m then (ρ.setR sym [h]).setM rest T
        else ((ρ.setR sym [h]).setM rest T).setM m X := by
  split_ifs with hrm
  · subst hrm; exact Env.setR_setM_setM_same ρ sym rest [h] X T
  · exact Env.setR_setM_setM_comm ρ sym [h] X T hrm

private theorem fix_env (ρ : Env) (m r : Name) (X Z : SpaceV) :
    (ρ.setM m X).setM r Z = if r = m then ρ.setM r Z else (ρ.setM r Z).setM m X := by
  split_ifs with hrm
  · subst hrm; exact Env.setM_setM_same ρ r X Z
  · exact Env.setM_setM_comm ρ X Z (fun h => hrm h.symm)

/-! ### Soundness -/

mutual
theorem Space.varB_sound (δ : RoutineEnv) (rt : VarTable) (hδ : VarGood δ rt) :
    ∀ (s : Space) (m : Name) (ρ : Env) (X Y : SpaceV), X ⊆ Y →
      Rel (s.varB rt m) (s.denT δ (ρ.setM m X)) (s.denT δ (ρ.setM m Y))
  | .empty, _, _, _, _, _ => rfl
  | .lit _, _, _, _, _, _ => rfl
  | .mention v, m, ρ, X, Y, hXY => by
      by_cases hv : v = m
      · subst hv; simpa [Space.varB, Space.denT, Rel] using hXY
      · simp [Space.varB, Space.denT, Rel, hv, Env.setM_spaces_ne _ _ hv]
  | .singleton p, m, ρ, X, Y, _ => by
      simp only [Space.varB]
      split_ifs
      · trivial
      · simp [Rel, Space.denT, Path.denT_setM]
  | .union x y, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT]
      exact Rel.binary (fun a a' b b' ha hb => Set.union_subset_union ha hb)
        (Space.varB_sound δ rt hδ x m ρ X Y hXY) (Space.varB_sound δ rt hδ y m ρ X Y hXY)
  | .inter x y, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT]
      exact Rel.binary (fun a a' b b' ha hb => Set.inter_subset_inter ha hb)
        (Space.varB_sound δ rt hδ x m ρ X Y hXY) (Space.varB_sound δ rt hδ y m ρ X Y hXY)
  | .sub x y, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT]
      exact Rel.binaryAnti (fun a a' b b' ha hb => Set.sdiff_subset_sdiff ha hb)
        (Space.varB_sound δ rt hδ x m ρ X Y hXY) (Space.varB_sound δ rt hδ y m ρ X Y hXY)
  | .restriction x y, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT]
      exact Rel.binary (f := fun A B => {e ∈ A | ∃ q ∈ B, q <+: e})
        (fun a a' b b' ha hb e ⟨he, q, hq, hqe⟩ => ⟨ha he, q, hb hq, hqe⟩)
        (Space.varB_sound δ rt hδ x m ρ X Y hXY) (Space.varB_sound δ rt hδ y m ρ X Y hXY)
  | .raffination x y, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT]
      exact Rel.binaryAnti (f := fun A B => A \ {e ∈ A | ∃ q ∈ B, q <+: e})
        (fun a a' b b' ha hb e ⟨he, hne⟩ => ⟨ha he, fun ⟨_, q, hq, hqe⟩ => hne ⟨he, q, hb hq, hqe⟩⟩)
        (Space.varB_sound δ rt hδ x m ρ X Y hXY) (Space.varB_sound δ rt hδ y m ρ X Y hXY)
  | .composition x y, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT]
      exact Rel.binary (f := fun A B => {e | ∃ u ∈ A, ∃ v ∈ B, e = u ++ v})
        (fun a a' b b' ha hb e ⟨u, hu, v, hv, he⟩ => ⟨u, ha hu, v, hb hv, he⟩)
        (Space.varB_sound δ rt hδ x m ρ X Y hXY) (Space.varB_sound δ rt hδ y m ρ X Y hXY)
  | .wrap s p, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT, Path.denT_setM]
      apply Rel.join_pathVar _ _ (by split_ifs <;> simp)
      exact Rel.unary (f := fun A => {e | ∃ u ∈ A, e = p.denT ρ ++ u})
        (fun a a' ha e ⟨u, hu, he⟩ => ⟨u, ha hu, he⟩) (Space.varB_sound δ rt hδ s m ρ X Y hXY)
  | .unwrap s p, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT, Path.denT_setM]
      apply Rel.join_pathVar _ _ (by split_ifs <;> simp)
      exact Rel.unary (f := fun A => {e | p.denT ρ ++ e ∈ A}) (fun a a' ha e he => ha he)
        (Space.varB_sound δ rt hδ s m ρ X Y hXY)
  | .tailsUnion s, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT]
      exact Rel.unary (f := fun A => {t | ∃ h, h :: t ∈ A}) (fun a a' ha t ⟨h, ht⟩ => ⟨h, ha ht⟩)
        (Space.varB_sound δ rt hδ s m ρ X Y hXY)
  | .tailsInter s, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT]
      exact Rel.composeZero (Space.varB_sound δ rt hδ s m ρ X Y hXY)
        (fun A => {t | ∀ h, (∃ t', h :: t' ∈ A) → h :: t ∈ A})
  | .range x _ _, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT]
      exact Rel.composeZero (Space.varB_sound δ rt hδ x m ρ X Y hXY) (fun _ => (∅ : SpaceV))
  | .fold _ _ _ _ _ _ _, m, ρ, X, Y, _ => by
      simp only [Space.varB]; split_ifs <;> simp [Rel, Space.denT]
  | .groundedPS _ _, m, ρ, X, Y, _ => by
      simp only [Space.varB]; split_ifs <;> simp [Rel, Space.denT]
  | .groundedSS s _, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT]
      exact Rel.composeZero (Space.varB_sound δ rt hδ s m ρ X Y hXY) (fun _ => (∅ : SpaceV))
  | .call r refs ms, m, ρ, X, Y, hXY => by
      simp only [Space.varB, Space.denT, Path.denTs_setM]
      apply Rel.join_pathVar _ _ (by split_ifs <;> simp)
      -- constant arguments give a constant call whatever the routine: the fallback both arms share
      have hconst : Rel (Var.compose .zero (Space.varBsAny rt m ms))
          (δ r (Path.denTs ρ refs) (Space.denTs δ (ρ.setM m X) ms))
          (δ r (Path.denTs ρ refs) (Space.denTs δ (ρ.setM m Y) ms)) := by
        have hv := Space.varBsAny_sound δ rt hδ ms m ρ X Y hXY
        cases hva : Space.varBsAny rt m ms
        · show δ r _ (Space.denTs δ (ρ.setM m X) ms) = δ r _ (Space.denTs δ (ρ.setM m Y) ms)
          rw [hv hva]
        all_goals trivial
      cases hrt : rt r with
      | none => exact hconst
      | some vs =>
          by_cases hlen : vs.length = ms.length
          · simp only [hlen, if_true]
            have hmono := Space.varBs_sound_mono δ rt hδ vs ms m ρ X Y hXY
            have hanti := Space.varBs_sound_anti δ rt hδ vs ms m ρ X Y hXY
            cases hva : Space.varBs rt m vs ms
            · show δ r _ (Space.denTs δ (ρ.setM m X) ms) = δ r _ (Space.denTs δ (ρ.setM m Y) ms)
              exact Set.Subset.antisymm (hδ.sound r _ _ _ vs hrt (hmono (by rw [hva]; rfl)))
                (hδ.sound r _ _ _ vs hrt (hanti (by rw [hva]; rfl)))
            · exact hδ.sound r _ _ _ vs hrt (hmono (by rw [hva]; rfl))
            · exact hδ.sound r _ _ _ vs hrt (hanti (by rw [hva]; rfl))
            · trivial
          · simp only [hlen, if_false]
            exact hconst
  | .iteration src sym rest t, m, ρ, X, Y, hXY => by
      have hsrc := Space.varB_sound δ rt hδ src m ρ X Y hXY
      -- the body seen from the outer variable `m`, at a fixed head and tail set …
      have hbodyM : ∀ (h : Name) (T : SpaceV),
          Rel (if rest = m then Var.abs else t.varB rt m)
              (t.denT δ (((ρ.setM m X).setR sym [h]).setM rest T))
              (t.denT δ (((ρ.setM m Y).setR sym [h]).setM rest T)) := by
        intro h T
        rw [iter_env ρ m sym rest X h T, iter_env ρ m sym rest Y h T]
        by_cases hrm : rest = m
        · simp [hrm, Rel]
        · simp only [hrm, if_false]
          exact Space.varB_sound δ rt hδ t m _ X Y hXY
      -- … and from its own tail variable `rest`
      have hbodyR : ∀ (ρ' : Env) (Z Z' : SpaceV), Z ⊆ Z' →
          Rel (t.varB rt rest) (t.denT δ (ρ'.setM rest Z)) (t.denT δ (ρ'.setM rest Z')) :=
        fun ρ' Z Z' hZ => Space.varB_sound δ rt hδ t rest ρ' Z Z' hZ
      -- both sides are `iterUnion`
      show Rel _ (iterUnion (src.denT δ (ρ.setM m X)) fun h T => t.denT δ (((ρ.setM m X).setR sym [h]).setM rest T))
                 (iterUnion (src.denT δ (ρ.setM m Y)) fun h T => t.denT δ (((ρ.setM m Y).setR sym [h]).setM rest T))
      simp only [Space.varB]
      set pol := (if (t.varB rt rest).monotone = true then Var.pos else Var.zero) with hpol
      have hpolc : pol = Var.pos ∨ pol = Var.zero := by rw [hpol]; split_ifs <;> simp
      set vB := (if rest = m then Var.abs else t.varB rt m) with hvB
      set vS := src.varB rt m with hvS
      -- case on the label of the whole iteration
      cases hV : (Var.compose pol vS).join vB
      · -- constant: same source, same bodies
        obtain ⟨hc, hb⟩ := Var.join_eq_abs hV
        have hS : vS = Var.abs := Var.compose_eq_abs hpolc hc
        rw [hS] at hsrc
        have hsrcEq : src.denT δ (ρ.setM m X) = src.denT δ (ρ.setM m Y) := hsrc
        show iterUnion _ _ = iterUnion _ _
        rw [hsrcEq]
        exact iterUnion_congr fun h T => by have := hbodyM h T; rw [hb] at this; exact this
      · -- monotone
        have hj := Var.join_mono (by rw [hV]; rfl)
        rcases Var.compose_mono hpolc hj.1 with hS | ⟨hp, hS⟩
        · -- the source is constant: compare the bodies head by head
          rw [hS] at hsrc
          have hsrcEq : src.denT δ (ρ.setM m X) = src.denT δ (ρ.setM m Y) := hsrc
          show iterUnion _ _ ⊆ iterUnion _ _
          rw [hsrcEq]
          exact iterUnion_le_same fun h T => Rel.mono_of hj.2 (hbodyM h T)
        · -- the source grows and the body is monotone in the tails: `Positive.lean`'s argument
          rw [hS] at hsrc
          have hSsub : src.denT δ (ρ.setM m X) ⊆ src.denT δ (ρ.setM m Y) := hsrc
          have hmonoR : (t.varB rt rest).monotone = true := by
            by_contra hn; simp [hpol, hn] at hp
          show iterUnion _ _ ⊆ iterUnion _ _
          exact iterUnion_le hSsub fun h Z Z' hZ =>
            (Rel.mono_of hmonoR (hbodyR _ Z Z' hZ)).trans (Rel.mono_of hj.2 (hbodyM h Z'))
      · -- antitone
        have hj := Var.join_anti (by rw [hV]; rfl)
        rcases Var.compose_anti hpolc hj.1 with hS | ⟨hp, hS⟩
        · rw [hS] at hsrc
          have hsrcEq : src.denT δ (ρ.setM m X) = src.denT δ (ρ.setM m Y) := hsrc
          show iterUnion _ _ ⊆ iterUnion _ _
          rw [hsrcEq]
          exact iterUnion_le_same fun h T => Rel.anti_of hj.2 (hbodyM h T)
        · rw [hS] at hsrc
          have hSsup : src.denT δ (ρ.setM m Y) ⊆ src.denT δ (ρ.setM m X) := hsrc
          have hmonoR : (t.varB rt rest).monotone = true := by
            by_contra hn; simp [hpol, hn] at hp
          show iterUnion _ _ ⊆ iterUnion _ _
          exact iterUnion_le hSsup fun h Z Z' hZ =>
            (Rel.mono_of hmonoR (hbodyR _ Z Z' hZ)).trans (Rel.anti_of hj.2 (hbodyM h Z'))
      · trivial
  | .fixpoint i r b, m, ρ, X, Y, hXY => by
      have hi := Space.varB_sound δ rt hδ i m ρ X Y hXY
      have hbodyM : ∀ Z : SpaceV,
          Rel (if r = m then Var.abs else b.varB rt m)
              (b.denT δ ((ρ.setM m X).setM r Z)) (b.denT δ ((ρ.setM m Y).setM r Z)) := by
        intro Z
        rw [fix_env ρ m r X Z, fix_env ρ m r Y Z]
        by_cases hrm : r = m
        · simp [hrm, Rel]
        · simp only [hrm, if_false]
          exact Space.varB_sound δ rt hδ b m _ X Y hXY
      have hbodyR : ∀ (ρ' : Env) (Z Z' : SpaceV), Z ⊆ Z' →
          Rel (b.varB rt r) (b.denT δ (ρ'.setM r Z)) (b.denT δ (ρ'.setM r Z')) :=
        fun ρ' Z Z' hZ => Space.varB_sound δ rt hδ b r ρ' Z Z' hZ
      show Rel _ (⋃ n, Kleene.chain (fixOp (i.denT δ (ρ.setM m X)) fun Z => b.denT δ ((ρ.setM m X).setM r Z)) (i.denT δ (ρ.setM m X)) n)
                 (⋃ n, Kleene.chain (fixOp (i.denT δ (ρ.setM m Y)) fun Z => b.denT δ ((ρ.setM m Y).setM r Z)) (i.denT δ (ρ.setM m Y)) n)
      simp only [Space.varB]
      set pol := (if (b.varB rt r).monotone = true then Var.pos else Var.zero) with hpol
      have hpolc : pol = Var.pos ∨ pol = Var.zero := by rw [hpol]; split_ifs <;> simp
      set vB := (if r = m then Var.abs else b.varB rt m) with hvB
      set vI := i.varB rt m with hvI
      cases hV : Var.compose pol (vI.join vB)
      · -- constant
        have hw : vI.join vB = Var.abs := Var.compose_eq_abs hpolc hV
        obtain ⟨hI, hB⟩ := Var.join_eq_abs hw
        rw [hI] at hi
        exact iUnion_chain_congr hi fun Z => by have := hbodyM Z; rw [hB] at this; exact this
      · -- monotone: the body is positive in `r` and both operands grow with `m`
        rcases Var.compose_mono hpolc (by rw [hV]; rfl) with hw | ⟨hp, hw⟩
        · obtain ⟨hI, hB⟩ := Var.join_eq_abs hw
          rw [hI] at hi
          exact (iUnion_chain_congr hi fun Z => by have := hbodyM Z; rw [hB] at this; exact this).le
        · have hj := Var.join_mono (by rw [hw]; rfl)
          have hmonoR : (b.varB rt r).monotone = true := by
            by_contra hn; simp [hpol, hn] at hp
          exact iUnion_chain_le (Rel.mono_of hj.1 hi) fun Z Z' hZ =>
            (Rel.mono_of hmonoR (hbodyR _ Z Z' hZ)).trans (Rel.mono_of hj.2 (hbodyM Z'))
      · -- antitone
        rcases Var.compose_anti hpolc (by rw [hV]; rfl) with hw | ⟨hp, hw⟩
        · obtain ⟨hI, hB⟩ := Var.join_eq_abs hw
          rw [hI] at hi
          exact (iUnion_chain_congr hi fun Z => by have := hbodyM Z; rw [hB] at this; exact this).ge
        · have hj := Var.join_anti (by rw [hw]; rfl)
          have hmonoR : (b.varB rt r).monotone = true := by
            by_contra hn; simp [hpol, hn] at hp
          exact iUnion_chain_le (Rel.anti_of hj.1 hi) fun Z Z' hZ =>
            (Rel.mono_of hmonoR (hbodyR _ Z Z' hZ)).trans (Rel.anti_of hj.2 (hbodyM Z'))
      · trivial

/-- the arguments of a call grow as the row demands when the joined label is monotone -/
theorem Space.varBs_sound_mono (δ : RoutineEnv) (rt : VarTable) (hδ : VarGood δ rt) :
    ∀ (vs : List Var) (ms : List Space) (m : Name) (ρ : Env) (X Y : SpaceV), X ⊆ Y →
      (Space.varBs rt m vs ms).monotone = true →
      ArgsRel vs (Space.denTs δ (ρ.setM m X) ms) (Space.denTs δ (ρ.setM m Y) ms)
  | [], [], _, _, _, _, _, _ => trivial
  | [], _ :: _, _, _, _, _, _, h => by simp [Space.varBs, Var.monotone] at h
  | _ :: _, [], _, _, _, _, _, h => by simp [Space.varBs, Var.monotone] at h
  | v :: vs, s :: ss, m, ρ, X, Y, hXY, h => by
      simp only [Space.varBs] at h
      have hj := Var.join_mono h
      exact ⟨Rel.argRel_of_compose_mono hj.1 (Space.varB_sound δ rt hδ s m ρ X Y hXY),
             Space.varBs_sound_mono δ rt hδ vs ss m ρ X Y hXY hj.2⟩

/-- … and shrink as the row demands when it is antitone -/
theorem Space.varBs_sound_anti (δ : RoutineEnv) (rt : VarTable) (hδ : VarGood δ rt) :
    ∀ (vs : List Var) (ms : List Space) (m : Name) (ρ : Env) (X Y : SpaceV), X ⊆ Y →
      (Space.varBs rt m vs ms).antitone = true →
      ArgsRel vs (Space.denTs δ (ρ.setM m Y) ms) (Space.denTs δ (ρ.setM m X) ms)
  | [], [], _, _, _, _, _, _ => trivial
  | [], _ :: _, _, _, _, _, _, h => by simp [Space.varBs, Var.antitone] at h
  | _ :: _, [], _, _, _, _, _, h => by simp [Space.varBs, Var.antitone] at h
  | v :: vs, s :: ss, m, ρ, X, Y, hXY, h => by
      simp only [Space.varBs] at h
      have hj := Var.join_anti h
      exact ⟨Rel.argRel_of_compose_anti hj.1 (Space.varB_sound δ rt hδ s m ρ X Y hXY),
             Space.varBs_sound_anti δ rt hδ vs ss m ρ X Y hXY hj.2⟩

/-- constant arguments (every position `abs`) denote the same list -/
theorem Space.varBsAny_sound (δ : RoutineEnv) (rt : VarTable) (hδ : VarGood δ rt) :
    ∀ (ms : List Space) (m : Name) (ρ : Env) (X Y : SpaceV), X ⊆ Y →
      Space.varBsAny rt m ms = Var.abs →
      Space.denTs δ (ρ.setM m X) ms = Space.denTs δ (ρ.setM m Y) ms
  | [], _, _, _, _, _, _ => rfl
  | s :: ss, m, ρ, X, Y, hXY, h => by
      simp only [Space.varBsAny] at h
      obtain ⟨hs, hss⟩ := Var.join_eq_abs h
      have h1 := Space.varB_sound δ rt hδ s m ρ X Y hXY
      rw [hs] at h1
      simp only [Space.denTs]
      rw [Rel.eq_of h1, Space.varBsAny_sound δ rt hδ ss m ρ X Y hXY hss]
end

/-! ## Part B — the delta step -/

namespace Delta

/-- `old ≤ new` on the changing variables `C`, equal elsewhere, the same path bindings -/
structure Grows (C : Finset Name) (ρo ρn : Env) : Prop where
  refs : ρo.refs = ρn.refs
  frozen : ∀ v, v ∉ C → ρo.spaces v = ρn.spaces v
  grows : ∀ v, v ∈ C → ρo.spaces v ⊆ ρn.spaces v

theorem Grows.agreeOn {C : Finset Name} {ρo ρn : Env} (h : Grows C ρo ρn) {s : Space}
    (hs : ∀ m ∈ C, m ∉ s.freeM) : Env.AgreeOn s.freeM ρo ρn :=
  ⟨h.refs, fun v hv => h.frozen v (fun hvC => hs v hvC hv)⟩

/-- a frozen term denotes the same thing before and after -/
theorem denT_frozen (δ : RoutineEnv) {C : Finset Name} {ρo ρn : Env} (h : Grows C ρo ρn) (s : Space)
    (hs : ∀ m ∈ C, m ∉ s.freeM) : s.denT δ ρo = s.denT δ ρn :=
  Space.denT_congr δ s ρo ρn (h.agreeOn hs)

theorem Env.setM_self (ρ : Env) (m : Name) : ρ.setM m (ρ.spaces m) = ρ := by
  simp [Env.setM]

/-- a term positive in every changing variable grows from `old` to `new`: monotonicity, one variable
at a time (`Positive.lean`'s `denT_mono`), by induction on the changing set -/
theorem denT_mono_grows (δ : RoutineEnv) (hδ : δ.Good) (s : Space) :
    ∀ (C : Finset Name) (ρo ρn : Env), Grows C ρo ρn → (∀ m ∈ C, s.posB m = true) →
      s.denT δ ρo ⊆ s.denT δ ρn := by
  intro C
  induction C using Finset.induction_on with
  | empty =>
      intro ρo ρn h _
      have : s.denT δ ρo = s.denT δ ρn :=
        Space.denT_congr δ s ρo ρn ⟨h.refs, fun v _ => h.frozen v (Finset.notMem_empty v)⟩
      exact this.le
  | insert m C hm ih =>
      intro ρo ρn h hpos
      -- move `m` first, then the rest
      let ρ1 := ρo.setM m (ρn.spaces m)
      have h1 : Grows C ρ1 ρn := by
        refine ⟨by simp [ρ1, Env.setM, h.refs], fun v hv => ?_, fun v hv => ?_⟩
        · by_cases hvm : v = m
          · subst hvm; simp [ρ1, Env.setM]
          · rw [show ρ1.spaces v = ρo.spaces v from Env.setM_spaces_ne ρo _ hvm]
            exact h.frozen v (by simp [hvm, hv])
        · have hvm : v ≠ m := fun hvm => hm (hvm ▸ hv)
          rw [show ρ1.spaces v = ρo.spaces v from Env.setM_spaces_ne ρo _ hvm]
          exact h.grows v (by simp [hv])
      have step1 : s.denT δ ρo ⊆ s.denT δ ρ1 := by
        have := Space.denT_mono δ hδ s ρo m (ρo.spaces m) (ρn.spaces m)
          (hpos m (Finset.mem_insert_self m C)) (h.grows m (Finset.mem_insert_self m C))
        rwa [Env.setM_self] at this
      exact step1.trans (ih ρ1 ρn h1 fun v hv => hpos v (Finset.mem_insert_of_mem hv))

open Classical in
/-- THE DIFFERENTIAL TRANSFER — rule for rule `Delta.dden` in DeltaIR.scala.  `C` is the set of
changing variables; the two environments are `old` and `new`.  Noncomputable only because the
"is this head old?" test is membership in a `Set` (the executor tests it on a finite trie). -/
noncomputable def dden (δ : RoutineEnv) : Finset Name → Env → Env → Space → SpaceV
  | C, ρo, ρn, .mention v => if v ∈ C then ρn.spaces v \ ρo.spaces v else ∅
  | _, _, _, .empty => ∅
  | _, _, _, .lit _ => ∅
  | _, _, _, .singleton _ => ∅
  | C, ρo, ρn, .union x y => dden δ C ρo ρn x ∪ dden δ C ρo ρn y
  | C, ρo, ρn, .inter x y => (dden δ C ρo ρn x ∩ y.denT δ ρn) ∪ (x.denT δ ρn ∩ dden δ C ρo ρn y)
  | C, ρo, ρn, .composition x y =>
      {e | ∃ u ∈ dden δ C ρo ρn x, ∃ v ∈ y.denT δ ρn, e = u ++ v}
        ∪ {e | ∃ u ∈ x.denT δ ρn, ∃ v ∈ dden δ C ρo ρn y, e = u ++ v}
  | C, ρo, ρn, .restriction x y =>
      {e ∈ dden δ C ρo ρn x | ∃ q ∈ y.denT δ ρn, q <+: e} ∪ {e ∈ x.denT δ ρn | ∃ q ∈ dden δ C ρo ρn y, q <+: e}
  | C, ρo, ρn, .sub x y => dden δ C ρo ρn x \ y.denT δ ρn
  | C, ρo, ρn, .raffination x y => dden δ C ρo ρn x \ {e ∈ x.denT δ ρn | ∃ q ∈ y.denT δ ρn, q <+: e}
  | C, ρo, ρn, .wrap s p => {e | ∃ u ∈ dden δ C ρo ρn s, e = p.denT ρn ++ u}
  | C, ρo, ρn, .unwrap s p => {e | p.denT ρn ++ e ∈ dden δ C ρo ρn s}
  | C, ρo, ρn, .tailsUnion s => {t | ∃ h, h :: t ∈ dden δ C ρo ρn s}
  -- frozen by positivity (`tailsInter`) or outside the fragment: the whole new value / nothing
  | _, _, ρn, .tailsInter s => (Space.tailsInter s).denT δ ρn
  | _, _, _, .range _ _ _ => ∅
  | _, _, _, .fold _ _ _ _ _ _ _ => ∅
  | _, _, _, .groundedPS _ _ => ∅
  | _, _, _, .groundedSS _ _ => ∅
  -- old heads: the body's differential under (rest := old tails → new tails); NEW heads: the body
  | C, ρo, ρn, .iteration src sym rest t =>
      let C' := if (src.freeM ∩ C).Nonempty then insert rest C else C.erase rest
      ⋃ h ∈ heads (src.denT δ ρn),
        if h ∈ heads (src.denT δ ρo) then
          dden δ C' ((ρo.setR sym [h]).setM rest (tailsAt h (src.denT δ ρo)))
                    ((ρn.setR sym [h]).setM rest (tailsAt h (src.denT δ ρn))) t
        else t.denT δ ((ρn.setR sym [h]).setM rest (tailsAt h (src.denT δ ρn)))
  -- sound, not incremental: the whole new value
  | _, _, ρn, .fixpoint i r b => (Space.fixpoint i r b).denT δ ρn
  | _, _, ρn, .call r refs ms => (Space.call r refs ms).denT δ ρn

/-- the two clauses the step equation needs -/
def Sound (δ : RoutineEnv) (C : Finset Name) (ρo ρn : Env) (s : Space) : Prop :=
  s.denT δ ρn ⊆ s.denT δ ρo ∪ dden δ C ρo ρn s ∧ dden δ C ρo ρn s ⊆ s.denT δ ρn

/-- positivity in every changing variable is inherited by the operands of a positive constructor -/
private theorem pos_of_and {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa using h

/-- **D1 and D2, per rule.** -/
theorem dden_sound (δ : RoutineEnv) (hδ : δ.Good) :
    ∀ (s : Space) (C : Finset Name) (ρo ρn : Env), Grows C ρo ρn → (∀ m ∈ C, s.posB m = true) →
      Sound δ C ρo ρn s
  | .empty, C, ρo, ρn, _, _ => ⟨by simp [Space.denT, dden], by simp [dden]⟩
  | .lit _, C, ρo, ρn, _, _ => ⟨by simp [Space.denT, dden], by simp [dden]⟩
  | .singleton p, C, ρo, ρn, h, _ => by
      refine ⟨?_, by simp [dden]⟩
      simp only [Space.denT, dden, Set.union_empty]
      rw [Path.denT_congr h.refs.symm p]
  | .mention v, C, ρo, ρn, h, _ => by
      simp only [Space.denT, dden, Sound]
      split_ifs with hv
      · exact ⟨fun e he => by by_cases heo : e ∈ ρo.spaces v <;> simp [heo, he], Set.sdiff_subset⟩
      · rw [h.frozen v hv]; simp
  | .union x y, C, ρo, ρn, h, hpos => by
      have hx := dden_sound δ hδ x C ρo ρn h fun m hm => (pos_of_and (hpos m hm)).1
      have hy := dden_sound δ hδ y C ρo ρn h fun m hm => (pos_of_and (hpos m hm)).2
      simp only [Sound, Space.denT, dden] at *
      constructor
      · intro e he
        rcases he with he | he
        · rcases hx.1 he with h1 | h1
          · exact Or.inl (Or.inl h1)
          · exact Or.inr (Or.inl h1)
        · rcases hy.1 he with h1 | h1
          · exact Or.inl (Or.inr h1)
          · exact Or.inr (Or.inr h1)
      · exact Set.union_subset_union hx.2 hy.2
  | .inter x y, C, ρo, ρn, h, hpos => by
      have hx := dden_sound δ hδ x C ρo ρn h fun m hm => (pos_of_and (hpos m hm)).1
      have hy := dden_sound δ hδ y C ρo ρn h fun m hm => (pos_of_and (hpos m hm)).2
      simp only [Sound, Space.denT, dden] at *
      constructor
      · intro e ⟨hex, hey⟩
        rcases hx.1 hex with h1 | h1
        · rcases hy.1 hey with h2 | h2
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr (Or.inr ⟨hex, h2⟩)
        · exact Or.inr (Or.inl ⟨h1, hey⟩)
      · intro e he
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨hx.2 h1, h2⟩
        · exact ⟨h1, hy.2 h2⟩
  | .composition x y, C, ρo, ρn, h, hpos => by
      have hx := dden_sound δ hδ x C ρo ρn h fun m hm => (pos_of_and (hpos m hm)).1
      have hy := dden_sound δ hδ y C ρo ρn h fun m hm => (pos_of_and (hpos m hm)).2
      simp only [Sound, Space.denT, dden] at *
      constructor
      · rintro e ⟨u, hu, v, hv, rfl⟩
        rcases hx.1 hu with h1 | h1
        · rcases hy.1 hv with h2 | h2
          · exact Or.inl ⟨u, h1, v, h2, rfl⟩
          · exact Or.inr (Or.inr ⟨u, hu, v, h2, rfl⟩)
        · exact Or.inr (Or.inl ⟨u, h1, v, hv, rfl⟩)
      · rintro e (⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩)
        · exact ⟨u, hx.2 hu, v, hv, rfl⟩
        · exact ⟨u, hu, v, hy.2 hv, rfl⟩
  | .restriction x y, C, ρo, ρn, h, hpos => by
      have hx := dden_sound δ hδ x C ρo ρn h fun m hm => (pos_of_and (hpos m hm)).1
      have hy := dden_sound δ hδ y C ρo ρn h fun m hm => (pos_of_and (hpos m hm)).2
      simp only [Sound, Space.denT, dden] at *
      constructor
      · rintro e ⟨hex, q, hq, hqe⟩
        rcases hx.1 hex with h1 | h1
        · rcases hy.1 hq with h2 | h2
          · exact Or.inl ⟨h1, q, h2, hqe⟩
          · exact Or.inr (Or.inr ⟨hex, q, h2, hqe⟩)
        · exact Or.inr (Or.inl ⟨h1, q, hq, hqe⟩)
      · rintro e (⟨h1, q, hq, hqe⟩ | ⟨h1, q, hq, hqe⟩)
        · exact ⟨hx.2 h1, q, hq, hqe⟩
        · exact ⟨h1, q, hy.2 hq, hqe⟩
  | .sub x y, C, ρo, ρn, h, hpos => by
      have hx := dden_sound δ hδ x C ρo ρn h fun m hm => (pos_of_and (hpos m hm)).1
      have hyf : y.denT δ ρo = y.denT δ ρn :=
        denT_frozen δ h y fun m hm => by simpa using (pos_of_and (hpos m hm)).2
      simp only [Sound, Space.denT, dden] at *
      constructor
      · rintro e ⟨hex, hey⟩
        rcases hx.1 hex with h1 | h1
        · exact Or.inl ⟨h1, hyf ▸ hey⟩
        · exact Or.inr ⟨h1, hey⟩
      · rintro e ⟨h1, h2⟩
        exact ⟨hx.2 h1, h2⟩
  | .raffination x y, C, ρo, ρn, h, hpos => by
      have hx := dden_sound δ hδ x C ρo ρn h fun m hm => (pos_of_and (hpos m hm)).1
      have hyf : y.denT δ ρo = y.denT δ ρn :=
        denT_frozen δ h y fun m hm => by simpa using (pos_of_and (hpos m hm)).2
      simp only [Sound, Space.denT, dden] at *
      constructor
      · rintro e ⟨hex, hne⟩
        rcases hx.1 hex with h1 | h1
        · left; refine ⟨h1, fun ⟨_, q, hq, hqe⟩ => hne ⟨hex, q, hyf ▸ hq, hqe⟩⟩
        · right; exact ⟨h1, hne⟩
      · rintro e ⟨h1, hne⟩
        exact ⟨hx.2 h1, hne⟩
  | .wrap s p, C, ρo, ρn, h, hpos => by
      have hs := dden_sound δ hδ s C ρo ρn h fun m hm => (pos_of_and (hpos m hm)).1
      have hp : p.denT ρo = p.denT ρn := Path.denT_congr h.refs p
      simp only [Sound, Space.denT, dden] at *
      constructor
      · rintro e ⟨u, hu, rfl⟩
        rcases hs.1 hu with h1 | h1
        · exact Or.inl ⟨u, h1, by rw [hp]⟩
        · exact Or.inr ⟨u, h1, rfl⟩
      · rintro e ⟨u, hu, rfl⟩
        exact ⟨u, hs.2 hu, rfl⟩
  | .unwrap s p, C, ρo, ρn, h, hpos => by
      have hs := dden_sound δ hδ s C ρo ρn h fun m hm => (pos_of_and (hpos m hm)).1
      have hp : p.denT ρo = p.denT ρn := Path.denT_congr h.refs p
      simp only [Sound, Space.denT, dden] at *
      constructor
      · intro e he
        rcases hs.1 he with h1 | h1
        · exact Or.inl (by rw [hp]; exact h1)
        · exact Or.inr h1
      · intro e he
        exact hs.2 he
  | .tailsUnion s, C, ρo, ρn, h, hpos => by
      have hs := dden_sound δ hδ s C ρo ρn h fun m hm => hpos m hm
      simp only [Sound, Space.denT, dden] at *
      constructor
      · rintro t ⟨hd, ht⟩
        rcases hs.1 ht with h1 | h1
        · exact Or.inl ⟨hd, h1⟩
        · exact Or.inr ⟨hd, h1⟩
      · rintro t ⟨hd, ht⟩
        exact ⟨hd, hs.2 ht⟩
  | .tailsInter s, C, ρo, ρn, h, hpos => by
      simp only [Sound, dden]
      exact ⟨fun e he => Or.inr he, subset_rfl⟩
  | .range _ _ _, C, ρo, ρn, _, _ => ⟨by simp [Space.denT, dden], by simp [dden]⟩
  | .fold _ _ _ _ _ _ _, C, ρo, ρn, _, _ => ⟨by simp [Space.denT, dden], by simp [dden]⟩
  | .groundedPS _ _, C, ρo, ρn, _, _ => ⟨by simp [Space.denT, dden], by simp [dden]⟩
  | .groundedSS _ _, C, ρo, ρn, _, _ => ⟨by simp [Space.denT, dden], by simp [dden]⟩
  | .fixpoint _ _ _, C, ρo, ρn, _, _ => ⟨fun e he => Or.inr (by simpa [dden] using he), by simp [dden]⟩
  | .call _ _ _, C, ρo, ρn, _, _ => ⟨fun e he => Or.inr (by simpa [dden] using he), by simp [dden]⟩
  | .iteration src sym rest t, C, ρo, ρn, h, hpos => by
      -- positivity of the iteration in every `m ∈ C` unpacks to its two conjuncts
      have hsrcPos : ∀ m ∈ C, m ∈ src.freeM → src.posB m = true ∧ t.posB rest = true := by
        intro m hm hfree
        have := hpos m hm
        simp only [Space.posB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
        rcases this.1 with hnot | hboth
        · exact absurd hfree hnot
        · exact hboth
      have htPos : ∀ m ∈ C, rest ≠ m → t.posB m = true := by
        intro m hm hne
        have := hpos m hm
        simp only [Space.posB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
        rcases this.2 with heq | hp
        · exact absurd heq hne
        · exact hp
      -- the source grows (positivity in every changing variable)
      have hsrcGrow : src.denT δ ρo ⊆ src.denT δ ρn := by
        by_cases hne : (src.freeM ∩ C).Nonempty
        · exact denT_mono_grows δ hδ src C ρo ρn h fun m hm => by
            by_cases hf : m ∈ src.freeM
            · exact (hsrcPos m hm hf).1
            · exact Space.posB_of_notFree src m hf
        · exact (denT_frozen δ h src fun m hm hf =>
            hne ⟨m, Finset.mem_inter.mpr ⟨hf, hm⟩⟩).le
      -- the changing set the body is analysed under, and the two facts about it
      set C' := (if (src.freeM ∩ C).Nonempty then insert rest C else C.erase rest) with hC'
      have hC'pos : ∀ m ∈ C', t.posB m = true := by
        intro m hm
        rw [hC'] at hm
        split_ifs at hm with hne
        · obtain ⟨m₀, hm₀⟩ := hne
          have hm₀C : m₀ ∈ C := (Finset.mem_inter.mp hm₀).2
          have hm₀f : m₀ ∈ src.freeM := (Finset.mem_inter.mp hm₀).1
          rcases Finset.mem_insert.mp hm with rfl | hmC
          · exact (hsrcPos m₀ hm₀C hm₀f).2
          · by_cases hrm : rest = m
            · subst hrm; exact (hsrcPos m₀ hm₀C hm₀f).2
            · exact htPos m hmC hrm
        · have := Finset.mem_erase.mp hm
          exact htPos m this.2 (fun heq => this.1 heq.symm)
      have hsrcFrozenIf : ¬ (src.freeM ∩ C).Nonempty → src.denT δ ρo = src.denT δ ρn := fun hne =>
        denT_frozen δ h src fun m hm hf => hne ⟨m, Finset.mem_inter.mpr ⟨hf, hm⟩⟩
      -- the pushed environments grow on `C'`
      have hgrow : ∀ hd : Name, Grows C' ((ρo.setR sym [hd]).setM rest (tailsAt hd (src.denT δ ρo)))
                                          ((ρn.setR sym [hd]).setM rest (tailsAt hd (src.denT δ ρn))) := by
        intro hd
        refine ⟨by simp [Env.setM, Env.setR, h.refs], fun v hv => ?_, fun v hv => ?_⟩
        · by_cases hvr : v = rest
          · subst hvr
            -- `rest ∉ C'` happens only when the source is frozen
            rw [hC'] at hv
            split_ifs at hv with hne
            · exact absurd (Finset.mem_insert_self _ _) hv
            · simp only [Env.setM, Env.setR, Function.update_self]
              rw [hsrcFrozenIf hne]
          · simp only [Env.setM, Env.setR, Function.update_of_ne hvr]
            apply h.frozen v
            intro hvC
            apply hv
            rw [hC']
            split_ifs
            · exact Finset.mem_insert_of_mem hvC
            · exact Finset.mem_erase.mpr ⟨hvr, hvC⟩
        · by_cases hvr : v = rest
          · subst hvr
            simp only [Env.setM, Env.setR, Function.update_self]
            exact tailsAt_mono _ hsrcGrow
          · simp only [Env.setM, Env.setR, Function.update_of_ne hvr]
            apply h.grows v
            rw [hC'] at hv
            split_ifs at hv
            · exact (Finset.mem_insert.mp hv).resolve_left hvr
            · exact (Finset.mem_erase.mp hv).2
      -- assemble D1 and D2 over the heads
      simp only [Sound, Space.denT, dden]
      rw [← hC']
      constructor
      · intro e he
        simp only [Set.mem_iUnion] at he
        obtain ⟨hd, hhd, he⟩ := he
        by_cases hold : hd ∈ heads (src.denT δ ρo)
        · have ih := dden_sound δ hδ t C' _ _ (hgrow hd) hC'pos
          rcases ih.1 he with h1 | h1
          · left; simp only [Set.mem_iUnion]; exact ⟨hd, hold, h1⟩
          · right; simp only [Set.mem_iUnion]; exact ⟨hd, hhd, by simp [hold, h1]⟩
        · right; simp only [Set.mem_iUnion]; exact ⟨hd, hhd, by simp [hold, he]⟩
      · intro e he
        simp only [Set.mem_iUnion] at he ⊢
        obtain ⟨hd, hhd, he⟩ := he
        by_cases hold : hd ∈ heads (src.denT δ ρo)
        · simp only [hold, if_true] at he
          exact ⟨hd, hhd, (dden_sound δ hδ t C' _ _ (hgrow hd) hC'pos).2 he⟩
        · simp only [hold, if_false] at he
          exact ⟨hd, hhd, he⟩

/-! ### The step equation and the round-for-round equivalence -/

/-- the one-variable step `F A = ⟦b⟧[X := A]` -/
def stepOf (δ : RoutineEnv) (ρ : Env) (b : Space) (X : Name) (A : SpaceV) : SpaceV := b.denT δ (ρ.setM X A)

theorem grows_single (ρ : Env) (X : Name) {Aprev A : SpaceV} (hle : Aprev ⊆ A) :
    Grows {X} (ρ.setM X Aprev) (ρ.setM X A) := by
  refine ⟨rfl, fun v hv => ?_, fun v hv => ?_⟩
  · have hvX : v ≠ X := by simpa using hv
    simp [Env.setM, Function.update_of_ne hvX]
  · have hvX : v = X := by simpa using hv
    subst hvX; simpa [Env.setM] using hle

/-- **THE STEP EQUATION.**  `A ∪ deltaStep(F, A, lastΔ) = A ∪ F(A)` under the invariant that the previous
full step is already in `A` (`F(A_prev) ⊆ A`) — so a delta round adds exactly what a naive round adds. -/
theorem delta_step_eq (δ : RoutineEnv) (hδ : δ.Good) (ρ : Env) (b : Space) (X : Name)
    (hpos : b.posB X = true) (Aprev A : SpaceV) (hle : Aprev ⊆ A)
    (hinv : stepOf δ ρ b X Aprev ⊆ A) :
    A ∪ dden δ {X} (ρ.setM X Aprev) (ρ.setM X A) b = A ∪ stepOf δ ρ b X A := by
  have hs := dden_sound δ hδ b {X} (ρ.setM X Aprev) (ρ.setM X A) (grows_single ρ X hle)
    (fun m hm => by simpa using (show m = X by simpa using hm) ▸ hpos)
  apply Set.Subset.antisymm
  · exact Set.union_subset_union subset_rfl hs.2
  · intro e he
    rcases he with he | he
    · exact Or.inl he
    · rcases hs.1 he with h1 | h1
      · exact Or.inl (hinv h1)
      · exact Or.inr h1

/-- the naive recurrence `A(n+1) = A(n) ∪ F(A(n))` -/
def naive (F : SpaceV → SpaceV) (I : SpaceV) : ℕ → SpaceV
  | 0 => I
  | n + 1 => naive F I n ∪ F (naive F I n)

/-- the semi-naive recurrence: a full first step, then differential steps against the previous two
accumulators (`Exec.solve`'s `Schedule.Delta`) -/
def semi (δ : RoutineEnv) (ρ : Env) (b : Space) (X : Name) (I : SpaceV) : ℕ → SpaceV
  | 0 => I
  | 1 => I ∪ stepOf δ ρ b X I
  | n + 2 => semi δ ρ b X I (n + 1)
              ∪ dden δ {X} (ρ.setM X (semi δ ρ b X I n)) (ρ.setM X (semi δ ρ b X I (n + 1))) b

theorem naive_le_succ (F : SpaceV → SpaceV) (I : SpaceV) (n : ℕ) : naive F I n ⊆ naive F I (n + 1) :=
  Set.subset_union_left

/-- **ACCUMULATED DELTA = FULL ITERATION**, at every round boundary. -/
theorem delta_iteration_eq_naive (δ : RoutineEnv) (hδ : δ.Good) (ρ : Env) (b : Space) (X : Name)
    (hpos : b.posB X = true) (I : SpaceV) :
    ∀ n, semi δ ρ b X I n = naive (stepOf δ ρ b X) I n := by
  -- two consecutive rounds at once, because the semi-naive step reads both
  have pair : ∀ n, semi δ ρ b X I n = naive (stepOf δ ρ b X) I n
                 ∧ semi δ ρ b X I (n + 1) = naive (stepOf δ ρ b X) I (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        show semi δ ρ b X I (n + 2) = naive (stepOf δ ρ b X) I (n + 2)
        simp only [semi, naive]
        rw [ih.1, ih.2]
        exact delta_step_eq δ hδ ρ b X hpos _ _ (naive_le_succ _ I n) Set.subset_union_right
  exact fun n => (pair n).1

/-- hence the same stationary point at the same round -/
theorem delta_stationary_iff (δ : RoutineEnv) (hδ : δ.Good) (ρ : Env) (b : Space) (X : Name)
    (hpos : b.posB X = true) (I : SpaceV) (n : ℕ) :
    semi δ ρ b X I (n + 1) = semi δ ρ b X I n
      ↔ naive (stepOf δ ρ b X) I (n + 1) = naive (stepOf δ ρ b X) I n := by
  rw [delta_iteration_eq_naive δ hδ ρ b X hpos I, delta_iteration_eq_naive δ hδ ρ b X hpos I]

end Delta

end Zippy
