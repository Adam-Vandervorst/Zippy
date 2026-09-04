/-
==================================================================================================
THE UNIVERSAL ZIPPER REFINEMENT THEOREM (plan.md 2A.4).

`transpileZ` (Zipper.scala) lifts a `Space` into a tree of `SpaceZipper` cursors — one virtual node per
local set operator — whose meaning is given OPERATIONALLY: a node answers `terminal` (is the focus path
in the space?) and `descend k` (the cursor one item down), and `materialize` walks those two.  The per-
operator legs `proofs/threeway_*.smt2` and `proofs/impl_*.smt2` certify, one operator at a time, that
a node's two answers realise the operator's set semantics.  What was missing is the statement over
the SYNTAX: for EVERY term of the local algebra, the cursor `transpileZ` builds observes exactly the
set `eval` computes — so the stage-2 cells of the equivalence pipeline can INSTANTIATE one theorem
instead of running a prover on each materialised instance.

==THE MODEL==
`Z` is the zipper program: one constructor per `SpaceZipper` node, with `lit A` standing for both a
`Lit(t)` cursor and an OPAQUE source (2A.4's addition to `SpaceZipper`) — what differs between them
is whether the set is known at transpile time, and the semantics is the same.  `zterm`/`zchild` are
the two cursor operations, each clause transcribed from the corresponding Scala node:

    Union         terminal = a ∨ b        descend k = union (a.k) (b.k)
    Intersection  terminal = a ∧ b        descend k = inter (a.k) (b.k)
    Subtraction   terminal = a ∧ ¬b       descend k = sub (a.k) (b.k)
    Composition   terminal = a ∧ b        descend k = if a.terminal then union (comp a.k b) b.k
                                                       else comp a.k b
    Prefix        terminal = false (mid-prefix) / src.terminal (consumed)
                  descend k = the next prefix node if k is the next item, else ∅
    Restriction   `restriction(x, p)` returns `x` when the prefix cursor is terminal and a
                  `RestrictionNode` (terminal = false) otherwise; `descend k = restriction (x.k) (p.k)`.
                  Both branches are the ONE clause here: terminal = x ∧ p, descend k = if p.terminal
                  then x.k else restr (x.k) (p.k).
    TailsUnion    the union of ALL child cursors of the source (`bigU`; an absent head contributes ∅)
                  — `tailsU s := bigU (s.descend ·)`, which is what the node's lazy `merged` chain is

`TailsIntersection`, `Range` and every non-pointwise constructor MATERIALISE in `transpileZ`
(`traversal(evalI(...))` / `ITrie.tailsIntersection(materialize(src))`), so `zipOf` maps them to a
`lit` of their `denT` value: they are BOUNDARIES of the theorem, and the header of every stage-2 cell
says which ones its shell has.  `Unwrap` is not a node either — `transpileZ` descends at transpile
time — and `zipOf` does the same.

`zmem z p` is what `materialize` reads off: `terminal` at the end of the path, `descend` along it.

==THE THEOREM==
    refinement : zmem (zipOf δ ρ s) p ↔ p ∈ s.denT δ ρ

for every term `s`, environment `ρ` and path `p`.  Each node lemma (`zmem_union`, …) is an
induction on the path and is the syntax-level form of the corresponding `threeway_*` leg; the
theorem composes them by induction on the term.  The correspondence between a Scala node's
`terminal`/`children` and a clause of `zterm`/`zchild` is by transcription, as it is in the SMT legs.

    proofs/lean/Zippy/Zipper.lean#Zippy.Zip.refinement
==================================================================================================
-/
import Zippy.Positive

namespace Zippy.Zip

open Classical

/-- the zipper program -/
inductive Z where
  /-- a concrete cursor (`Lit`) or an OPAQUE source, by the set it denotes -/
  | lit (A : SpaceV)
  | union (a b : Z)
  | inter (a b : Z)
  | sub (a b : Z)
  | comp (a b : Z)
  /-- `Prefix(remaining, src)` -/
  | pfx (ks : List Name) (s : Z)
  /-- `restriction(x, prefixes)` -/
  | restr (x p : Z)
  /-- the union of a family of cursors — `TailsUnion.merged`'s chain over the source's child cursors,
  here over every head (an absent head is the ∅ cursor).  `TailsUnion(src)` IS `bigU (src.descend ·)`:
  the node's `terminal`/`children` are exactly those of the merged chain. -/
  | bigU (f : Name → Z)

namespace Z

mutual
  /-- `terminal` -/
  noncomputable def zterm : Z → Prop
    | lit A => [] ∈ A
    | union a b => zterm a ∨ zterm b
    | inter a b => zterm a ∧ zterm b
    | sub a b => zterm a ∧ ¬ zterm b
    | comp a b => zterm a ∧ zterm b
    | pfx [] s => zterm s
    | pfx (_ :: _) _ => False
    | restr x p => zterm x ∧ zterm p
    | bigU f => ∃ h, zterm (f h)
  /-- `descend k` -/
  noncomputable def zchild : Z → Name → Z
    | lit A, k => lit (tailsAt k A)
    | union a b, k => union (zchild a k) (zchild b k)
    | inter a b, k => inter (zchild a k) (zchild b k)
    | sub a b, k => sub (zchild a k) (zchild b k)
    | comp a b, k =>
        if zterm a then union (comp (zchild a k) b) (zchild b k) else comp (zchild a k) b
    | pfx [] s, k => zchild s k
    | pfx (h :: t) s, k => if k = h then pfx t s else lit ∅
    | restr x p, k => if zterm p then zchild x k else restr (zchild x k) (zchild p k)
    | bigU f, k => bigU fun h => zchild (f h) k
end

/-- what `materialize` reads: `terminal` at the end of the path, `descend` along it -/
noncomputable def zmem (z : Z) : PathV → Prop
  | [] => zterm z
  | k :: q => zmem (zchild z k) q

@[simp] theorem zmem_nil (z : Z) : zmem z [] = zterm z := rfl
@[simp] theorem zmem_cons (z : Z) (k : Name) (q : PathV) : zmem z (k :: q) = zmem (zchild z k) q := rfl

/-! ### The node lemmas — one per `SpaceZipper` node, each an induction on the path -/

theorem zmem_lit : ∀ (p : PathV) (A : SpaceV), zmem (lit A) p ↔ p ∈ A
  | [], A => by simp [zterm]
  | k :: q, A => by
      simp only [zmem_cons, zchild]
      rw [zmem_lit q]
      simp [tailsAt]

theorem zmem_union : ∀ (p : PathV) (a b : Z), zmem (union a b) p ↔ zmem a p ∨ zmem b p
  | [], a, b => by simp [zterm]
  | k :: q, a, b => by simp only [zmem_cons, zchild]; exact zmem_union q _ _

theorem zmem_inter : ∀ (p : PathV) (a b : Z), zmem (inter a b) p ↔ zmem a p ∧ zmem b p
  | [], a, b => by simp [zterm]
  | k :: q, a, b => by simp only [zmem_cons, zchild]; exact zmem_inter q _ _

theorem zmem_sub : ∀ (p : PathV) (a b : Z), zmem (sub a b) p ↔ zmem a p ∧ ¬ zmem b p
  | [], a, b => by simp [zterm]
  | k :: q, a, b => by simp only [zmem_cons, zchild]; exact zmem_sub q _ _

theorem zmem_bigU : ∀ (p : PathV) (f : Name → Z), zmem (bigU f) p ↔ ∃ h, zmem (f h) p
  | [], f => by simp [zterm]
  | k :: q, f => by simp only [zmem_cons, zchild]; exact zmem_bigU q _

/-- `TailsUnion(src)`: the merged chain of the source's child cursors -/
noncomputable def tailsU (s : Z) : Z := bigU fun h => zchild s h

theorem zmem_tailsU (p : PathV) (s : Z) : zmem (tailsU s) p ↔ ∃ h, zmem s (h :: p) := by
  simp only [tailsU, zmem_bigU, zmem_cons]

theorem zmem_prefix : ∀ (ks : List Name) (p : PathV) (s : Z),
    zmem (pfx ks s) p ↔ ∃ q, p = ks ++ q ∧ zmem s q
  | [], p, s => by
      have h0 : ∀ r : PathV, zmem (pfx [] s) r ↔ zmem s r := fun r => by
        cases r <;> simp [zterm, zchild]
      rw [h0]
      constructor
      · intro h; exact ⟨p, by simp, h⟩
      · rintro ⟨q, hq, h⟩; simpa [hq] using h
  | h :: t, [], s => by simp [zterm]
  | h :: t, k :: q, s => by
      simp only [zmem_cons, zchild]
      by_cases hk : k = h
      · subst hk
        simp only [if_true]
        rw [zmem_prefix t q s]
        constructor
        · rintro ⟨q', rfl, hq⟩; exact ⟨q', by simp, hq⟩
        · rintro ⟨q', hq', hq⟩
          simp only [List.cons_append, List.cons.injEq, true_and] at hq'
          exact ⟨q', hq', hq⟩
      · simp only [hk, if_false]
        rw [zmem_lit]
        simp only [Set.mem_empty_iff_false, false_iff, not_exists, not_and]
        intro q' hq'
        simp only [List.cons_append, List.cons.injEq] at hq'
        exact absurd hq'.1 hk

theorem zmem_comp : ∀ (p : PathV) (a b : Z),
    zmem (comp a b) p ↔ ∃ u v, p = u ++ v ∧ zmem a u ∧ zmem b v
  | [], a, b => by
      simp only [zmem_nil, zterm]
      constructor
      · rintro ⟨ha, hb⟩; exact ⟨[], [], rfl, ha, hb⟩
      · rintro ⟨u, v, huv, hu, hv⟩
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv.symm
        exact ⟨hu, hv⟩
  | k :: q, a, b => by
      simp only [zmem_cons, zchild]
      by_cases ha : zterm a
      · simp only [ha, if_true]
        rw [zmem_union, zmem_comp q]
        constructor
        · rintro (⟨u, v, rfl, hu, hv⟩ | hb)
          · exact ⟨k :: u, v, rfl, hu, hv⟩
          · exact ⟨[], k :: q, rfl, ha, hb⟩
        · rintro ⟨u, v, huv, hu, hv⟩
          cases u with
          | nil =>
            simp only [List.nil_append] at huv
            subst huv
            exact Or.inr hv
          | cons u0 u' =>
            simp only [List.cons_append, List.cons.injEq] at huv
            obtain ⟨rfl, rfl⟩ := huv
            exact Or.inl ⟨u', v, rfl, hu, hv⟩
      · simp only [ha, if_false]
        rw [zmem_comp q]
        constructor
        · rintro ⟨u, v, rfl, hu, hv⟩; exact ⟨k :: u, v, rfl, hu, hv⟩
        · rintro ⟨u, v, huv, hu, hv⟩
          cases u with
          | nil => exact absurd hu ha
          | cons u0 u' =>
            simp only [List.cons_append, List.cons.injEq] at huv
            obtain ⟨rfl, rfl⟩ := huv
            exact ⟨u', v, rfl, hu, hv⟩

theorem zmem_restr : ∀ (q : PathV) (x p : Z),
    zmem (restr x p) q ↔ zmem x q ∧ ∃ r, zmem p r ∧ r <+: q
  | [], x, p => by
      simp only [zmem_nil, zterm]
      constructor
      · rintro ⟨hx, hp⟩; exact ⟨hx, [], hp, List.prefix_rfl⟩
      · rintro ⟨hx, r, hr, hrq⟩
        rw [List.prefix_nil.mp hrq] at hr
        exact ⟨hx, hr⟩
  | k :: q, x, p => by
      simp only [zmem_cons, zchild]
      by_cases hp : zterm p
      · simp only [hp, if_true]
        constructor
        · intro hx; exact ⟨hx, [], hp, List.nil_prefix⟩
        · rintro ⟨hx, _⟩; exact hx
      · simp only [hp, if_false]
        rw [zmem_restr q]
        constructor
        · rintro ⟨hx, r, hr, hrq⟩
          exact ⟨hx, k :: r, hr, List.cons_prefix_cons.mpr ⟨rfl, hrq⟩⟩
        · rintro ⟨hx, r, hr, hrq⟩
          cases r with
          | nil => exact absurd hr hp
          | cons r0 r' =>
            obtain ⟨rfl, hrq'⟩ := List.cons_prefix_cons.mp hrq
            exact ⟨hx, r', hr, hrq'⟩

/-- `Unwrap`: descend along the constant prefix at transpile time -/
noncomputable def descendAll (z : Z) : List Name → Z
  | [] => z
  | k :: ks => descendAll (zchild z k) ks

theorem zmem_descendAll : ∀ (ks : List Name) (z : Z) (p : PathV),
    zmem (descendAll z ks) p ↔ zmem z (ks ++ p)
  | [], z, p => Iff.rfl
  | k :: ks, z, p => by simp only [descendAll, List.cons_append, zmem_cons]; exact zmem_descendAll ks _ p

end Z

/-! ### `transpileZ`, as a function on the syntax -/

open Z in
/-- `transpileZ` with every source opaque: the local algebra becomes nodes, everything else
MATERIALISES (`traversal(evalI(...))`) and is a `lit` of its `denT` value — the theorem's boundary. -/
noncomputable def zipOf (δ : RoutineEnv) (ρ : Env) : Space → Z
  | .empty => lit ∅
  | .lit ps => lit {e | e ∈ ps}
  | .mention m => lit (ρ.spaces m)
  | .singleton p => lit {p.denT ρ}
  | .union x y => union (zipOf δ ρ x) (zipOf δ ρ y)
  | .inter x y => inter (zipOf δ ρ x) (zipOf δ ρ y)
  | .sub x y => sub (zipOf δ ρ x) (zipOf δ ρ y)
  | .restriction x y => restr (zipOf δ ρ x) (zipOf δ ρ y)
  -- `raffination(x, y) = Subtraction(x, restriction(x, y))`
  | .raffination x y => sub (zipOf δ ρ x) (restr (zipOf δ ρ x) (zipOf δ ρ y))
  | .composition x y => comp (zipOf δ ρ x) (zipOf δ ρ y)
  | .wrap s p => pfx (p.denT ρ) (zipOf δ ρ s)
  | .unwrap s p => descendAll (zipOf δ ρ s) (p.denT ρ)
  | .tailsUnion s => tailsU (zipOf δ ρ s)
  -- boundaries: materialised by `transpileZ`
  | s@(.tailsInter _) => lit (s.denT δ ρ)
  | s@(.range _ _ _) => lit (s.denT δ ρ)
  | s@(.call _ _ _) => lit (s.denT δ ρ)
  | s@(.iteration _ _ _ _) => lit (s.denT δ ρ)
  | s@(.fixpoint _ _ _) => lit (s.denT δ ρ)
  | s@(.fold _ _ _ _ _ _ _) => lit (s.denT δ ρ)
  | s@(.groundedPS _ _) => lit (s.denT δ ρ)
  | s@(.groundedSS _ _) => lit (s.denT δ ρ)

open Z in
/-- **THE REFINEMENT THEOREM.**  The zipper `transpileZ` builds observes exactly the set the
denotation gives, for every term, environment and path. -/
theorem refinement (δ : RoutineEnv) (ρ : Env) : ∀ (s : Space) (p : PathV),
    zmem (zipOf δ ρ s) p ↔ p ∈ s.denT δ ρ
  | .empty, p => by simp [zipOf, zmem_lit, Space.denT]
  | .lit ps, p => by simp [zipOf, zmem_lit, Space.denT]
  | .mention m, p => by simp [zipOf, zmem_lit, Space.denT]
  | .singleton q, p => by simp [zipOf, zmem_lit, Space.denT]
  | .union x y, p => by
      simp only [zipOf, zmem_union, Space.denT, Set.mem_union]
      rw [refinement δ ρ x p, refinement δ ρ y p]
  | .inter x y, p => by
      simp only [zipOf, zmem_inter, Space.denT, Set.mem_inter_iff]
      rw [refinement δ ρ x p, refinement δ ρ y p]
  | .sub x y, p => by
      simp only [zipOf, zmem_sub, Space.denT, Set.mem_sdiff]
      rw [refinement δ ρ x p, refinement δ ρ y p]
  | .restriction x y, p => by
      simp only [zipOf, zmem_restr, Space.denT, Set.mem_ofPred_eq]
      rw [refinement δ ρ x p]
      constructor
      · rintro ⟨hx, r, hr, hrp⟩; exact ⟨hx, r, (refinement δ ρ y r).mp hr, hrp⟩
      · rintro ⟨hx, r, hr, hrp⟩; exact ⟨hx, r, (refinement δ ρ y r).mpr hr, hrp⟩
  | .raffination x y, p => by
      simp only [zipOf, zmem_sub, zmem_restr, Space.denT, Set.mem_sdiff, Set.mem_ofPred_eq]
      rw [refinement δ ρ x p]
      constructor
      · rintro ⟨hx, hne⟩
        exact ⟨hx, fun ⟨_, r, hr, hrp⟩ => hne ⟨hx, r, (refinement δ ρ y r).mpr hr, hrp⟩⟩
      · rintro ⟨hx, hne⟩
        exact ⟨hx, fun ⟨_, r, hr, hrp⟩ => hne ⟨hx, r, (refinement δ ρ y r).mp hr, hrp⟩⟩
  | .composition x y, p => by
      simp only [zipOf, zmem_comp, Space.denT, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨u, v, rfl, hu, hv⟩
        exact ⟨u, (refinement δ ρ x u).mp hu, v, (refinement δ ρ y v).mp hv, rfl⟩
      · rintro ⟨u, hu, v, hv, rfl⟩
        exact ⟨u, v, rfl, (refinement δ ρ x u).mpr hu, (refinement δ ρ y v).mpr hv⟩
  | .wrap s q, p => by
      simp only [zipOf, zmem_prefix, Space.denT, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨u, rfl, hu⟩; exact ⟨u, (refinement δ ρ s u).mp hu, rfl⟩
      · rintro ⟨u, hu, rfl⟩; exact ⟨u, rfl, (refinement δ ρ s u).mpr hu⟩
  | .unwrap s q, p => by
      simp only [zipOf, zmem_descendAll, Space.denT, Set.mem_ofPred_eq]
      exact refinement δ ρ s _
  | .tailsUnion s, p => by
      simp only [zipOf, zmem_tailsU, Space.denT, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h, hh⟩; exact ⟨h, (refinement δ ρ s _).mp hh⟩
      · rintro ⟨h, hh⟩; exact ⟨h, (refinement δ ρ s _).mpr hh⟩
  | .tailsInter _, p => by simp only [zipOf]; exact zmem_lit p _
  | .range _ _ _, p => by simp only [zipOf]; exact zmem_lit p _
  | .call _ _ _, p => by simp only [zipOf]; exact zmem_lit p _
  | .iteration _ _ _ _, p => by simp only [zipOf]; exact zmem_lit p _
  | .fixpoint _ _ _, p => by simp only [zipOf]; exact zmem_lit p _
  | .fold _ _ _ _ _ _ _, p => by simp only [zipOf]; exact zmem_lit p _
  | .groundedPS _ _, p => by simp only [zipOf]; exact zmem_lit p _
  | .groundedSS _ _, p => by simp only [zipOf]; exact zmem_lit p _

/-- the set form: `materialize (transpileZ s) = eval s` -/
theorem materialize_eq (δ : RoutineEnv) (ρ : Env) (s : Space) :
    {p | Z.zmem (zipOf δ ρ s) p} = s.denT δ ρ := by
  ext p; exact refinement δ ρ s p


/-! ### The first-order shadow's induction schema

`proofs/zipper_refinement.smt2` states the theorem over the key-free fragment as a `Term` datatype and
asserts the structural-induction schema over it (`; ASSUMED: T1`).  This is that datatype, declared as
SMT declares it, and its schema — for every predicate — so the marker has a discharge. -/
inductive Term where
  | leaf (src : SpaceV)
  | tunion (l r : Term) | tinter (l r : Term) | tsub (l r : Term) | tcomp (l r : Term)
  | twrap (k : Name) (s : Term) | tunwrap (k : Name) (s : Term)
  | trestr (l r : Term) | traff (l r : Term)

theorem term_induction (P : Term → Prop)
    (hleaf : ∀ src, P (.leaf src))
    (hunion : ∀ l r, P l → P r → P (.tunion l r)) (hinter : ∀ l r, P l → P r → P (.tinter l r))
    (hsub : ∀ l r, P l → P r → P (.tsub l r)) (hcomp : ∀ l r, P l → P r → P (.tcomp l r))
    (hwrap : ∀ k s, P s → P (.twrap k s)) (hunwrap : ∀ k s, P s → P (.tunwrap k s))
    (hrestr : ∀ l r, P l → P r → P (.trestr l r)) (hraff : ∀ l r, P l → P r → P (.traff l r)) :
    ∀ t, P t
  | .leaf src => hleaf src
  | .tunion l r => hunion l r (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff l)
                              (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff r)
  | .tinter l r => hinter l r (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff l)
                              (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff r)
  | .tsub l r => hsub l r (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff l)
                          (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff r)
  | .tcomp l r => hcomp l r (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff l)
                            (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff r)
  | .twrap k s => hwrap k s (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff s)
  | .tunwrap k s => hunwrap k s (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff s)
  | .trestr l r => hrestr l r (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff l)
                              (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff r)
  | .traff l r => hraff l r (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff l)
                            (term_induction P hleaf hunion hinter hsub hcomp hwrap hunwrap hrestr hraff r)

end Zippy.Zip
