/-
==================================================================================================
DRIVING TRACES INSTANTIATE THE FOLD THEOREM.

`Supercompile.lean` proves the fold theorem PARAMETRICALLY: under `FoldPremises` (the original
meaning is a fixpoint of the residual system, one unfold per node, approximants from ⊥) the residual
system's least fixpoint is the original meaning.  Its header maps each premise to an executable
invariant of `SC.State` — but the `fix` premise bundled three things the implementation only CHECKED
per run: that every law step preserves the denotation, that the unfold is definitional, and that a
fold site is an instance of its node's configuration.  This module turns that bundle into a theorem
about the RUN'S TRACE:

  * a driving step is either a certified-law rewrite at a position (`DStep.law`, whose semantic
    validity is the law's own certificate — an SMT theorem, carried here as the hypothesis it is), or
    a FOLD at a position (`DStep.fold`: the instance `conf g · θ` replaced by the residual call
    `g(θ)`), and a node's body is reached from ONE UNFOLD of its configuration by a finite chain
    of such steps (`DTrace`);
  * `DStep.sound` shows every step preserves the denotation under any CONSISTENT valuation — one
    that gives each residual name the meaning of its configuration — the fold case by C1's
    `instance_denT` and the positional-binding lemma `argEnv_extend_agree`, in any one-hole
    context (`Ctx.plug_congr`);
  * `unfold_step` shows the unfold itself preserves the denotation at every approximant, again by
    `substS_denT`, because a configuration's call has CALL-FREE arguments (`SC.callPositive`);
  * from these, `DriveSystem.premises` DERIVES `FoldPremises` for the mixed valuations
    `μ n` (original names at Kleene depth `n`, residual names at their configuration's depth-`n`
    meaning) and `drive_correct` concludes, through `Fold.resid_lfp_eq_orig`, that every residual
    routine computes exactly its configuration's original meaning.

Nothing about the trace is assumed: the two things a step may claim — a law's validity and an
instance relation — are exactly what `SC.reduceTraced`/`verifyTrace` and `SC.State.checkFold` check
on every run, and what `C3`'s typed trace objects carry.  Configurations are calls to original
routines with call-free arguments (`scCall`/`makeNode`), residual bodies call only residual
routines, original bodies only original ones, and every routine body is closed (its free names are
its parameters): these are the `DriveSystem` fields, each an executable check.
==================================================================================================
-/
import Zippy.SubstSem
import Zippy.Supercompile

namespace Zippy

/-! ### The routine names a term calls -/

mutual
  def Space.calls : Space → Finset Name
    | .empty | .lit _ | .mention _ => ∅
    | .singleton p => p.calls
    | .union x y | .inter x y | .sub x y
    | .restriction x y | .raffination x y | .composition x y => x.calls ∪ y.calls
    | .wrap s p | .unwrap s p => s.calls ∪ p.calls
    | .tailsUnion s | .tailsInter s => s.calls
    | .range x _ _ => x.calls
    | .call r refs ms => insert r (Path.callsL refs ∪ Space.callsL ms)
    | .iteration src _ _ t => src.calls ∪ t.calls
    | .fixpoint i _ b => i.calls ∪ b.calls
    | .fold src ini _ _ _ t upd => src.calls ∪ ini.calls ∪ t.calls ∪ upd.calls
    | .groundedPS p _ => p.calls
    | .groundedSS s _ => s.calls
  def Space.callsL : List Space → Finset Name
    | [] => ∅
    | s :: rest => s.calls ∪ Space.callsL rest
  def Path.calls : Path → Finset Name
    | .deref _ | .const _ => ∅
    | .concat l r => l.calls ∪ r.calls
    | .groundedPP p _ => p.calls
    | .groundedSP s _ => s.calls
  def Path.callsL : List Path → Finset Name
    | [] => ∅
    | p :: rest => p.calls ∪ Path.callsL rest
end

/-- two routine environments agreeing on a set of names -/
def RoutineEnv.AgreeOn (S : Finset Name) (δ δ' : RoutineEnv) : Prop := ∀ r ∈ S, δ r = δ' r

theorem RoutineEnv.AgreeOn.mono {S S' : Finset Name} {δ δ' : RoutineEnv} (h : RoutineEnv.AgreeOn S δ δ')
    (hS : S' ⊆ S) : RoutineEnv.AgreeOn S' δ δ' := fun r hr => h r (hS hr)

/-! `Path.denT` never reads the routine environment, so only `Space.denT` needs the lemma -/

mutual
/-- THE DENOTATION DEPENDS ON THE ROUTINE ENVIRONMENT ONLY AT THE NAMES IT CALLS -/
theorem Space.denT_congr_delta_calls :
    ∀ (s : Space) (δ δ' : RoutineEnv) (ρ : Env), RoutineEnv.AgreeOn s.calls δ δ' → s.denT δ ρ = s.denT δ' ρ
  | .empty, _, _, _, _ => rfl
  | .lit _, _, _, _, _ => rfl
  | .mention _, _, _, _, _ => rfl
  | .singleton _, _, _, _, _ => rfl
  | .union x y, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      simp [Space.denT, Space.denT_congr_delta_calls x δ δ' ρ (h.mono Finset.subset_union_left),
            Space.denT_congr_delta_calls y δ δ' ρ (h.mono Finset.subset_union_right)]
  | .inter x y, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      simp [Space.denT, Space.denT_congr_delta_calls x δ δ' ρ (h.mono Finset.subset_union_left),
            Space.denT_congr_delta_calls y δ δ' ρ (h.mono Finset.subset_union_right)]
  | .sub x y, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      simp [Space.denT, Space.denT_congr_delta_calls x δ δ' ρ (h.mono Finset.subset_union_left),
            Space.denT_congr_delta_calls y δ δ' ρ (h.mono Finset.subset_union_right)]
  | .restriction x y, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      simp [Space.denT, Space.denT_congr_delta_calls x δ δ' ρ (h.mono Finset.subset_union_left),
            Space.denT_congr_delta_calls y δ δ' ρ (h.mono Finset.subset_union_right)]
  | .raffination x y, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      simp [Space.denT, Space.denT_congr_delta_calls x δ δ' ρ (h.mono Finset.subset_union_left),
            Space.denT_congr_delta_calls y δ δ' ρ (h.mono Finset.subset_union_right)]
  | .composition x y, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      simp [Space.denT, Space.denT_congr_delta_calls x δ δ' ρ (h.mono Finset.subset_union_left),
            Space.denT_congr_delta_calls y δ δ' ρ (h.mono Finset.subset_union_right)]
  | .wrap s p, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      simp [Space.denT, Space.denT_congr_delta_calls s δ δ' ρ (h.mono Finset.subset_union_left)]
  | .unwrap s p, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      simp [Space.denT, Space.denT_congr_delta_calls s δ δ' ρ (h.mono Finset.subset_union_left)]
  | .tailsUnion s, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      simp [Space.denT, Space.denT_congr_delta_calls s δ δ' ρ h]
  | .tailsInter s, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      simp [Space.denT, Space.denT_congr_delta_calls s δ δ' ρ h]
  | .range _ _ _, _, _, _, _ => rfl
  | .call r refs ms, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      have hr : δ r = δ' r := h r (Finset.mem_insert_self _ _)
      simp only [Space.denT, hr]
      rw [Space.denTs_congr_delta_calls ms δ δ' ρ
        (h.mono ((Finset.subset_union_right).trans (Finset.subset_insert _ _)))]
  | .iteration src sym rest t, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      have hsrc := Space.denT_congr_delta_calls src δ δ' ρ (h.mono Finset.subset_union_left)
      simp only [Space.denT, hsrc]
      exact Set.iUnion_congr fun hd => Set.iUnion_congr fun _ =>
        Space.denT_congr_delta_calls t δ δ' _ (h.mono Finset.subset_union_right)
  | .fixpoint i r b, δ, δ', ρ, h => by
      simp only [Space.calls] at h
      have hi := Space.denT_congr_delta_calls i δ δ' ρ (h.mono Finset.subset_union_left)
      simp only [Space.denT]
      exact Set.iUnion_congr fun n =>
        Kleene.chain_congr (F := fixOp (i.denT δ ρ) fun X => b.denT δ (ρ.setM r X))
          (fun X => by simp [fixOp, hi, Space.denT_congr_delta_calls b δ δ' (ρ.setM r X) (h.mono Finset.subset_union_right)]) hi n
  | .fold _ _ _ _ _ _ _, _, _, _, _ => rfl
  | .groundedPS _ _, _, _, _, _ => rfl
  | .groundedSS _ _, _, _, _, _ => rfl

theorem Space.denTs_congr_delta_calls :
    ∀ (ms : List Space) (δ δ' : RoutineEnv) (ρ : Env), RoutineEnv.AgreeOn (Space.callsL ms) δ δ' →
      Space.denTs δ ρ ms = Space.denTs δ' ρ ms
  | [], _, _, _, _ => rfl
  | s :: rest, δ, δ', ρ, h => by
      simp only [Space.callsL] at h
      simp [Space.denTs, Space.denT_congr_delta_calls s δ δ' ρ (h.mono Finset.subset_union_left),
            Space.denTs_congr_delta_calls rest δ δ' ρ (h.mono Finset.subset_union_right)]
end

/-! ### One-hole contexts: a step applies at a POSITION -/

/-- a one-hole context over spaces (the hole is a space).  Every constructor that has a space
child gets a context constructor per child; binders included — a step under a binder is still a
step, because the semantic steps below hold under every environment. -/
inductive Ctx where
  | hole
  | unionL (c : Ctx) (y : Space) | unionR (x : Space) (c : Ctx)
  | interL (c : Ctx) (y : Space) | interR (x : Space) (c : Ctx)
  | subL (c : Ctx) (y : Space) | subR (x : Space) (c : Ctx)
  | restrictionL (c : Ctx) (y : Space) | restrictionR (x : Space) (c : Ctx)
  | raffinationL (c : Ctx) (y : Space) | raffinationR (x : Space) (c : Ctx)
  | compositionL (c : Ctx) (y : Space) | compositionR (x : Space) (c : Ctx)
  | wrap (c : Ctx) (p : Path) | unwrap (c : Ctx) (p : Path)
  | tailsUnion (c : Ctx) | tailsInter (c : Ctx)
  | range (c : Ctx) (lo hi : Int)
  | callArg (r : Name) (refs : List Path) (before : List Space) (c : Ctx) (after : List Space)
  | iterationSrc (c : Ctx) (sym rest : Name) (t : Space)
  | iterationBody (src : Space) (sym rest : Name) (c : Ctx)
  | fixpointInit (c : Ctx) (r : Name) (b : Space)
  | fixpointBody (i : Space) (r : Name) (c : Ctx)

def Ctx.plug : Ctx → Space → Space
  | .hole, s => s
  | .unionL c y, s => .union (c.plug s) y
  | .unionR x c, s => .union x (c.plug s)
  | .interL c y, s => .inter (c.plug s) y
  | .interR x c, s => .inter x (c.plug s)
  | .subL c y, s => .sub (c.plug s) y
  | .subR x c, s => .sub x (c.plug s)
  | .restrictionL c y, s => .restriction (c.plug s) y
  | .restrictionR x c, s => .restriction x (c.plug s)
  | .raffinationL c y, s => .raffination (c.plug s) y
  | .raffinationR x c, s => .raffination x (c.plug s)
  | .compositionL c y, s => .composition (c.plug s) y
  | .compositionR x c, s => .composition x (c.plug s)
  | .wrap c p, s => .wrap (c.plug s) p
  | .unwrap c p, s => .unwrap (c.plug s) p
  | .tailsUnion c, s => .tailsUnion (c.plug s)
  | .tailsInter c, s => .tailsInter (c.plug s)
  | .range c lo hi, s => .range (c.plug s) lo hi
  | .callArg r refs before c after, s => .call r refs (before ++ c.plug s :: after)
  | .iterationSrc c sym rest t, s => .iteration (c.plug s) sym rest t
  | .iterationBody src sym rest c, s => .iteration src sym rest (c.plug s)
  | .fixpointInit c r b, s => .fixpoint (c.plug s) r b
  | .fixpointBody i r c, s => .fixpoint i r (c.plug s)

theorem Space.denTs_append (δ : RoutineEnv) (ρ : Env) :
    ∀ (xs ys : List Space), Space.denTs δ ρ (xs ++ ys) = Space.denTs δ ρ xs ++ Space.denTs δ ρ ys
  | [], _ => rfl
  | x :: xs, ys => by simp [Space.denTs, Space.denTs_append δ ρ xs ys]

/-- a semantic step at a position is a semantic step of the whole term -/
theorem Ctx.plug_congr (δ : RoutineEnv) {a b : Space} (h : ∀ ρ, a.denT δ ρ = b.denT δ ρ) :
    ∀ (c : Ctx) (ρ : Env), (c.plug a).denT δ ρ = (c.plug b).denT δ ρ
  | .hole, ρ => h ρ
  | .unionL c y, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .unionR x c, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .interL c y, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .interR x c, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .subL c y, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .subR x c, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .restrictionL c y, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .restrictionR x c, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .raffinationL c y, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .raffinationR x c, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .compositionL c y, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .compositionR x c, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .wrap c p, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .unwrap c p, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .tailsUnion c, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .tailsInter c, ρ => by simp [Ctx.plug, Space.denT, Ctx.plug_congr δ h c ρ]
  | .range c lo hi, ρ => by simp [Ctx.plug, Space.denT]
  | .callArg r refs before c after, ρ => by
      simp only [Ctx.plug, Space.denT]
      rw [Space.denTs_append, Space.denTs_append]
      simp [Space.denTs, Ctx.plug_congr δ h c ρ]
  | .iterationSrc c sym rest t, ρ => by
      simp only [Ctx.plug, Space.denT]
      rw [Ctx.plug_congr δ h c ρ]
  | .iterationBody src sym rest c, ρ => by
      simp only [Ctx.plug, Space.denT]
      exact Set.iUnion_congr fun hd => Set.iUnion_congr fun _ => Ctx.plug_congr δ h c _
  | .fixpointInit c r b, ρ => by
      simp only [Ctx.plug, Space.denT]
      rw [Ctx.plug_congr δ h c ρ]
  | .fixpointBody i r c, ρ => by
      simp only [Ctx.plug, Space.denT]
      exact Set.iUnion_congr fun n =>
        Kleene.chain_congr (F := fixOp (i.denT δ ρ) fun X => (c.plug a).denT δ (ρ.setM r X))
          (fun X => by simp [fixOp, Ctx.plug_congr δ h c (ρ.setM r X)]) rfl n

/-! ### Chains of semantic steps -/

/-- a finite chain of steps, each preserving the denotation under `μ` -/
inductive Chain (μ : RoutineEnv) : Space → Space → Prop
  | refl (a : Space) : Chain μ a a
  | step {a b c : Space} (h : ∀ ρ, a.denT μ ρ = b.denT μ ρ) (rest : Chain μ b c) : Chain μ a c

theorem Chain.denT_eq {μ : RoutineEnv} {a b : Space} (c : Chain μ a b) : ∀ ρ, a.denT μ ρ = b.denT μ ρ := by
  induction c with
  | refl _ => intro ρ; rfl
  | step h _ ih => intro ρ; exact (h ρ).trans (ih ρ)

theorem Chain.trans {μ : RoutineEnv} {a b c : Space} (h₁ : Chain μ a b) (h₂ : Chain μ b c) : Chain μ a c := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact Chain.step h (ih h₂)

/-! ### Positional binding agrees with the substitution's environment

`Resid.argEnv T g ps xs` binds the parameters POSITIONALLY over the base environment; `Env.extend`
binds by lookup in a substitution list.  On the body's free names — which are among the parameters
for a closed routine — they agree, argument for argument. -/

theorem Resid.bindM_spaces (ρ0 : Env) (δ : RoutineEnv) (ρ : Env) :
    ∀ (params : List Name) (xs : List Space) (m : Name), params.length = xs.length →
      (Resid.bindM ρ0 params (Space.denTs δ ρ xs)).spaces m
        = match lookupM (params.zip xs) m with | some t => t.denT δ ρ | none => ρ0.spaces m
  | [], [], m, _ => by simp [Resid.bindM, List.zip, lookupM]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | n :: ns, x :: xs, m, h => by
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [Space.denTs, Resid.bindM, List.zip_cons_cons, lookupM]
      by_cases hmn : n = m
      · subst hmn; simp
      · rw [Env.setM_spaces_ne _ _ (fun h' => hmn h'.symm)]
        simp only [hmn, if_false]
        exact Resid.bindM_spaces ρ0 δ ρ ns xs m h

theorem Resid.bindM_refs (ρ0 : Env) : ∀ (params : List Name) (xs : List SpaceV),
    (Resid.bindM ρ0 params xs).refs = ρ0.refs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | n :: ns, x :: xs => by simp [Resid.bindM, Env.setM_refs, Resid.bindM_refs ρ0 ns xs]

theorem Resid.bindR_refs (ρ0 : Env) (ρ : Env) :
    ∀ (params : List Name) (ps : List Path) (r : Name), params.length = ps.length →
      (Resid.bindR ρ0 params (Path.denTs ρ ps)).refs r
        = match lookupR (params.zip ps) r with | some p => p.denT ρ | none => ρ0.refs r
  | [], [], r, _ => by simp [Resid.bindR, List.zip, lookupR]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | n :: ns, p :: ps, r, h => by
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [Path.denTs, Resid.bindR, List.zip_cons_cons, lookupR]
      by_cases hrn : n = r
      · subst hrn; simp [Env.setR]
      · simp only [Env.setR, Function.update_of_ne (fun h' => hrn h'.symm), hrn, if_false]
        exact Resid.bindR_refs ρ0 ρ ns ps r h

theorem Resid.bindR_spaces (ρ0 : Env) : ∀ (params : List Name) (ps : List PathV),
    (Resid.bindR ρ0 params ps).spaces = ρ0.spaces
  | [], _ => rfl
  | _ :: _, [] => rfl
  | n :: ns, p :: ps => by simp [Resid.bindR, Env.setR_spaces, Resid.bindR_spaces ρ0 ns ps]

/-- a name looked up in a zip is one of the parameters -/
theorem lookupM_zip_mem : ∀ (params : List Name) (xs : List Space) (m : Name) (t : Space),
    lookupM (params.zip xs) m = some t → m ∈ params
  | [], _, _, _, h => by simp [List.zip, lookupM] at h
  | _ :: _, [], _, _, h => by simp [List.zip, lookupM] at h
  | n :: ns, x :: xs, m, t, h => by
      simp only [List.zip_cons_cons, lookupM] at h
      split at h
      · rename_i heq; exact heq ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (lookupM_zip_mem ns xs m t h)

theorem lookupR_zip_mem : ∀ (params : List Name) (ps : List Path) (r : Name) (p : Path),
    lookupR (params.zip ps) r = some p → r ∈ params
  | [], _, _, _, h => by simp [List.zip, lookupR] at h
  | _ :: _, [], _, _, h => by simp [List.zip, lookupR] at h
  | n :: ns, q :: ps, r, p, h => by
      simp only [List.zip_cons_cons, lookupR] at h
      split at h
      · rename_i heq; exact heq ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (lookupR_zip_mem ns ps r p h)

/-- a parameter always has an argument when the lists have equal length -/
theorem lookupR_zip_of_mem : ∀ (params : List Name) (ps : List Path) (r : Name),
    params.length = ps.length → r ∈ params → ∃ p, lookupR (params.zip ps) r = some p
  | [], _, _, _, hmem => by simp at hmem
  | _ :: _, [], _, h, _ => by simp at h
  | n :: ns, q :: qs, r, h, hmem => by
      simp only [List.zip_cons_cons, lookupR]
      by_cases hnr : n = r
      · exact ⟨q, by simp [hnr]⟩
      · simp only [hnr, if_false]
        have hlen : ns.length = qs.length := by simpa using h
        have hmem' : r ∈ ns := by
          rcases List.mem_cons.mp hmem with heq | hin
          · exact absurd heq.symm hnr
          · exact hin
        exact lookupR_zip_of_mem ns qs r hlen hmem'

theorem lookupM_zip_of_mem : ∀ (params : List Name) (xs : List Space) (m : Name),
    params.length = xs.length → m ∈ params → ∃ t, lookupM (params.zip xs) m = some t
  | [], _, _, _, hmem => by simp at hmem
  | _ :: _, [], _, h, _ => by simp at h
  | n :: ns, x :: xs, m, h, hmem => by
      simp only [List.zip_cons_cons, lookupM]
      by_cases hnm : n = m
      · exact ⟨x, by simp [hnm]⟩
      · simp only [hnm, if_false]
        have hlen : ns.length = xs.length := by simpa using h
        have hmem' : m ∈ ns := by
          rcases List.mem_cons.mp hmem with heq | hin
          · exact absurd heq.symm hnm
          · exact hin
        exact lookupM_zip_of_mem ns xs m hlen hmem'

theorem Env.AgreeRM.symm {R M : Finset Name} {ρ ρ' : Env} (h : Env.AgreeRM R M ρ ρ') : Env.AgreeRM R M ρ' ρ :=
  ⟨fun r hr => (h.1 r hr).symm, fun m hm => (h.2 m hm).symm⟩

/-- THE AGREEMENT: on a body whose free names are among the parameters, the positional argument
environment equals the substitution's extension of ANY caller environment `ρ` (the body never reads
the caller's other names) -/
theorem argEnv_extend_agree (T : Resid.Table) (δ : RoutineEnv) (ρ : Env) (g : Name)
    (refs : List Path) (ms : List Space) (body : Space)
    (hR : body.freeR ⊆ (T.refs g).toFinset) (hM : body.freeM ⊆ (T.ments g).toFinset)
    (hlR : (T.refs g).length = refs.length) (hlM : (T.ments g).length = ms.length) :
    Env.AgreeRM body.freeR body.freeM
      (Env.extend δ ρ ((T.ments g).zip ms) ((T.refs g).zip refs))
      (Resid.argEnv T g (Path.denTs ρ refs) (Space.denTs δ ρ ms)) := by
  refine ⟨fun r hr => ?_, fun m hm => ?_⟩
  · have hmem : r ∈ T.refs g := by simpa using hR hr
    obtain ⟨p, hp⟩ := lookupR_zip_of_mem (T.refs g) refs r hlR hmem
    show (Env.extend δ ρ ((T.ments g).zip ms) ((T.refs g).zip refs)).refs r
      = (Resid.bindM (Resid.bindR Resid.Env.base (T.refs g) (Path.denTs ρ refs)) (T.ments g) (Space.denTs δ ρ ms)).refs r
    rw [Resid.bindM_refs, Resid.bindR_refs Resid.Env.base ρ (T.refs g) refs r hlR, Env.extend_refs_some δ ρ _ hp]
    simp [hp]
  · have hmem : m ∈ T.ments g := by simpa using hM hm
    obtain ⟨t, ht⟩ := lookupM_zip_of_mem (T.ments g) ms m hlM hmem
    show (Env.extend δ ρ ((T.ments g).zip ms) ((T.refs g).zip refs)).spaces m
      = (Resid.bindM (Resid.bindR Resid.Env.base (T.refs g) (Path.denTs ρ refs)) (T.ments g) (Space.denTs δ ρ ms)).spaces m
    rw [Resid.bindM_spaces _ δ ρ (T.ments g) ms m hlM, Env.extend_spaces_some δ ρ _ ht]
    simp [ht]

/-! ### The unfold and the fold, as semantic steps -/

/-- ONE UNFOLD of a call: the callee's body with the arguments substituted (`SC.State.unfold`,
`Lower.inline`), as a term -/
def unfoldOnce (F : FreshSupply) (O : Resid.Table) (r : Name) (refs : List Path) (ms : List Space) : Space :=
  substS F ((O.ments r).zip ms) ((O.refs r).zip refs) (O.body r)

/-- THE UNFOLD STEP.  Under a valuation that is `sys O`-consistent at `r` (reading `r`'s body under
`δ` gives `δ' r`) and arguments whose value is the same at `δ` and `δ'` (call-free arguments: the
same at every depth), unfolding a call equals the call — at the fixpoint `δ = δ'`; at an approximant,
`δ' = iter (n+1)` and `δ = iter n`. -/
theorem unfold_step (F : FreshSupply) (O : Resid.Table) (δ δ' : RoutineEnv) (ρ : Env) (r : Name)
    (refs : List Path) (ms : List Space)
    (hR : (O.body r).freeR ⊆ (O.refs r).toFinset) (hM : (O.body r).freeM ⊆ (O.ments r).toFinset)
    (hlR : (O.refs r).length = refs.length) (hlM : (O.ments r).length = ms.length)
    (hfix : δ' r = fun ps xs => (O.body r).denT δ (Resid.argEnv O r ps xs))
    (hargs : Space.denTs δ' ρ ms = Space.denTs δ ρ ms) :
    (Space.call r refs ms).denT δ' ρ = (unfoldOnce F O r refs ms).denT δ ρ := by
  simp only [Space.denT, unfoldOnce, hfix, hargs]
  rw [substS_denT F δ (O.body r) _ _ ρ]
  exact (Space.denT_congr_rm δ (O.body r) _ _ (argEnv_extend_agree O δ ρ r refs ms (O.body r) hR hM hlR hlM)).symm

/-- the argument lists a fold builds: each parameter replaced by its instance, or left as itself
(`SC.State.callOf`) -/
def foldArgsM (θm : List (Name × Space)) (params : List Name) : List Space :=
  params.map fun m => (lookupM θm m).getD (.mention m)
def foldArgsR (θp : List (Name × Path)) (params : List Name) : List Path :=
  params.map fun r => (lookupR θp r).getD (.deref r)

theorem foldArgsM_denTs (δ : RoutineEnv) (ρ : Env) (θm : List (Name × Space)) (θp : List (Name × Path)) :
    ∀ params : List Name, Space.denTs δ ρ (foldArgsM θm params) = params.map fun m => (Env.extend δ ρ θm θp).spaces m
  | [] => rfl
  | m :: rest => by
      have hcons : foldArgsM θm (m :: rest) = ((lookupM θm m).getD (.mention m)) :: foldArgsM θm rest := rfl
      rw [hcons, List.map_cons]
      simp only [Space.denTs]
      rw [foldArgsM_denTs δ ρ θm θp rest]
      congr 1
      cases h : lookupM θm m with
      | none => simp [Space.denT, Env.extend_spaces_none δ ρ θp h]
      | some t => simp [Env.extend_spaces_some δ ρ θp h]

theorem foldArgsR_denTs (δ : RoutineEnv) (ρ : Env) (θm : List (Name × Space)) (θp : List (Name × Path)) :
    ∀ params : List Name, Path.denTs ρ (foldArgsR θp params) = params.map fun r => (Env.extend δ ρ θm θp).refs r
  | [] => rfl
  | r :: rest => by
      have hcons : foldArgsR θp (r :: rest) = ((lookupR θp r).getD (.deref r)) :: foldArgsR θp rest := rfl
      rw [hcons, List.map_cons]
      simp only [Path.denTs]
      rw [foldArgsR_denTs δ ρ θm θp rest]
      congr 1
      cases h : lookupR θp r with
      | none => simp [Path.denT, Env.extend_refs_none δ ρ θm h]
      | some p => simp [Env.extend_refs_some δ ρ θm h]

/-- binding a parameter list to its own values (as read from `ρ'`) reads `ρ'` on the parameters -/
theorem Resid.bindR_self (ρ0 ρ' : Env) : ∀ (params : List Name) (r : Name), r ∈ params →
    (Resid.bindR ρ0 params (params.map fun r => ρ'.refs r)).refs r = ρ'.refs r
  | [], _, hmem => by simp at hmem
  | n :: ns, r, hmem => by
      simp only [List.map_cons, Resid.bindR]
      by_cases hnr : n = r
      · subst hnr; simp [Env.setR]
      · simp only [Env.setR, Function.update_of_ne (fun h => hnr h.symm)]
        have hmem' : r ∈ ns := by
          rcases List.mem_cons.mp hmem with heq | hin
          · exact absurd heq.symm hnr
          · exact hin
        exact Resid.bindR_self ρ0 ρ' ns r hmem'

theorem Resid.bindM_self (ρ0 ρ' : Env) : ∀ (params : List Name) (m : Name), m ∈ params →
    (Resid.bindM ρ0 params (params.map fun m => ρ'.spaces m)).spaces m = ρ'.spaces m
  | [], _, hmem => by simp at hmem
  | n :: ns, m, hmem => by
      simp only [List.map_cons, Resid.bindM]
      by_cases hnm : n = m
      · subst hnm; simp
      · rw [Env.setM_spaces_ne _ _ (fun h => hnm h.symm)]
        have hmem' : m ∈ ns := by
          rcases List.mem_cons.mp hmem with heq | hin
          · exact absurd heq.symm hnm
          · exact hin
        exact Resid.bindM_self ρ0 ρ' ns m hmem'

theorem argEnv_of_values (T : Resid.Table) (g : Name) (ρ' : Env) (body : Space)
    (hR : body.freeR ⊆ (T.refs g).toFinset) (hM : body.freeM ⊆ (T.ments g).toFinset) :
    Env.AgreeRM body.freeR body.freeM
      (Resid.argEnv T g ((T.refs g).map fun r => ρ'.refs r) ((T.ments g).map fun m => ρ'.spaces m)) ρ' := by
  refine ⟨fun r hr => ?_, fun m hm => ?_⟩
  · have hmem : r ∈ T.refs g := by simpa using hR hr
    show (Resid.bindM (Resid.bindR Resid.Env.base (T.refs g) _) (T.ments g) _).refs r = ρ'.refs r
    rw [Resid.bindM_refs]
    exact Resid.bindR_self Resid.Env.base ρ' (T.refs g) r hmem
  · have hmem : m ∈ T.ments g := by simpa using hM hm
    show (Resid.bindM (Resid.bindR Resid.Env.base (T.refs g) _) (T.ments g) _).spaces m = ρ'.spaces m
    exact Resid.bindM_self _ ρ' (T.ments g) m hmem

/-- THE FOLD STEP.  A residual name `g` whose configuration `gc` is closed by `T`'s parameters
for `g`, under a valuation `μ` CONSISTENT at `g` (`μ g ps xs` is `gc` read at the arguments): the
instance `gc·θ` denotes the residual call `g(θ)`. -/
theorem fold_step (F : FreshSupply) (T : Resid.Table) (μ : RoutineEnv) (ρ : Env) (g : Name) (gc : Space)
    (θm : List (Name × Space)) (θp : List (Name × Path))
    (hR : gc.freeR ⊆ (T.refs g).toFinset) (hM : gc.freeM ⊆ (T.ments g).toFinset)
    (hcons : μ g = fun ps xs => gc.denT μ (Resid.argEnv T g ps xs)) :
    (substS F θm θp gc).denT μ ρ
      = (Space.call g (foldArgsR θp (T.refs g)) (foldArgsM θm (T.ments g))).denT μ ρ := by
  simp only [Space.denT, hcons]
  rw [substS_denT F μ gc θm θp ρ, foldArgsM_denTs μ ρ θm θp, foldArgsR_denTs μ ρ θm θp]
  exact Space.denT_congr_rm μ gc _ _ (argEnv_of_values T g (Env.extend μ ρ θm θp) gc hR hM).symm


/-! ### A call with call-free arguments reads the routine environment at one name only -/

theorem call_denT_congr {δ δ' : RoutineEnv} (ρ : Env) (r : Name) (refs : List Path) (ms : List Space)
    (hr : δ r = δ' r) (hms : Space.hasCalls ms = false) :
    (Space.call r refs ms).denT δ ρ = (Space.call r refs ms).denT δ' ρ := by
  simp only [Space.denT, hr, Space.denTs_congr_delta_of_noCall δ δ' ρ ms hms]

/-! ### THE DRIVE SYSTEM — what `SC.State` guarantees, as fields -/

/-- a supercompilation run: the original table, the residual bodies, each residual name's
configuration and parameters, and the invariants `SC.State` checks (see the header) -/
structure DriveSystem where
  F : FreshSupply
  /-- the original routines -/
  O : Resid.Table
  /-- the residual bodies, parameters (the configuration's free names), configurations -/
  Tb : Name → Space
  Trefs : Name → List Name
  Tments : Name → List Name
  conf : Name → Space
  Onames : Finset Name
  Tnames : Finset Name
  disjoint : Disjoint Onames Tnames
  /-- every configuration is a call to an original routine with CALL-FREE arguments (`scCall`,
  `SC.callPositive`), of the right arity -/
  confCall : ∀ g ∈ Tnames, ∃ r refs ms, r ∈ Onames ∧ conf g = .call r refs ms ∧
      Path.hasCalls refs = false ∧ Space.hasCalls ms = false ∧
      (O.refs r).length = refs.length ∧ (O.ments r).length = ms.length
  /-- original bodies are closed, call original names only, and are positive -/
  Oclosed : ∀ r, (O.body r).freeR ⊆ (O.refs r).toFinset ∧ (O.body r).freeM ⊆ (O.ments r).toFinset
  Ocalls : ∀ r, (O.body r).calls ⊆ Onames
  Opos : ∀ r, (O.body r).callPosB = true
  /-- a configuration's free names are its residual routine's parameters (`paramsOf`) -/
  Tclosed : ∀ g ∈ Tnames, (conf g).freeR ⊆ (Trefs g).toFinset ∧ (conf g).freeM ⊆ (Tments g).toFinset
  /-- residual bodies are positive (`SC.State.residualPositive`) -/
  Tpos : ∀ g ∈ Tnames, (Tb g).callPosB = true

namespace DriveSystem

variable (D : DriveSystem)

/-- the COMBINED table: residual bodies on residual names, original bodies elsewhere -/
def TT : Resid.Table :=
  ⟨fun g => if g ∈ D.Tnames then D.Trefs g else D.O.refs g,
   fun g => if g ∈ D.Tnames then D.Tments g else D.O.ments g,
   fun g => if g ∈ D.Tnames then D.Tb g else D.O.body g⟩

theorem TT_body_T {g : Name} (h : g ∈ D.Tnames) : D.TT.body g = D.Tb g := by simp [TT, h]
theorem TT_body_O {g : Name} (h : g ∉ D.Tnames) : D.TT.body g = D.O.body g := by simp [TT, h]
theorem argEnv_TT_O {g : Name} (h : g ∉ D.Tnames) (ps : List PathV) (xs : List SpaceV) :
    Resid.argEnv D.TT g ps xs = Resid.argEnv D.O g ps xs := by
  simp [Resid.argEnv, TT, h]
theorem TT_refs_T {g : Name} (h : g ∈ D.Tnames) : D.TT.refs g = D.Trefs g := by simp [TT, h]
theorem TT_ments_T {g : Name} (h : g ∈ D.Tnames) : D.TT.ments g = D.Tments g := by simp [TT, h]

/-- the combined table is positive -/
theorem TT_pos : Resid.Positive D.TT := by
  intro g
  by_cases h : g ∈ D.Tnames
  · rw [TT_body_T D h]; exact D.Tpos g h
  · rw [TT_body_O D h]; exact D.Opos g

/-- the ORIGINAL approximants and their limit -/
def tO (n : ℕ) : RoutineEnv := Fold.iter (Resid.sys D.O) n
def tOinf : RoutineEnv := Fold.kleene (Resid.sys D.O)

theorem tO_chain : RoutineChain D.tO := fun k =>
  (Resid.le_iff _ _).mp (Fold.iter_mono (Resid.sys_mono D.O D.Opos) (Nat.le_succ k))

theorem tOinf_fix : Resid.sys D.O D.tOinf = D.tOinf :=
  (Fold.kleene_is_lfp (Resid.sys_mono D.O D.Opos) (Resid.sys_cont D.O D.Opos)).1

/-- THE MIXED VALUATION over an original valuation `δO`: original names as `δO`, residual names as
their configuration's meaning under `δO` -/
def mixed (δO : RoutineEnv) : RoutineEnv :=
  fun g ps xs => if g ∈ D.Tnames then (D.conf g).denT δO (Resid.argEnv D.TT g ps xs) else δO g ps xs

theorem mixed_T (δO : RoutineEnv) {g : Name} (h : g ∈ D.Tnames) :
    D.mixed δO g = fun ps xs => (D.conf g).denT δO (Resid.argEnv D.TT g ps xs) := by
  funext ps xs; simp [mixed, h]
theorem mixed_O (δO : RoutineEnv) {g : Name} (h : g ∉ D.Tnames) : D.mixed δO g = δO g := by
  funext ps xs; simp [mixed, h]

theorem notT_of_O {r : Name} (h : r ∈ D.Onames) : r ∉ D.Tnames := Finset.disjoint_left.mp D.disjoint h

/-- the mixed valuation agrees with `δO` on the original names -/
theorem mixed_agreeO (δO : RoutineEnv) : RoutineEnv.AgreeOn D.Onames (D.mixed δO) δO :=
  fun r hr => D.mixed_O δO (D.notT_of_O hr)

/-- CONSISTENCY: a valuation giving every residual name its configuration's meaning under itself -/
def Consistent (μ : RoutineEnv) : Prop :=
  ∀ g ∈ D.Tnames, μ g = fun ps xs => (D.conf g).denT μ (Resid.argEnv D.TT g ps xs)

/-- every mixed valuation is consistent: a configuration calls one original name, at which the mixed
valuation is `δO`, with call-free arguments -/
theorem mixed_consistent (δO : RoutineEnv) : D.Consistent (D.mixed δO) := by
  intro g hg
  obtain ⟨r, refs, ms, hrO, hconf, _, hms, _, _⟩ := D.confCall g hg
  rw [D.mixed_T δO hg]
  funext ps xs
  rw [hconf]
  exact call_denT_congr _ r refs ms (D.mixed_O δO (D.notT_of_O hrO)).symm hms

/-! ### The typed driving steps and their soundness -/

/-- ONE DRIVING STEP, at a position: a certified law, or a fold -/
inductive DStep : Space → Space → Prop
  /-- a certified-law rewrite: `SC.reduceTraced` records `(law, before, after)`, `verifyTrace`
  re-applies the law at the position; the law's semantic validity is its SMT certificate -/
  | law (c : Ctx) {a b : Space} (ok : ∀ δ ρ, a.denT δ ρ = b.denT δ ρ) : DStep (c.plug a) (c.plug b)
  /-- a fold: the instance `conf g · θ` (checked by `SC.State.checkFold`) replaced by the call `g(θ)` -/
  | fold (c : Ctx) (g : Name) (hg : g ∈ D.Tnames) (θm : List (Name × Space)) (θp : List (Name × Path)) :
      DStep (c.plug (substS D.F θm θp (D.conf g)))
            (c.plug (.call g (foldArgsR θp (D.Trefs g)) (foldArgsM θm (D.Tments g))))

/-- a finite trace of steps -/
inductive DTrace : Space → Space → Prop
  | refl (a : Space) : DTrace a a
  | step {a b c : Space} (s : D.DStep a b) (rest : DTrace b c) : DTrace a c

/-- EVERY STEP IS SOUND under a consistent valuation -/
theorem DStep.sound {μ : RoutineEnv} (hμ : D.Consistent μ) {a b : Space} (s : D.DStep a b) :
    ∀ ρ, a.denT μ ρ = b.denT μ ρ := by
  cases s with
  | law c ok => exact Ctx.plug_congr μ (fun ρ => ok μ ρ) c
  | fold c g hg θm θp =>
      apply Ctx.plug_congr μ _ c
      intro ρ
      have hc := hμ g hg
      rw [← D.TT_refs_T hg, ← D.TT_ments_T hg]
      exact fold_step D.F D.TT μ ρ g (D.conf g) θm θp
        (by rw [D.TT_refs_T hg]; exact (D.Tclosed g hg).1)
        (by rw [D.TT_ments_T hg]; exact (D.Tclosed g hg).2) hc

theorem DTrace.sound {μ : RoutineEnv} (hμ : D.Consistent μ) {a b : Space} (t : D.DTrace a b) : Chain μ a b := by
  induction t with
  | refl a => exact Chain.refl a
  | step s _ ih => exact Chain.step (DStep.sound D hμ s) ih

/-! ### The unfold at the fixpoint and at an approximant -/

/-- at the fixpoint: a configuration equals its unfolding under the mixed limit valuation -/
theorem unfold_inf {r : Name} {refs : List Path} {ms : List Space} (hrO : r ∈ D.Onames)
    (hms : Space.hasCalls ms = false) (hlR : (D.O.refs r).length = refs.length)
    (hlM : (D.O.ments r).length = ms.length) (ρ : Env) :
    (Space.call r refs ms).denT (D.mixed D.tOinf) ρ = (unfoldOnce D.F D.O r refs ms).denT (D.mixed D.tOinf) ρ := by
  apply unfold_step D.F D.O (D.mixed D.tOinf) (D.mixed D.tOinf) ρ r refs ms (D.Oclosed r).1 (D.Oclosed r).2 hlR hlM
  · -- the mixed limit is a fixpoint of the original system at `r`
    rw [D.mixed_O D.tOinf (D.notT_of_O hrO)]
    funext ps xs
    have hK : D.tOinf r ps xs = (D.O.body r).denT D.tOinf (Resid.argEnv D.O r ps xs) := by
      have := congrFun (congrFun (congrFun D.tOinf_fix r) ps) xs
      exact this.symm
    rw [hK]
    exact Space.denT_congr_delta_calls (D.O.body r) _ _ _
      (fun q hq => (D.mixed_agreeO D.tOinf q (D.Ocalls r hq)).symm)
  · rfl

/-- at an approximant: the depth-`(n+1)` configuration equals its unfolding under the mixed depth-`n` valuation -/
theorem unfold_succ (n : ℕ) {r : Name} {refs : List Path} {ms : List Space}
    (hms : Space.hasCalls ms = false) (hlR : (D.O.refs r).length = refs.length)
    (hlM : (D.O.ments r).length = ms.length) (ρ : Env) :
    (Space.call r refs ms).denT (D.tO (n + 1)) ρ = (unfoldOnce D.F D.O r refs ms).denT (D.mixed (D.tO n)) ρ := by
  apply unfold_step D.F D.O (D.mixed (D.tO n)) (D.tO (n + 1)) ρ r refs ms (D.Oclosed r).1 (D.Oclosed r).2 hlR hlM
  · funext ps xs
    show Resid.sys D.O (D.tO n) r ps xs = _
    simp only [Resid.sys]
    exact Space.denT_congr_delta_calls (D.O.body r) _ _ _
      (fun q hq => (D.mixed_agreeO (D.tO n) q (D.Ocalls r hq)).symm)
  · exact Space.denTs_congr_delta_of_noCall _ _ ρ ms hms

/-! ### THE PREMISES, DERIVED -/

/-- the traces a run recorded: one per residual node, from the one unfold of its configuration -/
def Traced : Prop :=
  ∀ g ∈ D.Tnames, ∀ r refs ms, D.conf g = .call r refs ms → D.DTrace (unfoldOnce D.F D.O r refs ms) (D.Tb g)

theorem premises (ht : D.Traced) :
    Fold.FoldPremises (Resid.sys D.TT) (D.mixed D.tOinf) (fun n => D.mixed (D.tO n)) where
  fix := by
    funext g ps xs
    by_cases hg : g ∈ D.Tnames
    · obtain ⟨r, refs, ms, hrO, hconf, _, hms, hlR, hlM⟩ := D.confCall g hg
      have hchain := (DTrace.sound D (D.mixed_consistent D.tOinf) (ht g hg r refs ms hconf)).denT_eq
      simp only [Resid.sys, D.TT_body_T hg]
      rw [← hchain, ← D.unfold_inf hrO hms hlR hlM, ← hconf, D.mixed_T D.tOinf hg]
      show (D.conf g).denT (D.mixed D.tOinf) _ = (D.conf g).denT D.tOinf _
      rw [hconf]
      exact call_denT_congr _ r refs ms (D.mixed_O D.tOinf (D.notT_of_O hrO)) hms
    · simp only [Resid.sys, D.TT_body_O hg, D.argEnv_TT_O hg, D.mixed_O D.tOinf hg]
      have hK : D.tOinf g ps xs = (D.O.body g).denT D.tOinf (Resid.argEnv D.O g ps xs) :=
        (congrFun (congrFun (congrFun D.tOinf_fix g) ps) xs).symm
      rw [hK]
      exact Space.denT_congr_delta_calls (D.O.body g) _ _ _
        (fun q hq => D.mixed_agreeO D.tOinf q (D.Ocalls g hq))
  productive := by
    intro n
    refine (Resid.le_iff _ _).mpr fun g ps xs => ?_
    by_cases hg : g ∈ D.Tnames
    · obtain ⟨r, refs, ms, hrO, hconf, _, hms, hlR, hlM⟩ := D.confCall g hg
      have hchain := (DTrace.sound D (D.mixed_consistent (D.tO n)) (ht g hg r refs ms hconf)).denT_eq
      simp only [Resid.sys, D.TT_body_T hg, D.mixed_T (D.tO (n + 1)) hg]
      rw [← hchain, hconf, D.unfold_succ n hms hlR hlM]
    · simp only [Resid.sys, D.TT_body_O hg, D.argEnv_TT_O hg, D.mixed_O (D.tO (n + 1)) hg]
      show Resid.sys D.O (D.tO n) g ps xs ⊆ _
      simp only [Resid.sys]
      rw [Space.denT_congr_delta_calls (D.O.body g) (D.tO n) (D.mixed (D.tO n)) _
        (fun q hq => (D.mixed_agreeO (D.tO n) q (D.Ocalls g hq)).symm)]
  zero := by
    funext g ps xs
    by_cases hg : g ∈ D.Tnames
    · obtain ⟨r, refs, ms, _, hconf, _, _, _, _⟩ := D.confCall g hg
      simp [mixed, hg, hconf, Space.denT, tO, Fold.iter]
    · simp [mixed, hg, tO, Fold.iter]
  mono := by
    intro i j hij
    refine (Resid.le_iff _ _).mpr fun g ps xs => ?_
    have hle : RoutineEnv.le (D.tO i) (D.tO j) :=
      (Resid.le_iff _ _).mp (Fold.iter_mono (Resid.sys_mono D.O D.Opos) hij)
    by_cases hg : g ∈ D.Tnames
    · obtain ⟨r, refs, ms, _, hconf, hrefs, hms, _, _⟩ := D.confCall g hg
      simp only [mixed, hg, if_true]
      exact Space.denT_mono_delta hle (D.conf g) _ (by rw [hconf]; simp [Space.callPosB, hrefs, hms])
    · simp only [mixed, hg, if_false]
      exact hle g ps xs
  sup := by
    rw [Resid.iSup_eq]
    funext g ps xs
    simp only [RoutineEnv.iSup]
    by_cases hg : g ∈ D.Tnames
    · obtain ⟨r, refs, ms, _, hconf, hrefs, hms, _, _⟩ := D.confCall g hg
      simp only [mixed, hg, if_true]
      have hcont := Space.denT_cont_delta D.tO_chain (D.conf g) (Resid.argEnv D.TT g ps xs)
        (by rw [hconf]; simp [Space.callPosB, hrefs, hms])
      have hlim : D.tOinf = RoutineEnv.iSup D.tO := by
        simp only [tOinf, Fold.kleene]; exact Resid.iSup_eq _
      rw [hlim, hcont]
    · simp only [mixed, hg, if_false]
      have hlim : D.tOinf = RoutineEnv.iSup D.tO := by
        simp only [tOinf, Fold.kleene]; exact Resid.iSup_eq _
      rw [hlim]
      rfl

/-- **THE FOLD THEOREM, INSTANTIATED.**  For a run whose recorded traces are `Traced`, the residual
system's least fixpoint is the mixed original meaning: every residual routine computes exactly its
configuration's original meaning, and every original routine keeps its own. -/
theorem drive_correct (ht : D.Traced) : Fold.kleene (Resid.sys D.TT) = D.mixed D.tOinf :=
  Fold.resid_lfp_eq_orig D.TT D.TT_pos (D.premises ht)

/-- per residual node -/
theorem drive_node (ht : D.Traced) {g : Name} (hg : g ∈ D.Tnames) (ps : List PathV) (xs : List SpaceV) :
    Fold.kleene (Resid.sys D.TT) g ps xs = (D.conf g).denT D.tOinf (Resid.argEnv D.TT g ps xs) := by
  rw [D.drive_correct ht]; simp [mixed, hg]

end DriveSystem

end Zippy
