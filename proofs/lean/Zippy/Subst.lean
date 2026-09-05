/-
==================================================================================================
SUBSTITUTION, MECHANIZED.

This is the Lean mirror of `src/main/scala/Subst.scala`: simultaneous in both sorts,
capture-avoiding, total over every constructor. `O6a` — beta-soundness of capture-avoiding
inlining — was OPEN as a first-order theorem because it needs a model of the substitution FUNCTION.
Here the function is a DEFINITION and the hygiene statements are theorems about it, checked by
Lean's kernel; its SEMANTIC half — substitution denotes environment extension — is `SubstSem.lean`
(`substS_denT`), which closes O6a.

==THE ONE PLACE THIS DEFINITION DIFFERS FROM THE SCALA, AND WHY==
At a binder that would capture, `Subst.scala` does TWO passes over the body: first a rename
(`recs(body, Map(rest -> Mention(nr)), …)`), then the substitution (`recs(body1, sm2, pm2)`).  This
definition does ONE pass, with the rename MERGED INTO the substitution map.

They agree.  The rename sends `rest ↦ nr` with `nr` fresh; the substitution `sm2` has `rest` removed
from its domain, so the merged map is well defined, and a replacement's free `rest` is not rewritten
by either form (substitution never descends into a replacement).  The merged form is what makes this
definition STRUCTURALLY RECURSIVE — the two-pass form recurses twice on a body of the same size, so
Lean would need a well-founded measure and every proof below would carry the unfolding lemma around.

That agreement is an OBLIGATION, not an assumption, and `1E.2` is where it is discharged: the
correspondence check re-runs each `(term, substitution, result)` triple the Scala actually performed
and asks Lean to confirm the result.  A disagreement between the two forms would show up there as a
failing triple, on real terms, rather than as an argument in a comment.

==FRESH NAMES ARE A PARAMETER==
`Subst.scala` mints `~m0`, `~m1`, … from a counter.  A Lean definition cannot use a mutable counter,
and more importantly the THEOREMS do not depend on which fresh name is chosen — only on its being
fresh.  So the supply is a parameter carrying its own correctness ([[FreshSupply]]), the theorems are
proved for every supply, and `1E.2`'s trace check is what confirms the Scala's particular choice
satisfies the contract.
==================================================================================================
-/
import Zippy.Syntax

namespace Zippy

/-- A source of names not already in a given finite set, carrying its own specification.
Parameterising the theorems over this is what makes them independent of the naming POLICY: the
Scala's `~m0`/`~m1` counter and the length-based generator below are both instances. -/
structure FreshSupply where
  gen : Finset Name → Name
  spec : ∀ S : Finset Name, gen S ∉ S

/-- A generator that is fresh BY LENGTH: longer than every name in the set, hence in none of them.
Not the Scala's policy (a counter), and deliberately so — see this file's header. -/
def FreshSupply.byLength : FreshSupply where
  gen := fun S => "~" ++ String.ofList (List.replicate (1 + S.sup String.length) 'm')
  spec := by
    intro S hmem
    -- The generated name is STRICTLY LONGER than every name in the set (its length is
    -- `1 + sup`, and every member's length is `≤ sup`), so it is a member of none of them.  A
    -- membership would give `1 + sup ≤ sup`.
    have hle : ("~" ++ String.ofList (List.replicate (1 + S.sup String.length) 'm')).length
                ≤ S.sup String.length := Finset.le_sup hmem
    simp only [String.length_append, String.length_ofList, List.length_replicate] at hle
    omega

/-! ### Substitutions

A substitution is an association list per sort.  A list rather than a `Finsupp` or a function:
membership, domain and range must all be COMPUTABLE for `subst` to be a definition, and a trace
(`1E.2`) carries exactly this shape. -/

/-! Lookup, domain and drop are written as EXPLICIT CONS RECURSIONS rather than as `find?` and
`filter`.  They compute the same thing; the difference is that every lemma below needs the `e :: σ`
equation, and `Option.map (·.2) (find? …)` gives one only after unfolding two library definitions
and a `decide`.  (Measured: the first version of `lookupM_dropM_ne` left an `∃ a,` goal that `simp`
could not close and an `ih` whose type printed identically to its expected type.) -/

/-- lookup, first match wins (as `Map` does in the Scala) -/
def lookupM : List (Name × Space) → Name → Option Space
  | [], _ => none
  | e :: σ, m => if e.1 = m then some e.2 else lookupM σ m

def lookupR : List (Name × Path) → Name → Option Path
  | [], _ => none
  | e :: σ, r => if e.1 = r then some e.2 else lookupR σ r

/-- the domain of a mention substitution -/
def domM : List (Name × Space) → Finset Name
  | [] => ∅
  | e :: σ => insert e.1 (domM σ)
def domR : List (Name × Path) → Finset Name
  | [] => ∅
  | e :: σ => insert e.1 (domR σ)

/-- drop a name from a substitution's domain — a binder SHADOWS a substitution for its own name -/
def dropM : List (Name × Space) → Name → List (Name × Space)
  | [], _ => []
  | e :: σ, m => if e.1 = m then dropM σ m else e :: dropM σ m
def dropR : List (Name × Path) → Name → List (Name × Path)
  | [], _ => []
  | e :: σ, r => if e.1 = r then dropR σ r else e :: dropR σ r

/-! The RANGE of a substitution: the free names of everything it can put into the term.  These are
what a binder must not capture, and `foldr` rather than `foldl` because every proof below needs the
cons equation `range (e :: σ) = free e.2 ∪ range σ`, which `foldr` gives by `rfl`. -/

/-- free mentions contributed by a mention substitution -/
def rangeMM : List (Name × Space) → Finset Name
  | [] => ∅
  | e :: σ => e.2.freeM ∪ rangeMM σ
/-- free mentions contributed by a path substitution (reachable through `groundedSP`) -/
def rangeMP : List (Name × Path) → Finset Name
  | [] => ∅
  | e :: σ => e.2.freeM ∪ rangeMP σ
/-- free refs contributed by a mention substitution -/
def rangeRM : List (Name × Space) → Finset Name
  | [] => ∅
  | e :: σ => e.2.freeR ∪ rangeRM σ
/-- free refs contributed by a path substitution -/
def rangeRP : List (Name × Path) → Finset Name
  | [] => ∅
  | e :: σ => e.2.freeR ∪ rangeRP σ

/-- the free MENTIONS of everything either substitution can put into the term.  `Subst.scala`'s
`rangeMentions`; it is what a binder must not capture. -/
def rangeM (σm : List (Name × Space)) (σp : List (Name × Path)) : Finset Name :=
  rangeMM σm ∪ rangeMP σp

/-- the free REFS of everything either substitution can put into the term.  `rangeRefs`. -/
def rangeR (σm : List (Name × Space)) (σp : List (Name × Path)) : Finset Name :=
  rangeRM σm ∪ rangeRP σp

/-! ### Binding a binder

`Subst.scala` computes, at each binder, whether a replacement's free name would be caught
(`capM`/`capP`), a fresh name if so, and the substitution the body is descended with.  Both of those
are the SAME decision at all three binding forms and for both sorts, so they are one function each
here — which is also what makes the capture-avoidance proof one lemma instead of five.

`avoid` is the extra set the fresh name must dodge beyond the range: the body's own free names, so a
rename cannot collide with something the body already refers to. -/

/-- a MENTION binder `b`: the name the result binds, and the substitution its scope is descended
with.  The pair is exactly `(nr, σm₂)` in `Subst.scala`'s binder arms. -/
def bindM (F : FreshSupply) (σm : List (Name × Space)) (σp : List (Name × Path))
    (b : Name) (avoid : Finset Name) : Name × List (Name × Space) :=
  if b ∈ rangeM (dropM σm b) σp then
    let nb := F.gen (rangeM (dropM σm b) σp ∪ avoid)
    (nb, (b, Space.mention nb) :: dropM σm b)
  else (b, dropM σm b)

/-- a REF binder `b`: the same, on the path side. -/
def bindR (F : FreshSupply) (σm : List (Name × Space)) (σp : List (Name × Path))
    (b : Name) (avoid : Finset Name) : Name × List (Name × Path) :=
  if b ∈ rangeR σm (dropR σp b) then
    let nb := F.gen (rangeR σm (dropR σp b) ∪ avoid)
    (nb, (b, Path.deref nb) :: dropR σp b)
  else (b, dropR σp b)

/-! ### The substitution itself -/

variable (F : FreshSupply)

mutual

/-- substitute inside a path.  `groundedSP` carries a SPACE, so it goes through the space walker —
the omission of exactly this case is one of the two defects `EquivPipeline.substPathRef` had. -/
def substP (σm : List (Name × Space)) (σp : List (Name × Path)) : Path → Path
  | .deref r => (lookupR σp r).getD (.deref r)
  | .const items => .const items
  | .concat l r => .concat (substP σm σp l) (substP σm σp r)
  | .groundedPP p f => .groundedPP (substP σm σp p) f
  | .groundedSP s f => .groundedSP (substS σm σp s) f

def substList : List (Name × Space) → List (Name × Path) → List Space → List Space
  | _, _, [] => []
  | σm, σp, s :: rest => substS σm σp s :: substList σm σp rest

def substPList : List (Name × Space) → List (Name × Path) → List Path → List Path
  | _, _, [] => []
  | σm, σp, p :: rest => substP σm σp p :: substPList σm σp rest

/-- substitute inside a space.  Simultaneous, capture-avoiding, total. -/
def substS (σm : List (Name × Space)) (σp : List (Name × Path)) : Space → Space
  | .mention m => (lookupM σm m).getD (.mention m)
  | .empty => .empty
  | .lit ps => .lit ps
  | .singleton p => .singleton (substP σm σp p)
  | .union x y => .union (substS σm σp x) (substS σm σp y)
  | .inter x y => .inter (substS σm σp x) (substS σm σp y)
  | .sub x y => .sub (substS σm σp x) (substS σm σp y)
  | .restriction x y => .restriction (substS σm σp x) (substS σm σp y)
  | .raffination x y => .raffination (substS σm σp x) (substS σm σp y)
  | .composition x y => .composition (substS σm σp x) (substS σm σp y)
  | .wrap s p => .wrap (substS σm σp s) (substP σm σp p)
  | .unwrap s p => .unwrap (substS σm σp s) (substP σm σp p)
  | .tailsUnion s => .tailsUnion (substS σm σp s)
  | .tailsInter s => .tailsInter (substS σm σp s)
  | .range x lo hi => .range (substS σm σp x) lo hi
  -- `r` is a GLOBAL routine name and is preserved; its ARGUMENTS are ordinary subterms of the
  -- enclosing scope and are descended.  Leaving them alone is what `EquivPipeline.substMention`'s
  -- `case other => other` used to do.
  | .call r refs ms => .call r (substPList σm σp refs) (substList σm σp ms)
  -- THE THREE BINDING FORMS.  `symbol`/`acc` bind on the REF side, `rest`/`rec_` on the MENTION
  -- side, and each is dropped from its own substitution (shadowing) and alpha-renamed when a
  -- replacement's free name would be caught (capture avoidance).  The rename is MERGED into the
  -- map rather than applied as a separate pass; see this file's header.
  -- Each binder is bound by `bindM`/`bindR`, in the order the binders nest: the REF binders are
  -- resolved first so a MENTION binder's fresh name avoids their replacements, and `Fold`'s second
  -- ref binder is resolved against the substitution the first produced, so the two fresh names
  -- cannot collide with each other.
  | .iteration src sym rest t =>
      let (ns, σp₂) := bindR F σm σp sym t.freeR
      let (nr, σm₂) := bindM F σm σp₂ rest t.freeM
      .iteration (substS σm σp src) ns nr (substS σm₂ σp₂ t)
  | .fixpoint i r b =>
      let (nr, σm₂) := bindM F σm σp r b.freeM
      .fixpoint (substS σm σp i) nr (substS σm₂ σp b)
  | .fold src ini acc sym rest t upd =>
      let bodyR := t.freeR ∪ upd.freeR
      let bodyM := t.freeM ∪ upd.freeM
      let (na, σpA) := bindR F σm σp acc bodyR
      let (ns, σp₂) := bindR F σm σpA sym (insert na bodyR)
      let (nr, σm₂) := bindM F σm σp₂ rest bodyM
      .fold (substS σm σp src) (substP σm σp ini) na ns nr
            (substS σm₂ σp₂ t) (substP σm₂ σp₂ upd)
  | .groundedPS p f => .groundedPS (substP σm σp p) f
  | .groundedSS s f => .groundedSS (substS σm σp s) f

end


/-! ==================================================================================================
### THEOREM 1 — the empty substitution is the identity

`Subst.apply` short-circuits on `if mentions.isEmpty && paths.isEmpty then s`.  That is an
optimisation whose correctness is assumed at every call site; here it is a theorem.  Its proof is
also the smallest place the binder machinery has to be shown INERT when nothing is being
substituted: with both maps empty the range is empty, so neither `capM` nor `capR` fires and no
binder is renamed — which is what makes `alphaNorm`-style callers able to rely on the fast path
returning the term unchanged rather than an alpha-variant of it.
================================================================================================== -/

@[simp] theorem lookupM_nil (m : Name) : lookupM [] m = none := rfl
@[simp] theorem lookupR_nil (r : Name) : lookupR [] r = none := rfl
@[simp] theorem dropM_nil (m : Name) : dropM [] m = [] := rfl
@[simp] theorem dropR_nil (r : Name) : dropR [] r = [] := rfl
@[simp] theorem rangeM_nil : rangeM [] [] = ∅ := by simp [rangeM, rangeMM, rangeMP]
@[simp] theorem rangeR_nil : rangeR [] [] = ∅ := by simp [rangeR, rangeRM, rangeRP]

/-- with nothing to substitute, a binder is bound to ITSELF and the empty substitution: no rename,
because the range is empty and nothing can be captured.  This is what lets the `Subst.apply` fast
path return the term rather than an alpha-variant of it. -/
@[simp] theorem bindM_nil (F : FreshSupply) (b : Name) (avoid : Finset Name) :
    bindM F [] [] b avoid = (b, []) := by
  simp [bindM, dropM, rangeM, rangeMM, rangeMP]

@[simp] theorem bindR_nil (F : FreshSupply) (b : Name) (avoid : Finset Name) :
    bindR F [] [] b avoid = (b, []) := by
  simp [bindR, dropR, rangeR, rangeRM, rangeRP]

mutual
theorem substP_nil (F : FreshSupply) : ∀ p : Path, substP F [] [] p = p
  | .deref _ => by simp [substP]
  | .const _ => by simp [substP]
  | .concat l r => by simp [substP, substP_nil F l, substP_nil F r]
  | .groundedPP p _ => by simp [substP, substP_nil F p]
  | .groundedSP s _ => by simp [substP, substS_nil F s]

theorem substList_nil (F : FreshSupply) : ∀ l : List Space, substList F [] [] l = l
  | [] => by simp [substList]
  | s :: rest => by simp [substList, substS_nil F s, substList_nil F rest]

theorem substPList_nil (F : FreshSupply) : ∀ l : List Path, substPList F [] [] l = l
  | [] => by simp [substPList]
  | p :: rest => by simp [substPList, substP_nil F p, substPList_nil F rest]

theorem substS_nil (F : FreshSupply) : ∀ s : Space, substS F [] [] s = s
  | .empty => by simp [substS]
  | .lit _ => by simp [substS]
  | .mention _ => by simp [substS]
  | .singleton p => by simp [substS, substP_nil F p]
  | .union x y => by simp [substS, substS_nil F x, substS_nil F y]
  | .inter x y => by simp [substS, substS_nil F x, substS_nil F y]
  | .sub x y => by simp [substS, substS_nil F x, substS_nil F y]
  | .restriction x y => by simp [substS, substS_nil F x, substS_nil F y]
  | .raffination x y => by simp [substS, substS_nil F x, substS_nil F y]
  | .composition x y => by simp [substS, substS_nil F x, substS_nil F y]
  | .wrap s p => by simp [substS, substS_nil F s, substP_nil F p]
  | .unwrap s p => by simp [substS, substS_nil F s, substP_nil F p]
  | .tailsUnion s => by simp [substS, substS_nil F s]
  | .tailsInter s => by simp [substS, substS_nil F s]
  | .range x _ _ => by simp [substS, substS_nil F x]
  | .call _ refs ms => by simp [substS, substPList_nil F refs, substList_nil F ms]
  | .iteration src sym rest t => by
      simp [substS, substS_nil F src, substS_nil F t]
  | .fixpoint i r b => by
      simp [substS, substS_nil F i, substS_nil F b]
  | .fold src ini acc sym rest t upd => by
      simp [substS, substS_nil F src, substP_nil F ini, substS_nil F t, substP_nil F upd]
  | .groundedPS p _ => by simp [substS, substP_nil F p]
  | .groundedSS s _ => by simp [substS, substS_nil F s]
end


/-! ==================================================================================================
### THEOREM 2 — `g(y,x)`: SEQUENTIAL SUBSTITUTION IS NOT SIMULTANEOUS SUBSTITUTION

`EquivPipeline`'s `Lower.inline` bound a routine's arguments in a loop:

    for (mn, arg) <- mentionns zip args do b = substMention(b, mn, arg)

which is sequential composition.  It differs from simultaneous substitution exactly when an ARGUMENT
mentions another FORMAL, and then it is WRONG.  This is that fact, on the smallest term that carries
it: a routine `g(a, b)` whose body uses both formals, called as `g(b, a)`.

The two arguments COLLAPSE INTO ONE VARIABLE under the sequential reading.  That is not a weaker
answer, it is a different program.
================================================================================================== -/

/-- `g(a, b) = a ∪ wrap(b, "k")` — the body of the routine, using both formals. -/
def gBody : Space := .union (.mention "a") (.wrap (.mention "b") (.const ["k"]))

/-- the SIMULTANEOUS reading of `g(b, a)`: the two arguments are swapped, as they should be -/
theorem simul_gyx (F : FreshSupply) :
    substS F [("a", .mention "b"), ("b", .mention "a")] [] gBody
      = .union (.mention "b") (.wrap (.mention "a") (.const ["k"])) := by
  simp [gBody, substS, substP, lookupM]

/-- the SEQUENTIAL reading: `a := b` rewrites every `a` to `b`, and the following `b := a` rewrites
BOTH to `a`.  The two arguments have become one. -/
theorem seq_gyx (F : FreshSupply) :
    substS F [("b", .mention "a")] [] (substS F [("a", .mention "b")] [] gBody)
      = .union (.mention "a") (.wrap (.mention "a") (.const ["k"])) := by
  simp [gBody, substS, substP, lookupM]

/-- THE FACT.  They are not the same term. -/
theorem seq_ne_simul_gyx (F : FreshSupply) :
    substS F [("a", .mention "b"), ("b", .mention "a")] [] gBody
      ≠ substS F [("b", .mention "a")] [] (substS F [("a", .mention "b")] [] gBody) := by
  rw [simul_gyx, seq_gyx]
  intro h
  -- the two differ in their left argument: `mention "b"` against `mention "a"`
  simp at h

/-! ==================================================================================================
### THEOREM 3 — CAPTURE AVOIDANCE

The theorem `SubstConformance` structurally cannot see, because it substitutes closed `Literal`s
only (the capture case required by ).  Capture needs a replacement with a FREE name that an inner binder
can swallow, and a closed replacement has none.

THE STATEMENT.  If a name `m` occurs free in `s` and the substitution replaces it by `t`, then every
free name of `t` is STILL FREE in the result.  That is exactly "no binder captured it": a captured
occurrence would have become bound, i.e. would have dropped out of `freeM`.

THE PROOF IS THE SAME AT ALL THREE BINDERS, AND IT SPLITS THE SAME WAY.  At a binder whose name is
`b`, the result's `freeM` is the body's with `b'` erased, where `b'` is `b` itself or the fresh name.
Both branches give `b' ∉ t.freeM`, for different reasons, and that is the whole content:

  * NO-CAPTURE BRANCH (`capM` false).  `capM` is precisely `b ∈ rangeM σm' σp'`, so its falsity says
    `b` is free in NO replacement — and `t` is one of them.  The binder does not need renaming
    because it provably cannot capture.
  * CAPTURE BRANCH (`capM` true).  `b' = F.gen (rangeM σm' σp' ∪ …)` and `FreshSupply.spec` gives
    `b' ∉ rangeM σm' σp'`, which again contains `t.freeM`.

So the fresh-name supply's contract is used at exactly one point, and the non-capture case needs no
supply at all.  Note which hypothesis is NOT needed: nothing about the ORDER of names, nothing about
the counter, nothing about `~`.  `1E.2`'s trace check is what ties the Scala's particular policy to
this contract.
================================================================================================== -/

/-- a replacement's free mentions are among the substitution's range.  The bridge between "what
`lookupM` found" and "what the binder had to avoid". -/
theorem freeM_subset_rangeMM :
    ∀ (σ : List (Name × Space)) (m : Name) (t : Space),
      lookupM σ m = some t → t.freeM ⊆ rangeMM σ
  | [], _, _, h => by simp [lookupM] at h
  | e :: σ, m, t, h => by
      simp only [lookupM] at h
      split at h
      · cases h; simp [rangeMM]
      · exact (freeM_subset_rangeMM σ m t h).trans (by simp [rangeMM])

/-- the same, folded into the two-sort range -/
theorem freeM_subset_rangeM (σm : List (Name × Space)) (σp : List (Name × Path))
    (m : Name) (t : Space) (h : lookupM σm m = some t) : t.freeM ⊆ rangeM σm σp :=
  (freeM_subset_rangeMM σm m t h).trans (by simp [rangeM])

/-- dropping a DIFFERENT name does not change a lookup -/
theorem lookupM_dropM_ne :
    ∀ (σ : List (Name × Space)) (m b : Name), m ≠ b →
      lookupM (dropM σ b) m = lookupM σ m
  | [], _, _, _ => rfl
  | e :: σ, m, b, hne => by
      simp only [dropM]
      split
      · -- e.1 = b, so e.1 ≠ m; the head is dropped and the head test would have failed anyway
        rename_i heb
        have : ¬ (e.1 = m) := by rw [heb]; exact fun h => hne h.symm
        simp only [lookupM, this, if_false]
        exact lookupM_dropM_ne σ m b hne
      · simp only [lookupM]
        split
        · rfl
        · exact lookupM_dropM_ne σ m b hne

/-- consing a DIFFERENT name in front does not change a lookup -/
theorem lookupM_cons_ne (σ : List (Name × Space)) (m b : Name) (v : Space) (hne : m ≠ b) :
    lookupM ((b, v) :: σ) m = lookupM σ m := by
  have : ¬ (b = m) := fun h => hne h.symm
  simp only [lookupM, this, if_false]

/-! ### The two facts a MENTION binder gives, which are the whole of capture avoidance -/

/-- THE BINDER CANNOT CAPTURE.  The name `bindM` binds is free in NO replacement the body is
descended with — in both branches, for different reasons:

  * the `if` was FALSE, and its condition is precisely "`b` is free in some replacement";
  * the `if` was TRUE, and `FreshSupply.spec` puts the generated name outside the range.

`FreshSupply`'s contract is used at exactly one point, and the non-capture branch needs no supply at
all.  Nothing about the naming POLICY enters: not the order, not a counter, not the `~` prefix. -/
theorem bindM_not_in_range (F : FreshSupply) (σm : List (Name × Space))
    (σp : List (Name × Path)) (b : Name) (avoid : Finset Name) :
    (bindM F σm σp b avoid).1 ∉ rangeM (dropM σm b) σp := by
  unfold bindM
  split
  · have := F.spec (rangeM (dropM σm b) σp ∪ avoid)
    simpa using fun h => this (Finset.mem_union_left _ h)
  · rename_i hnot
    simpa using hnot

/-- and it does not disturb any OTHER name's replacement: the substitution the scope is descended
with still maps `m` to the same `t`, for every `m` the binder does not shadow. -/
theorem bindM_lookup_ne (F : FreshSupply) (σm : List (Name × Space))
    (σp : List (Name × Path)) (b : Name) (avoid : Finset Name) (m : Name) (t : Space)
    (hne : m ≠ b) (h : lookupM σm m = some t) :
    lookupM (bindM F σm σp b avoid).2 m = some t := by
  have hd : lookupM (dropM σm b) m = some t := by
    rw [lookupM_dropM_ne σm m b hne]; exact h
  unfold bindM
  split
  · simpa [lookupM_cons_ne _ m b _ hne] using hd
  · simpa using hd


/-! ### The theorem

`m` occurs free in `s`, and the substitution replaces it by `t`.  Then every free name of `t` is
STILL FREE in the result — which is exactly "no binder captured it", since a captured occurrence
would have become bound and dropped out of `freeM`. -/

mutual

theorem substP_keeps_freeM (F : FreshSupply) :
    ∀ (p : Path) (σm : List (Name × Space)) (σp : List (Name × Path)) (m : Name) (t : Space),
      m ∈ p.freeM → lookupM σm m = some t → t.freeM ⊆ (substP F σm σp p).freeM
  | .deref _, _, _, _, _, hm, _ => by simp [Path.freeM] at hm
  | .const _, _, _, _, _, hm, _ => by simp [Path.freeM] at hm
  | .concat l r, σm, σp, m, t, hm, hl => by
      simp only [Path.freeM, Finset.mem_union] at hm
      simp only [substP, Path.freeM]
      rcases hm with h | h
      · exact (substP_keeps_freeM F l σm σp m t h hl).trans Finset.subset_union_left
      · exact (substP_keeps_freeM F r σm σp m t h hl).trans Finset.subset_union_right
  | .groundedPP q _, σm, σp, m, t, hm, hl => by
      simp only [Path.freeM] at hm; simp only [substP, Path.freeM]
      exact substP_keeps_freeM F q σm σp m t hm hl
  | .groundedSP q _, σm, σp, m, t, hm, hl => by
      simp only [Path.freeM] at hm; simp only [substP, Path.freeM]
      exact substS_keeps_freeM F q σm σp m t hm hl

theorem substPs_keeps_freeM (F : FreshSupply) :
    ∀ (l : List Path) (σm : List (Name × Space)) (σp : List (Name × Path)) (m : Name) (t : Space),
      m ∈ Path.freeMs l → lookupM σm m = some t →
      t.freeM ⊆ Path.freeMs (substPList F σm σp l)
  | [], _, _, _, _, hm, _ => by simp [Path.freeMs] at hm
  | q :: rest, σm, σp, m, t, hm, hl => by
      simp only [Path.freeMs, Finset.mem_union] at hm
      simp only [substPList, Path.freeMs]
      rcases hm with h | h
      · exact (substP_keeps_freeM F q σm σp m t h hl).trans Finset.subset_union_left
      · exact (substPs_keeps_freeM F rest σm σp m t h hl).trans Finset.subset_union_right

theorem substSs_keeps_freeM (F : FreshSupply) :
    ∀ (l : List Space) (σm : List (Name × Space)) (σp : List (Name × Path)) (m : Name) (t : Space),
      m ∈ Space.freeMs l → lookupM σm m = some t →
      t.freeM ⊆ Space.freeMs (substList F σm σp l)
  | [], _, _, _, _, hm, _ => by simp [Space.freeMs] at hm
  | q :: rest, σm, σp, m, t, hm, hl => by
      simp only [Space.freeMs, Finset.mem_union] at hm
      simp only [substList, Space.freeMs]
      rcases hm with h | h
      · exact (substS_keeps_freeM F q σm σp m t h hl).trans Finset.subset_union_left
      · exact (substSs_keeps_freeM F rest σm σp m t h hl).trans Finset.subset_union_right

theorem substS_keeps_freeM (F : FreshSupply) :
    ∀ (s : Space) (σm : List (Name × Space)) (σp : List (Name × Path)) (m : Name) (t : Space),
      m ∈ s.freeM → lookupM σm m = some t → t.freeM ⊆ (substS F σm σp s).freeM
  | .empty, _, _, _, _, hm, _ => by simp [Space.freeM] at hm
  | .lit _, _, _, _, _, hm, _ => by simp [Space.freeM] at hm
  | .mention m', σm, σp, m, t, hm, hl => by
      simp only [Space.freeM, Finset.mem_singleton] at hm
      subst hm
      simp [substS, hl]
  | .singleton q, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM] at hm; simp only [substS, Space.freeM]
      exact substP_keeps_freeM F q σm σp m t hm hl
  | .union x y, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM, Finset.mem_union] at hm
      simp only [substS, Space.freeM]
      rcases hm with h | h
      · exact (substS_keeps_freeM F x σm σp m t h hl).trans Finset.subset_union_left
      · exact (substS_keeps_freeM F y σm σp m t h hl).trans Finset.subset_union_right
  | .inter x y, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM, Finset.mem_union] at hm
      simp only [substS, Space.freeM]
      rcases hm with h | h
      · exact (substS_keeps_freeM F x σm σp m t h hl).trans Finset.subset_union_left
      · exact (substS_keeps_freeM F y σm σp m t h hl).trans Finset.subset_union_right
  | .sub x y, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM, Finset.mem_union] at hm
      simp only [substS, Space.freeM]
      rcases hm with h | h
      · exact (substS_keeps_freeM F x σm σp m t h hl).trans Finset.subset_union_left
      · exact (substS_keeps_freeM F y σm σp m t h hl).trans Finset.subset_union_right
  | .restriction x y, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM, Finset.mem_union] at hm
      simp only [substS, Space.freeM]
      rcases hm with h | h
      · exact (substS_keeps_freeM F x σm σp m t h hl).trans Finset.subset_union_left
      · exact (substS_keeps_freeM F y σm σp m t h hl).trans Finset.subset_union_right
  | .raffination x y, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM, Finset.mem_union] at hm
      simp only [substS, Space.freeM]
      rcases hm with h | h
      · exact (substS_keeps_freeM F x σm σp m t h hl).trans Finset.subset_union_left
      · exact (substS_keeps_freeM F y σm σp m t h hl).trans Finset.subset_union_right
  | .composition x y, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM, Finset.mem_union] at hm
      simp only [substS, Space.freeM]
      rcases hm with h | h
      · exact (substS_keeps_freeM F x σm σp m t h hl).trans Finset.subset_union_left
      · exact (substS_keeps_freeM F y σm σp m t h hl).trans Finset.subset_union_right
  | .wrap q pp, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM, Finset.mem_union] at hm
      simp only [substS, Space.freeM]
      rcases hm with h | h
      · exact (substS_keeps_freeM F q σm σp m t h hl).trans Finset.subset_union_left
      · exact (substP_keeps_freeM F pp σm σp m t h hl).trans Finset.subset_union_right
  | .unwrap q pp, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM, Finset.mem_union] at hm
      simp only [substS, Space.freeM]
      rcases hm with h | h
      · exact (substS_keeps_freeM F q σm σp m t h hl).trans Finset.subset_union_left
      · exact (substP_keeps_freeM F pp σm σp m t h hl).trans Finset.subset_union_right
  | .tailsUnion q, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM] at hm; simp only [substS, Space.freeM]
      exact substS_keeps_freeM F q σm σp m t hm hl
  | .tailsInter q, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM] at hm; simp only [substS, Space.freeM]
      exact substS_keeps_freeM F q σm σp m t hm hl
  | .range q _ _, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM] at hm; simp only [substS, Space.freeM]
      exact substS_keeps_freeM F q σm σp m t hm hl
  | .call _ refs ms, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM, Finset.mem_union] at hm
      simp only [substS, Space.freeM]
      rcases hm with h | h
      · exact (substPs_keeps_freeM F refs σm σp m t h hl).trans Finset.subset_union_left
      · exact (substSs_keeps_freeM F ms σm σp m t h hl).trans Finset.subset_union_right
  | .groundedPS q _, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM] at hm; simp only [substS, Space.freeM]
      exact substP_keeps_freeM F q σm σp m t hm hl
  | .groundedSS q _, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM] at hm; simp only [substS, Space.freeM]
      exact substS_keeps_freeM F q σm σp m t hm hl
  -- ==== THE THREE BINDER CASES.  Same argument each time; see `bindM_not_in_range`. ====
  | .fixpoint i r b, σm, σp, m, t, hm, hl => by
      simp only [Space.freeM, Finset.mem_union] at hm
      simp only [substS, Space.freeM]
      rcases hm with h | h
      · exact (substS_keeps_freeM F i σm σp m t h hl).trans Finset.subset_union_left
      · have hmr : m ≠ r := (Finset.mem_erase.mp h).1
        have hb : m ∈ b.freeM := (Finset.mem_erase.mp h).2
        have hl2 : lookupM (bindM F σm σp r b.freeM).2 m = some t :=
          bindM_lookup_ne F σm σp r b.freeM m t hmr hl
        have hsub := substS_keeps_freeM F b (bindM F σm σp r b.freeM).2 σp m t hb hl2
        -- and the bound name is not among `t`'s free names, so erasing it loses nothing
        have hnot : (bindM F σm σp r b.freeM).1 ∉ t.freeM := fun hin =>
          bindM_not_in_range F σm σp r b.freeM
            (freeM_subset_rangeM (dropM σm r) σp m t
              (by rw [lookupM_dropM_ne σm m r hmr]; exact hl) hin)
        refine Finset.Subset.trans ?_ Finset.subset_union_right
        intro z hz
        exact Finset.mem_erase.mpr ⟨fun hzeq => hnot (hzeq ▸ hz), hsub hz⟩
  | .iteration src sym rest t, σm, σp, m, t', hm, hl => by
      simp only [Space.freeM, Finset.mem_union] at hm
      simp only [substS, Space.freeM]
      rcases hm with h | h
      · exact (substS_keeps_freeM F src σm σp m t' h hl).trans Finset.subset_union_left
      · have hmr : m ≠ rest := (Finset.mem_erase.mp h).1
        have ht : m ∈ t.freeM := (Finset.mem_erase.mp h).2
        -- the REF binder is resolved first, so the mention binder is bound against `σp₂`
        set σp₂ := (bindR F σm σp sym t.freeR).2 with hσp
        have hl2 : lookupM (bindM F σm σp₂ rest t.freeM).2 m = some t' :=
          bindM_lookup_ne F σm σp₂ rest t.freeM m t' hmr hl
        have hsub := substS_keeps_freeM F t (bindM F σm σp₂ rest t.freeM).2 σp₂ m t' ht hl2
        have hnot : (bindM F σm σp₂ rest t.freeM).1 ∉ t'.freeM := fun hin =>
          bindM_not_in_range F σm σp₂ rest t.freeM
            (freeM_subset_rangeM (dropM σm rest) σp₂ m t'
              (by rw [lookupM_dropM_ne σm m rest hmr]; exact hl) hin)
        refine Finset.Subset.trans ?_ Finset.subset_union_right
        intro z hz
        exact Finset.mem_erase.mpr ⟨fun hzeq => hnot (hzeq ▸ hz), hsub hz⟩
  | .fold src ini acc sym rest t upd, σm, σp, m, t', hm, hl => by
      simp only [Space.freeM, Finset.mem_union] at hm
      simp only [substS, Space.freeM]
      rcases hm with (h | h) | h
      · exact (substS_keeps_freeM F src σm σp m t' h hl).trans
          (Finset.subset_union_left.trans Finset.subset_union_left)
      · exact (substP_keeps_freeM F ini σm σp m t' h hl).trans
          (Finset.subset_union_right.trans Finset.subset_union_left)
      · have hmr : m ≠ rest := (Finset.mem_erase.mp h).1
        have hin : m ∈ t.freeM ∪ upd.freeM := (Finset.mem_erase.mp h).2
        -- both ref binders are resolved before the mention binder, in that order
        set σpA := (bindR F σm σp acc (t.freeR ∪ upd.freeR)).2 with hσpA
        set σp₂ := (bindR F σm σpA sym (insert (bindR F σm σp acc (t.freeR ∪ upd.freeR)).1
                      (t.freeR ∪ upd.freeR))).2 with hσp
        set σm₂ := (bindM F σm σp₂ rest (t.freeM ∪ upd.freeM)).2 with hσm
        have hl2 : lookupM σm₂ m = some t' :=
          bindM_lookup_ne F σm σp₂ rest (t.freeM ∪ upd.freeM) m t' hmr hl
        have hnot : (bindM F σm σp₂ rest (t.freeM ∪ upd.freeM)).1 ∉ t'.freeM := fun hz =>
          bindM_not_in_range F σm σp₂ rest (t.freeM ∪ upd.freeM)
            (freeM_subset_rangeM (dropM σm rest) σp₂ m t'
              (by rw [lookupM_dropM_ne σm m rest hmr]; exact hl) hz)
        have hsub : t'.freeM ⊆ (substS F σm₂ σp₂ t).freeM ∪ (substP F σm₂ σp₂ upd).freeM := by
          rcases Finset.mem_union.mp hin with ht | hu
          · exact (substS_keeps_freeM F t σm₂ σp₂ m t' ht hl2).trans Finset.subset_union_left
          · exact (substP_keeps_freeM F upd σm₂ σp₂ m t' hu hl2).trans Finset.subset_union_right
        refine Finset.Subset.trans ?_ Finset.subset_union_right
        intro z hz
        exact Finset.mem_erase.mpr ⟨fun hzeq => hnot (hzeq ▸ hz), hsub hz⟩

end

end Zippy
