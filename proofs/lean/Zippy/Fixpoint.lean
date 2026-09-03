/-
==================================================================================================
T2, MECHANIZED (plan.md 1E.3).

`docs/TRUSTED.md` T2 is "the four bridging induction principles of `fixpoint_is_lfp.smt2`".  That
file proves each of them in three parts — base, step, then the bridging principle asserted "exactly
as a hand proof invokes it" — and the four `(assert (forall ((n Int)) ...))` lines are the trusted
items.  Its own header on the pattern:

  "each an explicit induction in the style of no_infinite_descent.smt2 - base, step, then the
   bridging induction principle"

The bases and the steps are machine-checked by z3.  What is asserted is the induction over ℕ, which
`Int`-sorted SMT cannot derive: there is no induction rule, and the `>= n 0` guard is a side
condition rather than a well-founded type.  In Lean the four are `Nat.rec`, so they are theorems.

==THE FOUR, IN THE ORDER THE SMT FILE ASSERTS THEM==
  (i)    `∀ n ≥ 0, C n ⊆ C (n+1)`                            — the Kleene chain ASCENDS
  (ii)   `∀ n ≥ 0, A n = C n`                                 — the accumulator is REDUNDANT
  (iii-a)`∀ n ≥ 0, init ⊆ C n`                                — every iterate is above `init`
  (iii-b)`∀ n ≥ 0, ∀ y, init ⊆ y → F y ⊆ y → C n ⊆ y`         — and below every pre-fixpoint

plus the CONCLUSION they exist for, which is what every lowering pass cites:

  (iii-c) at a stationary index, `A n` is a fixpoint of `F`, contains `init`, and is contained in
          every pre-fixpoint above `init` — i.e. `A n = lfp_{⊇init} F`.

`(iv)` of the SMT file is NOT one of the four: it is a single `card` check, and its bridging
principle is `no_infinite_descent.smt2` rather than an assertion in that file.  It is the FINITENESS
half — the stationary index EXISTS — and it is stated at the end of this file as an explicit
hypothesis rather than proved, because it is a different kind of claim (a well-foundedness argument
over a finite universe) and `docs/TRUSTED.md` attributes it elsewhere.  Saying which of the five
parts is and is not discharged here is the point.

==THE TWO SIDE CONDITIONS ARE HYPOTHESES, AS THEY ARE IN THE SMT FILE==
`fixpoint_is_lfp.smt2`'s header: the iteration reaches the least post-fixpoint "under TWO premises —
monotone `F` AND `init ⊆ F(init)`", and it carries a machine-checked monotone-but-non-inflationary
counterexample where accumulating the iterates of `F` gives `{a,b}` while the least post-fixpoint is
`{a,b,c}`.  Both premises are hypotheses of every theorem below, so none of them can be read as
holding unconditionally — which is exactly the failure the counterexample records.

`Space.Fixpoint`'s own doc explains why the executors fold the union into the iteration: it makes
`init ⊆ F(init)` hold BY CONSTRUCTION, leaving monotonicity as the one side condition.  `(ii)` below
is where that earns its keep — without ascent the union does not collapse and `A n = C n` is FALSE.

    proofs/lean/Zippy/Fixpoint.lean#Zippy.Kleene.stationary_is_lfp
==================================================================================================
-/
import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation

namespace Zippy.Kleene

variable {α : Type*}

/-- `C k` — the Kleene chain: `C 0 = init`, `C (k+1) = F (C k)`.  `(declare-fun C (Int) NSet)` with
`(= (C 0) init)` and `(= (C (+ n 1)) (F (C n)))` in the SMT file. -/
def chain (F : Set α → Set α) (init : Set α) : Nat → Set α
  | 0 => init
  | n + 1 => F (chain F init n)

/-- `A k` — the ACCUMULATOR the executors actually compute: `A 0 = init`,
`A (k+1) = A k ∪ C (k+1)`.  `(= (A (+ n 1)) (cup (A n) (C (+ n 1))))`. -/
def acc (F : Set α → Set α) (init : Set α) : Nat → Set α
  | 0 => init
  | n + 1 => acc F init n ∪ chain F init (n + 1)

@[simp] theorem chain_zero (F : Set α → Set α) (init : Set α) : chain F init 0 = init := rfl
@[simp] theorem chain_succ (F : Set α → Set α) (init : Set α) (n : Nat) :
    chain F init (n + 1) = F (chain F init n) := rfl
@[simp] theorem acc_zero (F : Set α → Set α) (init : Set α) : acc F init 0 = init := rfl
@[simp] theorem acc_succ (F : Set α → Set α) (init : Set α) (n : Nat) :
    acc F init (n + 1) = acc F init n ∪ chain F init (n + 1) := rfl

/-! ### The two side conditions

They are EXPLICIT PARAMETERS of every theorem below rather than section `variable`s, so that no
statement can be read as holding unconditionally and so that each recursive call has to pass them —
which is the same discipline `fixpoint_is_lfp.smt2` uses by asserting them at the top of the file
and re-deriving each base and step under them.

  `hmono : ∀ x y, x ⊆ y → F x ⊆ F y`   MONOTONICITY of `F` — the one side condition
                                        `AgnosticPipeline.monotoneInMention` checks before an emitter
                                        may write a first-class `Fix`.
  `hinfl : init ⊆ F init`               INFLATIONARY AT `init`.  Holds BY CONSTRUCTION for
                                        `Space.Fixpoint`, whose body is `init ∪ F(·)`; a hypothesis
                                        here because `fixpoint_is_lfp.smt2` carries a machine-checked
                                        counterexample for the shape that lacks it — monotone but not
                                        inflationary, where accumulating the iterates of `F` gives
                                        `{a,b}` while the least post-fixpoint is `{a,b,c}`. -/

/-- **(i)** THE KLEENE CHAIN ASCENDS.
`(assert (forall ((n Int)) (=> (>= n 0) (subset (C n) (C (+ n 1))))))`

Base is `hinfl` itself; the step is monotonicity.  Over `Nat` the bridge is `Nat.rec`. -/
theorem chain_ascends (F : Set α → Set α) (init : Set α)
    (hmono : ∀ x y : Set α, x ⊆ y → F x ⊆ F y) (hinfl : init ⊆ F init) :
    ∀ n, chain F init n ⊆ chain F init (n + 1)
  | 0 => by simpa using hinfl
  | n + 1 => by simpa using hmono _ _ (chain_ascends F init hmono hinfl n)

/-- **(ii)** THE ACCUMULATOR IS REDUNDANT: `A n = C n`.
`(assert (forall ((n Int)) (=> (>= n 0) (= (A n) (C n)))))`

This is where ASCENDING earns its keep, exactly as the SMT file's comment says: the step needs
`C n ⊆ C (n+1)` for the union `A n ∪ C (n+1)` to collapse, and without it `A n = C n` is FALSE.
That is obligation O10. -/
theorem acc_eq_chain (F : Set α → Set α) (init : Set α)
    (hmono : ∀ x y : Set α, x ⊆ y → F x ⊆ F y) (hinfl : init ⊆ F init) :
    ∀ n, acc F init n = chain F init n
  | 0 => rfl
  | n + 1 => by
      rw [acc_succ, acc_eq_chain F init hmono hinfl n]
      exact Set.union_eq_self_of_subset_left (chain_ascends F init hmono hinfl n)

/-- **(iii-a)** EVERY ITERATE IS ABOVE `init`.
`(assert (forall ((n Int)) (=> (>= n 0) (subset init (C n)))))` -/
theorem init_subset_chain (F : Set α → Set α) (init : Set α)
    (hmono : ∀ x y : Set α, x ⊆ y → F x ⊆ F y) (hinfl : init ⊆ F init) :
    ∀ n, init ⊆ chain F init n
  | 0 => subset_rfl
  | n + 1 => (init_subset_chain F init hmono hinfl n).trans
               (chain_ascends F init hmono hinfl n)

/-- **(iii-b)** EVERY ITERATE IS BELOW EVERY PRE-FIXPOINT ABOVE `init`.
`(assert (forall ((n Int) (y NSet)) (=> (and (>= n 0) (subset init y) (subset (F y) y)) (subset (C n) y))))`

`y` is UNIVERSALLY QUANTIFIED, which the SMT file flags as the reason the conclusion is genuinely
"least" and not "least among some enumerated candidates".  It is universally quantified here too,
and note that this one needs only MONOTONICITY — `hinfl` is not used. -/
theorem chain_below_prefixpoint (F : Set α → Set α) (init : Set α)
    (hmono : ∀ x y : Set α, x ⊆ y → F x ⊆ F y) :
    ∀ n (y : Set α), init ⊆ y → F y ⊆ y → chain F init n ⊆ y
  | 0, y, hy, _ => by simpa using hy
  | n + 1, y, hy, hFy => by
      have hih := chain_below_prefixpoint F init hmono n y hy hFy
      have : chain F init (n + 1) ⊆ F y := by simpa using hmono _ _ hih
      exact this.trans hFy

/-- **(iii-c)** THE CONCLUSION, which is the statement every lowering pass cites: at a STATIONARY
index the returned accumulator `A n` is a fixpoint of `F`, contains `init`, and is contained in every
pre-fixpoint above `init` — i.e. it is `lfp_{⊇init} F`.

The SMT file's own words: "at a stationary index n the RETURNED value A_n is a fixpoint of F,
contains I, and is contained in every pre-fixpoint above I - i.e. A_n = lfp_{>=I} F". -/
theorem stationary_is_lfp (F : Set α → Set α) (init : Set α)
    (hmono : ∀ x y : Set α, x ⊆ y → F x ⊆ F y) (hinfl : init ⊆ F init)
    (n : Nat) (hstat : chain F init (n + 1) = chain F init n) :
    F (acc F init n) = acc F init n
    ∧ init ⊆ acc F init n
    ∧ ∀ y : Set α, init ⊆ y → F y ⊆ y → acc F init n ⊆ y := by
  have hAC : acc F init n = chain F init n := acc_eq_chain F init hmono hinfl n
  refine ⟨?_, ?_, ?_⟩
  · -- `F (A n) = F (C n) = C (n+1) = C n = A n`
    rw [hAC]; simpa using hstat
  · rw [hAC]; exact init_subset_chain F init hmono hinfl n
  · intro y hy hFy
    rw [hAC]; exact chain_below_prefixpoint F init hmono n y hy hFy

/-- and the least fixpoint is UNIQUE as such, which is what makes "the" least fixpoint well posed.
Not one of T2's four — it needs no induction at all — but stated because
`terminating/least_fixpoint_unique.smt2` is a separate obligation and this is its content. -/
theorem lfp_unique (F : Set α → Set α) (init x y : Set α)
    (hx : init ⊆ x ∧ F x ⊆ x ∧ ∀ z : Set α, init ⊆ z → F z ⊆ z → x ⊆ z)
    (hy : init ⊆ y ∧ F y ⊆ y ∧ ∀ z : Set α, init ⊆ z → F z ⊆ z → y ⊆ z) : x = y :=
  Set.Subset.antisymm (hx.2.2 y hy.1 hy.2.1) (hy.2.2 x hx.1 hx.2.1)

/-! ### WHAT IS NOT DISCHARGED HERE, AND WHY

`fixpoint_is_lfp.smt2`'s part **(iv)** — "over a FINITE universe the stationary index EXISTS: every
non-stationary step strictly shrinks `card(top \ C_k)`" — is not proved above, and it is not one of
T2's four bridging inductions: it is a single `card` check whose bridging principle lives in
`no_infinite_descent.smt2`.

It is a WELL-FOUNDEDNESS claim over a finite universe, not an induction over the chain index, and it
is the one part of `fixpoint_is_lfp` whose Lean form would need a finiteness hypothesis
(`Finite α`) that none of the theorems above require.  `stationary_is_lfp` takes the stationary index
as a HYPOTHESIS for exactly that reason: it says what the answer IS once the loop stops, and (iv)
says the loop stops.  Conflating them would let a reader take the termination for granted from a
theorem that does not mention it. -/

/-- (iv)'s shape, as a statement rather than a theorem: on a finite universe a strictly decreasing
`Nat` measure at every non-stationary step forces a stationary index.  Recorded so that the gap is a
named proposition and not an absence; `2E.1` is where the lattice development makes it provable. -/
def StationaryIndexExists (F : Set α → Set α) (init : Set α) : Prop :=
  ∃ n, chain F init (n + 1) = chain F init n

end Zippy.Kleene
