/-
==================================================================================================
THE MORKL SYNTAX WITH VARIABLES AND BINDERS.

`Core.lean` models the CLOSED pointwise fragment, which is all its two theorems need.  Substitution
is about variables and binders, so this module adds them: the two variable forms (`Space.mention`, a
space variable; `Path.deref`, a path variable) and the three binding forms, mirroring
`src/main/scala/MORKL.scala` constructor for constructor.

WHY A SEPARATE MODULE.  `Core.lean`'s `Space` has no binders at all, and its `denote` is therefore
environment-free — which is what makes `unwrap_wrap` a one-line statement.  Adding binders forces
`denote` to take an environment, and an environment-passing semantics for `Fixpoint` needs a least
fixpoint, which is `2E.1`'s subject and not `1E.1`'s.  Splitting keeps `Core`'s theorems stated in
the form their SMT twins are stated in, and lets this module be about the SYNTAX, which is what
substitution operates on.

WHAT IS MODELLED HERE, AND WHAT IS NOT.
  * MODELLED: every constructor `Subst.scala` walks, so `subst` here is total over exactly what the
    Scala is total over.  The two `Grounded*` space forms and the two grounded path forms carry an
    OPAQUE function in Scala (`docs/TRUSTED.md` T6 assumes only that it is deterministic); here the
    function is a `Name` standing for its identity, because substitution never inspects it and two
    grounded terms are equal for our purposes exactly when their argument and their function
    identity are.  That is a faithful model of what `Subst` does with them: descend the argument,
    keep `f`.
  * NOT MODELLED: `denote`.  See above; `2E.1` adds it.

`Name := String` deliberately, so a Lean-checked trace of the production substitutions (`1E.2`) can
carry the actual names the Scala used, including its `~m0`-style fresh ones.
==================================================================================================
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold

namespace Zippy

/-- A name.  `String`, matching `SpaceMention.s` / `PathRef.s`, so a trace can carry real names. -/
abbrev Name := String

-- `Path` and `Space` are MUTUALLY inductive: `Path.GroundedSP` carries a `Space` and
-- `Space.Singleton` carries a `Path`, exactly as in MORKL.scala.
mutual

/-- The PATH syntax.  Mirrors `enum Path` (MORKL.scala): `Deref`, `Constant`, `Concat`,
`GroundedPP`, `GroundedSP`. -/
inductive Path where
  /-- `Path.Deref(pr)` — a path VARIABLE -/
  | deref (r : Name)
  /-- `Path.Constant(pi)` — a ground path value -/
  | const (items : List Name)
  /-- `Path.Concat(l, r)` -/
  | concat (l r : Path)
  /-- `Path.GroundedPP(p, f)` — `f` is opaque; only its identity matters here -/
  | groundedPP (p : Path) (f : Name)
  /-- `Path.GroundedSP(s, f)` — carries a SPACE, so the space walker must see it -/
  | groundedSP (s : Space) (f : Name)

/-- The SPACE syntax.  Mirrors `enum Space` (MORKL.scala) constructor for constructor. -/
inductive Space where
  | empty
  | lit (paths : List (List Name))
  /-- `Space.Mention(v)` — a space VARIABLE -/
  | mention (m : Name)
  | singleton (p : Path)
  | union (x y : Space)
  | inter (x y : Space)
  | sub (x y : Space)
  | restriction (x y : Space)
  | raffination (x y : Space)
  | composition (x y : Space)
  | wrap (src : Space) (p : Path)
  | unwrap (src : Space) (p : Path)
  | tailsUnion (src : Space)
  | tailsInter (src : Space)
  | range (x : Space) (lo hi : Int)
  /-- `Space.Call(r, refs, mentions)` — `r` is a GLOBAL routine name, not a binder -/
  | call (r : Name) (refs : List Path) (mentions : List Space)
  /-- `Space.Iteration(src, symbol, rest, templates)` — binds `symbol` (a ref) and `rest` (a
  mention) in `templates`; `src` is OUTSIDE -/
  | iteration (src : Space) (symbol : Name) (rest : Name) (templates : Space)
  /-- `Space.Fixpoint(init, rec, body)` — binds `rec` in `body`; `init` is OUTSIDE -/
  | fixpoint (init : Space) (rec_ : Name) (body : Space)
  /-- `Space.Fold(src, initial, acc, symbol, rest, templates, update)` — binds `acc` and `symbol`
  (refs) and `rest` (a mention) in `templates` and `update`; `src` and `initial` are OUTSIDE -/
  | fold (src : Space) (initial : Path) (acc : Name) (symbol : Name) (rest : Name)
         (templates : Space) (update : Path)
  | groundedPS (p : Path) (f : Name)
  | groundedSS (s : Space) (f : Name)

end

-- NO `deriving DecidableEq`.  Lean's handler does not apply to a MUTUAL inductive, and writing the
-- instance by hand would be ~40 clauses of boilerplate for no gain: a concrete disagreement between
-- two substitution strategies is provable from CONSTRUCTOR INJECTIVITY, which `simp` knows, and
-- `1E.2`'s trace check compares the two sides by reducing both to normal form rather than by
-- `decide`.  If a later task needs the instance, that is the point to write it.

/-! ### Size

A structural size, used as the well-founded measure wherever a definition is not obviously
structurally recursive, and to state that renaming preserves shape. -/

mutual
  def Path.size : Path → Nat
    | .deref _ => 1
    | .const _ => 1
    | .concat l r => 1 + l.size + r.size
    | .groundedPP p _ => 1 + p.size
    | .groundedSP s _ => 1 + s.size
  def Space.size : Space → Nat
    | .empty => 1
    | .lit _ => 1
    | .mention _ => 1
    | .singleton p => 1 + p.size
    | .union x y => 1 + x.size + y.size
    | .inter x y => 1 + x.size + y.size
    | .sub x y => 1 + x.size + y.size
    | .restriction x y => 1 + x.size + y.size
    | .raffination x y => 1 + x.size + y.size
    | .composition x y => 1 + x.size + y.size
    | .wrap s p => 1 + s.size + p.size
    | .unwrap s p => 1 + s.size + p.size
    | .tailsUnion s => 1 + s.size
    | .tailsInter s => 1 + s.size
    | .range x _ _ => 1 + x.size
    | .call _ refs ms =>
        1 + (refs.map Path.size).sum + (ms.map Space.size).sum
    | .iteration src _ _ t => 1 + src.size + t.size
    | .fixpoint i _ b => 1 + i.size + b.size
    | .fold src ini _ _ _ t upd => 1 + src.size + ini.size + t.size + upd.size
    | .groundedPS p _ => 1 + p.size
    | .groundedSS s _ => 1 + s.size
end

/-! ### Free variables

Two sorts, two functions, mirroring `Matching.freeMentions` / `Matching.freeRefs`.  A `Finset Name`
rather than a `List`, because every use below is membership and union. -/

mutual
  /-- free path refs of a path -/
  def Path.freeR : Path → Finset Name
    | .deref r => {r}
    | .const _ => ∅
    | .concat l r => l.freeR ∪ r.freeR
    | .groundedPP p _ => p.freeR
    | .groundedSP s _ => s.freeR
  /-- free path refs of a space.  `Iteration` binds `symbol`; `Fold` binds `acc` and `symbol` over
  `templates` and `update` but NOT over `src`/`initial`. -/
  def Space.freeR : Space → Finset Name
    | .empty | .lit _ | .mention _ => ∅
    | .singleton p => p.freeR
    | .union x y | .inter x y | .sub x y
    | .restriction x y | .raffination x y | .composition x y => x.freeR ∪ y.freeR
    | .wrap s p | .unwrap s p => s.freeR ∪ p.freeR
    | .tailsUnion s | .tailsInter s => s.freeR
    | .range x _ _ => x.freeR
    -- CONS-SHAPED, via the two helpers below, and not `(refs.map freeR).foldl (· ∪ ·) ∅`.  A
    -- `foldl` over a mapped list gives no usable equation for `e :: σ`, and every proof about
    -- `call` needs exactly that equation; the helpers give it by `rfl`.
    | .call _ refs ms => Path.freeRs refs ∪ Space.freeRs ms
    | .iteration src sym _ t => src.freeR ∪ (t.freeR.erase sym)
    | .fixpoint i _ b => i.freeR ∪ b.freeR
    | .fold src ini acc sym _ t upd =>
        src.freeR ∪ ini.freeR ∪ ((t.freeR ∪ upd.freeR).erase acc).erase sym
    | .groundedPS p _ => p.freeR
    | .groundedSS s _ => s.freeR
  /-- free refs of a list of paths (a `Call`'s `refs`) -/
  def Path.freeRs : List Path → Finset Name
    | [] => ∅
    | p :: rest => p.freeR ∪ Path.freeRs rest
  /-- free refs of a list of spaces (a `Call`'s `mentions`) -/
  def Space.freeRs : List Space → Finset Name
    | [] => ∅
    | s :: rest => s.freeR ∪ Space.freeRs rest
end

mutual
  /-- free space mentions of a path (reachable only through `groundedSP`) -/
  def Path.freeM : Path → Finset Name
    | .deref _ => ∅
    | .const _ => ∅
    | .concat l r => l.freeM ∪ r.freeM
    | .groundedPP p _ => p.freeM
    | .groundedSP s _ => s.freeM
  /-- free space mentions of a space.  `Iteration`/`Fold` bind `rest` over `templates` (and, for
  `Fold`, `update`); `Fixpoint` binds `rec_` over `body`. -/
  def Space.freeM : Space → Finset Name
    | .empty | .lit _ => ∅
    | .mention m => {m}
    | .singleton p => p.freeM
    | .union x y | .inter x y | .sub x y
    | .restriction x y | .raffination x y | .composition x y => x.freeM ∪ y.freeM
    | .wrap s p | .unwrap s p => s.freeM ∪ p.freeM
    | .tailsUnion s | .tailsInter s => s.freeM
    | .range x _ _ => x.freeM
    | .call _ refs ms => Path.freeMs refs ∪ Space.freeMs ms
    | .iteration src _ rest t => src.freeM ∪ (t.freeM.erase rest)
    | .fixpoint i r b => i.freeM ∪ (b.freeM.erase r)
    | .fold src ini _ _ rest t upd =>
        src.freeM ∪ ini.freeM ∪ ((t.freeM ∪ upd.freeM).erase rest)
    | .groundedPS p _ => p.freeM
    | .groundedSS s _ => s.freeM
  def Path.freeMs : List Path → Finset Name
    | [] => ∅
    | p :: rest => p.freeM ∪ Path.freeMs rest
  def Space.freeMs : List Space → Finset Name
    | [] => ∅
    | s :: rest => s.freeM ∪ Space.freeMs rest
end

end Zippy
