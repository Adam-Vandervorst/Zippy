import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The 15-puzzle's state space, independently of the cost model

A board is a permutation of the sixteen cells' tiles (`Board := Equiv.Perm (Fin 16)`, cell ↦ tile,
tile `0` the blank).  A move swaps the blank with one of its grid neighbours; the result is a
permutation again BY TYPE, which is the first invariant ("the board stays a board").  What the
resource analysis needs from the state space is proved here and nowhere near the cost model:

* every cell has at most four neighbours (`neighbours_le_four`), so a board has at most four
  successors (`successors_le_four`) and one BFS expansion of a frontier `F` has at most `4 · |F|`
  states (`expand_le`) — the finite maximum any bound on the expansion may reach;
* the blank of the moved board is the cell it moved to (`blank_move`), the move is undone by moving
  back (`move_move`), and every other cell keeps its tile (`move_tile_unchanged`): projection to a
  cell commutes with a move away from it;
* the whole state space is finite with `16!` boards (`states_card`);
* the path encoding `blank :: tiles of the other cells` has a fibre of at most 16 values at the
  first position and 15 at every other one (`nonblank_card`, `tile_fibre`): the per-cell / per-prefix
  fibre constraints the spatial domain is fed.

Everything is decidable over `Fin 16` where a computation is the proof (`decide`).
-/

namespace Zippy.Puzzle15

/-- a board: cell ↦ tile, a permutation of `Fin 16`; tile `0` is the blank -/
abbrev Board := Equiv.Perm (Fin 16)

/-- the cell holding the blank -/
def blank (b : Board) : Fin 16 := b.symm 0

def row (i : Fin 16) : ℕ := i.val / 4
def col (i : Fin 16) : ℕ := i.val % 4

/-- grid adjacency on the 4×4 board -/
def adjacent (i j : Fin 16) : Prop :=
  (row i = row j ∧ (col i + 1 = col j ∨ col j + 1 = col i)) ∨
  (col i = col j ∧ (row i + 1 = row j ∨ row j + 1 = row i))

instance : DecidableRel adjacent := fun i j => by unfold adjacent; infer_instance

def neighbours (i : Fin 16) : Finset (Fin 16) := Finset.univ.filter (adjacent i)

/-- no cell has more than four neighbours: a computation over the sixteen cells -/
theorem neighbours_le_four (i : Fin 16) : (neighbours i).card ≤ 4 := by
  revert i; decide

/-- a move: the blank swaps places with cell `j` (meaningful when `j` is adjacent to the blank; the
    permutation invariant holds for any `j`, which is why it is not a hypothesis here) -/
def move (b : Board) (j : Fin 16) : Board := b * Equiv.swap (blank b) j

/-- the blank of the moved board is the cell it moved to -/
theorem blank_move (b : Board) (j : Fin 16) : blank (move b j) = j := by
  simp only [blank, move, Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  exact Equiv.swap_apply_left _ _

/-- moving back undoes a move -/
theorem move_move (b : Board) (j : Fin 16) : move (move b j) (blank b) = b := by
  show move b j * Equiv.swap (blank (move b j)) (blank b) = b
  rw [blank_move]
  show b * Equiv.swap (blank b) j * Equiv.swap j (blank b) = b
  rw [mul_assoc, Equiv.swap_comm j (blank b), Equiv.swap_mul_self, mul_one]

/-- every cell other than the two swapped keeps its tile: projection commutes with a move elsewhere -/
theorem move_tile_unchanged (b : Board) (j c : Fin 16) (hc : c ≠ blank b) (hj : c ≠ j) :
    move b j c = b c := by
  simp [move, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hc hj]

/-- the successors of a board: one move per neighbour of the blank -/
def successors (b : Board) : Finset Board := (neighbours (blank b)).image (move b)

theorem successors_le_four (b : Board) : (successors b).card ≤ 4 :=
  Finset.card_image_le.trans (neighbours_le_four _)

/-- one BFS expansion of a frontier -/
def expand (F : Finset Board) : Finset Board := F.biUnion successors

/-- THE FINITE MAXIMUM of one expansion: at most four successors per frontier board -/
theorem expand_le (F : Finset Board) : (expand F).card ≤ 4 * F.card := by
  unfold expand
  calc (F.biUnion successors).card ≤ ∑ b ∈ F, (successors b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ F, 4 := Finset.sum_le_sum (fun b _ => successors_le_four b)
    _ = 4 * F.card := by simp [mul_comm]

/-- the whole state space is finite: `16!` boards -/
theorem states_card : Fintype.card Board = Nat.factorial 16 := by
  simp [Fintype.card_perm, Fintype.card_fin]

/-- the path encoding's first position (the blank cell) has 16 possible values, every other position a
    tile other than the blank: 15 values -/
theorem tile_fibre : (Finset.univ.filter (fun t : Fin 16 => t ≠ 0)).card = 15 := by decide

/-- a board has exactly fifteen non-blank cells -/
theorem nonblank_card (b : Board) : (Finset.univ.filter (fun c => b c ≠ 0)).card = 15 := by
  have h : (Finset.univ.filter (fun c => b c ≠ 0)) = Finset.univ.erase (b.symm 0) := by
    ext c
    simp [Equiv.eq_symm_apply]
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

end Zippy.Puzzle15
