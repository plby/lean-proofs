import Wikipedia.HopfProblem.CuspHoneycombTilingBasic
import Mathlib.Tactic.SplitIfs

/-!
# An explicit floor-based covering by the dual hexagons

Inside each integral unit square, the two diagonally ordered halves are
covered by the three neighboring hexagons given by their linear
inequalities.  Translating the fractional parts back gives a concrete
integral center for every point of the real plane.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspHoneycombTiling

/-- A concrete neighboring center for a point of the real unit square. -/
def squareCenter (p q : ℝ) : Lattice :=
  if q ≤ p then
    if 2 * p + q ≤ 1 then 0
    else if 2 ≤ p + 2 * q then 1
    else ![1, 0]
  else
    if p + 2 * q ≤ 1 then 0
    else if 2 ≤ 2 * p + q then 1
    else ![0, 1]

/-- The six branches of the center formula satisfy the literal six
half-plane inequalities of their chosen hexagon. -/
theorem mem_cell_squareCenter (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (![p, q] : Plane) ∈ cell (squareCenter p q) := by
  unfold squareCenter
  split_ifs
  all_goals simp only [mem_cell, mem_baseCell, Pi.sub_apply, latticePoint_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Pi.zero_apply, Pi.one_apply, Int.cast_zero, Int.cast_one, sub_zero, abs_le]
  all_goals repeat' apply And.intro
  all_goals linarith

/-- The integer floor is corrected by one of the four corners of its
unit square.  No choice of an abstract covering cell is used. -/
def floorCenter (x : Plane) : Lattice :=
  fun i => ⌊x i⌋ + squareCenter (Int.fract (x 0)) (Int.fract (x 1)) i

theorem sub_latticePoint_floorCenter (x : Plane) :
    x - latticePoint (floorCenter x) =
      (![Int.fract (x 0), Int.fract (x 1)] : Plane) -
        latticePoint (squareCenter (Int.fract (x 0)) (Int.fract (x 1))) := by
  funext i
  simp only [Pi.sub_apply, latticePoint, floorCenter, Int.cast_add, sub_add_eq_sub_sub]
  rw [Int.self_sub_floor]
  fin_cases i <;> rfl

theorem mem_cell_floorCenter (x : Plane) : x ∈ cell (floorCenter x) := by
  change x - latticePoint (floorCenter x) ∈ baseCell
  rw [sub_latticePoint_floorCenter]
  exact mem_cell_squareCenter _ _ (Int.fract_nonneg _) (Int.fract_lt_one _).le
    (Int.fract_nonneg _) (Int.fract_lt_one _).le

/-- Every real point lies in one of the actual integral translates. -/
theorem exists_mem_cell (x : Plane) : ∃ v : Lattice, x ∈ cell v :=
  ⟨floorCenter x, mem_cell_floorCenter x⟩

theorem iUnion_cell : (⋃ v : Lattice, cell v) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  exact exists_mem_cell x

end Wikipedia.HopfProblem.CuspHoneycombTiling
