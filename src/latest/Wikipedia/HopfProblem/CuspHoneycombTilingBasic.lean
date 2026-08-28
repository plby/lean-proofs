import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The literal dual hexagons of the integral triangular lattice

The central cell is cut out by its six affine half-plane inequalities.
Every other cell is its translate by an actual integral plane vector.
These are subsets of the ordinary real plane, with its usual topology.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombTiling

abbrev Plane := Fin 2 → ℝ
abbrev Lattice := Fin 2 → ℤ

def latticePoint (v : Lattice) : Plane := fun i => (v i : ℝ)

@[simp] theorem latticePoint_apply (v : Lattice) (i : Fin 2) :
    latticePoint v i = (v i : ℝ) := rfl

@[simp] theorem latticePoint_zero : latticePoint 0 = 0 := by
  funext i
  simp [latticePoint]

@[simp] theorem latticePoint_add (v w : Lattice) :
    latticePoint (v + w) = latticePoint v + latticePoint w := by
  funext i
  simp [latticePoint]

@[simp] theorem latticePoint_neg (v : Lattice) : latticePoint (-v) = -latticePoint v := by
  funext i
  simp [latticePoint]

/-- The closed hexagonal cell dual to the integral vertex at the origin. -/
def baseCell : Set Plane :=
  {x | |2 * x 0 + x 1| ≤ 1 ∧ |x 0 - x 1| ≤ 1 ∧ |x 0 + 2 * x 1| ≤ 1}

/-- The actual translate of the central dual cell to an integral vertex. -/
def cell (v : Lattice) : Set Plane := {x | x - latticePoint v ∈ baseCell}

@[simp] theorem mem_baseCell (x : Plane) :
    x ∈ baseCell ↔
      |2 * x 0 + x 1| ≤ 1 ∧ |x 0 - x 1| ≤ 1 ∧ |x 0 + 2 * x 1| ≤ 1 := Iff.rfl

@[simp] theorem mem_cell (v : Lattice) (x : Plane) :
    x ∈ cell v ↔ x - latticePoint v ∈ baseCell := Iff.rfl

@[simp] theorem cell_zero : cell 0 = baseCell := by
  ext x
  simp only [mem_cell, latticePoint_zero, sub_zero]

@[simp] theorem zero_mem_baseCell : (0 : Plane) ∈ baseCell := by
  norm_num [baseCell]

@[simp] theorem latticePoint_mem_cell (v : Lattice) : latticePoint v ∈ cell v := by
  simp only [mem_cell, sub_self, zero_mem_baseCell]

/-- Each coordinate actually lies in the sharper interval `[-2/3,2/3]`. -/
theorem baseCell_coordinate_bound_sharp {x : Plane} (hx : x ∈ baseCell) (i : Fin 2) :
    |x i| ≤ (2 / 3 : ℝ) := by
  obtain ⟨h0, h1, h2⟩ := hx
  have h0' := abs_le.mp h0
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  fin_cases i
  · change |x 0| ≤ (2 / 3 : ℝ)
    exact abs_le.mpr ⟨by linarith [h0'.1, h1'.1], by linarith [h0'.2, h1'.2]⟩
  · change |x 1| ≤ (2 / 3 : ℝ)
    exact abs_le.mpr ⟨by linarith [h2'.1, h1'.2], by linarith [h2'.2, h1'.1]⟩

theorem baseCell_coordinate_bound {x : Plane} (hx : x ∈ baseCell) (i : Fin 2) :
    |x i| ≤ 1 := (baseCell_coordinate_bound_sharp hx i).trans (by norm_num)

theorem cell_coordinate_bound {v : Lattice} {x : Plane} (hx : x ∈ cell v) (i : Fin 2) :
    |x i - (v i : ℝ)| ≤ 1 := baseCell_coordinate_bound hx i

/-- Integral translation carries the literal cells to the corresponding
translated cells. -/
theorem add_latticePoint_mem_cell_iff (v w : Lattice) (x : Plane) :
    x + latticePoint w ∈ cell (v + w) ↔ x ∈ cell v := by
  simp only [mem_cell, latticePoint_add, add_sub_add_right_eq_sub]

end Wikipedia.HopfProblem.CuspHoneycombTiling
