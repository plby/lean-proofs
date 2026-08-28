import Wikipedia.HopfProblem.CuspHoneycombTilingBasic

/-!
# Literal neighbor and edge intersections of the honeycomb cells

A closed dual hexagon meets exactly itself and the six cells at adjacent
integral vertices. The positive-coordinate neighbors meet it in the three
corresponding closed edges, expressed by their actual affine equations.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspHoneycombTiling

theorem baseCell_inter_cell_nonempty_iff (v : Lattice) :
    (baseCell ∩ cell v).Nonempty ↔
      v = 0 ∨ v = ![1, 0] ∨ v = ![0, 1] ∨ v = ![1, -1] ∨
        v = ![-1, 0] ∨ v = ![0, -1] ∨ v = ![-1, 1] := by
  constructor
  · rintro ⟨x, hx, hxv⟩
    have hcoord (i : Fin 2) : -1 ≤ v i ∧ v i ≤ 1 := by
      have hbase := abs_le.mp (baseCell_coordinate_bound_sharp hx i)
      have hshift := abs_le.mp (baseCell_coordinate_bound_sharp hxv i)
      change -(2 / 3 : ℝ) ≤ x i - (v i : ℝ) ∧
        x i - (v i : ℝ) ≤ 2 / 3 at hshift
      have hlo : (-2 : ℝ) < (v i : ℝ) := by linarith [hbase.1, hshift.2]
      have hhi : (v i : ℝ) < (2 : ℝ) := by linarith [hbase.2, hshift.1]
      have hlo' : (-2 : ℤ) < v i := by exact_mod_cast hlo
      have hhi' : v i < (2 : ℤ) := by exact_mod_cast hhi
      omega
    have hbase := abs_le.mp hx.1
    have hshift := abs_le.mp hxv.1
    change (-1 : ℝ) ≤ 2 * (x 0 - (v 0 : ℝ)) + (x 1 - (v 1 : ℝ)) ∧
      2 * (x 0 - (v 0 : ℝ)) + (x 1 - (v 1 : ℝ)) ≤ 1 at hshift
    have hlinear : (-2 : ℝ) ≤ 2 * (v 0 : ℝ) + (v 1 : ℝ) ∧
        2 * (v 0 : ℝ) + (v 1 : ℝ) ≤ 2 := by
      constructor <;> linarith [hbase.1, hbase.2, hshift.1, hshift.2]
    have hlinear' : (-2 : ℤ) ≤ 2 * v 0 + v 1 ∧ 2 * v 0 + v 1 ≤ 2 := by
      exact_mod_cast hlinear
    have h0 := hcoord 0
    have h1 := hcoord 1
    simp only [funext_iff, Fin.forall_fin_two, Pi.zero_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · intro hv
    refine ⟨fun i => (v i : ℝ) / 2, ?_, ?_⟩
    · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [baseCell]
    · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [cell, baseCell, latticePoint]

/-- Translate the first center to the origin without changing intersection incidence. -/
theorem cell_inter_cell_nonempty_iff_baseCell (v w : Lattice) :
    (cell v ∩ cell w).Nonempty ↔ (baseCell ∩ cell (w - v)).Nonempty := by
  constructor
  · rintro ⟨x, hxv, hxw⟩
    refine ⟨x - latticePoint v, hxv, ?_⟩
    apply (add_latticePoint_mem_cell_iff (w - v) v (x - latticePoint v)).mp
    simpa only [sub_add_cancel] using hxw
  · rintro ⟨x, hx, hxwv⟩
    refine ⟨x + latticePoint v, ?_, ?_⟩
    · have h := (add_latticePoint_mem_cell_iff 0 v x).mpr
        (by simpa only [cell_zero] using hx)
      simpa only [zero_add] using h
    · simpa only [sub_add_cancel] using
        (add_latticePoint_mem_cell_iff (w - v) v x).mpr hxwv

theorem cell_inter_cell_nonempty_iff (v w : Lattice) :
    (cell v ∩ cell w).Nonempty ↔
      w - v = 0 ∨ w - v = ![1, 0] ∨ w - v = ![0, 1] ∨ w - v = ![1, -1] ∨
        w - v = ![-1, 0] ∨ w - v = ![0, -1] ∨ w - v = ![-1, 1] := by
  rw [cell_inter_cell_nonempty_iff_baseCell, baseCell_inter_cell_nonempty_iff]

/-- The neighbor at `(1,0)` meets the base cell in its first positive edge. -/
theorem baseCell_inter_cell_one_zero :
    baseCell ∩ cell ![1, 0] = {x : Plane | x ∈ baseCell ∧ 2 * x 0 + x 1 = 1} := by
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    have hbase := abs_le.mp hx.1
    have hshift := abs_le.mp hy.1
    norm_num [latticePoint] at hshift
    linarith
  · rintro ⟨hx, he⟩
    refine ⟨hx, ?_⟩
    have h0 := abs_le.mp hx.1
    have h1 := abs_le.mp hx.2.1
    have h2 := abs_le.mp hx.2.2
    simp only [mem_cell, mem_baseCell, Pi.sub_apply, latticePoint_apply,
      Matrix.cons_val_zero, Int.cast_one, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.cast_zero, sub_zero, abs_le]
    repeat' apply And.intro
    all_goals linarith

/-- The neighbor at `(0,1)` meets the base cell in its third positive edge. -/
theorem baseCell_inter_cell_zero_one :
    baseCell ∩ cell ![0, 1] = {x : Plane | x ∈ baseCell ∧ x 0 + 2 * x 1 = 1} := by
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    have hbase := abs_le.mp hx.2.2
    have hshift := abs_le.mp hy.2.2
    norm_num [latticePoint] at hshift
    linarith
  · rintro ⟨hx, he⟩
    refine ⟨hx, ?_⟩
    have h0 := abs_le.mp hx.1
    have h1 := abs_le.mp hx.2.1
    have h2 := abs_le.mp hx.2.2
    simp only [mem_cell, mem_baseCell, Pi.sub_apply, latticePoint_apply,
      Matrix.cons_val_zero, Int.cast_zero, sub_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.cast_one, abs_le]
    repeat' apply And.intro
    all_goals linarith

/-- The neighbor at `(1,-1)` meets the base cell in its second positive edge. -/
theorem baseCell_inter_cell_one_neg_one :
    baseCell ∩ cell ![1, -1] = {x : Plane | x ∈ baseCell ∧ x 0 - x 1 = 1} := by
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    have hbase := abs_le.mp hx.2.1
    have hshift := abs_le.mp hy.2.1
    norm_num [latticePoint] at hshift
    linarith
  · rintro ⟨hx, he⟩
    refine ⟨hx, ?_⟩
    have h0 := abs_le.mp hx.1
    have h1 := abs_le.mp hx.2.1
    have h2 := abs_le.mp hx.2.2
    simp only [mem_cell, mem_baseCell, Pi.sub_apply, latticePoint_apply,
      Matrix.cons_val_zero, Int.cast_one, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.cast_neg, sub_neg_eq_add, abs_le]
    repeat' apply And.intro
    all_goals linarith

end Wikipedia.HopfProblem.CuspHoneycombTiling
