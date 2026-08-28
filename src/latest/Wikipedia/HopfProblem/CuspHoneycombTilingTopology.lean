import Wikipedia.HopfProblem.CuspHoneycombTilingBasic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Order.Compact

/-!
# Topology of the literal honeycomb cells

The central hexagon and all of its lattice translates are closed and compact.
Every unit ball meets only cells whose lattice indices belong to an explicit
finite integer box. Thus the actual indexed family of cells is locally finite,
and a compact subset of the plane meets only finitely many cells.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombTiling

theorem baseCell_isClosed : IsClosed baseCell := by
  have h0 : IsClosed {x : Plane | |2 * x 0 + x 1| ≤ 1} :=
    isClosed_le ((continuous_const.mul (continuous_apply 0)).add
      (continuous_apply 1)).abs continuous_const
  have h1 : IsClosed {x : Plane | |x 0 - x 1| ≤ 1} :=
    isClosed_le ((continuous_apply 0).sub (continuous_apply 1)).abs continuous_const
  have h2 : IsClosed {x : Plane | |x 0 + 2 * x 1| ≤ 1} :=
    isClosed_le ((continuous_apply 0).add
      (continuous_const.mul (continuous_apply 1))).abs continuous_const
  exact h0.inter (h1.inter h2)

theorem baseCell_isCompact : IsCompact baseCell := by
  apply (isCompact_Icc : IsCompact (Icc (-1 : Plane) 1)).of_isClosed_subset
    baseCell_isClosed
  intro x hx
  exact ⟨fun i => (abs_le.mp (baseCell_coordinate_bound hx i)).1,
    fun i => (abs_le.mp (baseCell_coordinate_bound hx i)).2⟩

theorem cell_isClosed (v : Lattice) : IsClosed (cell v) :=
  baseCell_isClosed.preimage (continuous_id.sub continuous_const)

theorem cell_eq_image_add (v : Lattice) :
    cell v = (fun x : Plane => x + latticePoint v) '' baseCell := by
  ext x
  constructor
  · intro hx
    exact ⟨x - latticePoint v, hx, sub_add_cancel _ _⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_cell, add_sub_cancel_right] using hy

theorem cell_isCompact (v : Lattice) : IsCompact (cell v) := by
  rw [cell_eq_image_add]
  exact baseCell_isCompact.image (continuous_id.add continuous_const)

/-- A unit ball can meet only finitely many of the actual lattice cells. -/
theorem cell_finite_inter_ball (x : Plane) :
    {v : Lattice | (cell v ∩ Metric.ball x 1).Nonempty}.Finite := by
  have hbox : {v : Lattice | ∀ i,
      v i ∈ Icc ⌈x i - 2⌉ ⌊x i + 2⌋}.Finite :=
    Set.Finite.pi' (fun i => Set.finite_Icc ⌈x i - 2⌉ ⌊x i + 2⌋)
  apply hbox.subset
  rintro v ⟨y, hyv, hyx⟩ i
  have hcoord := abs_le.mp (cell_coordinate_bound hyv i)
  have hdist : |y i - x i| < 1 := by
    simpa only [Real.dist_eq] using
      (dist_le_pi_dist y x i).trans_lt (Metric.mem_ball.mp hyx)
  have hnear := abs_lt.mp hdist
  constructor
  · apply Int.ceil_le.mpr
    linarith [hcoord.2, hnear.1]
  · apply Int.le_floor.mpr
    linarith [hcoord.1, hnear.2]

theorem cell_locallyFinite : LocallyFinite cell := by
  intro x
  exact ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), cell_finite_inter_ball x⟩

theorem cell_finite_inter_compact {K : Set Plane} (hK : IsCompact K) :
    {v : Lattice | (cell v ∩ K).Nonempty}.Finite :=
  cell_locallyFinite.finite_nonempty_inter_compact hK

end Wikipedia.HopfProblem.CuspHoneycombTiling
