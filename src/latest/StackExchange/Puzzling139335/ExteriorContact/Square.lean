import StackExchange.Puzzling139335.JordanAccessibility

/-! # The Jordan regions of the unit-square boundary -/

open Set

namespace Puzzling139335

theorem unitSquare_eq_closedSquare :
    unitSquare = Schoenflies.Plane.closedSquare squareCenter (1 / 2) := by
  rw [Schoenflies.Plane.closedSquare_eq_inter]
  ext p
  norm_num [unitSquare, squareCenter]

theorem isJordanCurve_frontier_unitSquare :
    Schoenflies.IsJordanCurve (frontier unitSquare) := by
  rw [unitSquare_eq_closedSquare]
  exact Schoenflies.isJordanCurve_frontier_closedSquare squareCenter (by norm_num)

theorem inside_frontier_unitSquare :
    Schoenflies.inside (frontier unitSquare) = interior unitSquare := by
  rw [unitSquare_eq_closedSquare, Schoenflies.inside_frontier_closedSquare,
    Schoenflies.Plane.interior_closedSquare]

theorem outside_frontier_unitSquare :
    Schoenflies.outside (frontier unitSquare) = unitSquareᶜ := by
  rw [unitSquare_eq_closedSquare, Schoenflies.outside_frontier_closedSquare]

theorem squareCenter_mem_inside_frontier_unitSquare :
    squareCenter ∈ Schoenflies.inside (frontier unitSquare) := by
  rw [unitSquare_eq_closedSquare, Schoenflies.inside_frontier_closedSquare]
  change Schoenflies.Plane.supDist squareCenter squareCenter < (1 / 2 : ℝ)
  simp

end Puzzling139335
