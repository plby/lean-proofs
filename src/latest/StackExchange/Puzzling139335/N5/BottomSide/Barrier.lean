import StackExchange.Puzzling139335.RectangularHull.Interlacing.Regions
import StackExchange.Puzzling139335.SquareExterior
import StackExchange.Puzzling139335.N8.SideOwnership.Geometry

/-!
# Boundary barriers along the bottom and left sides

If one Jordan piece contains both endpoints of a square side, a second
piece reaching the complementary square boundary cannot meet the side
away from its endpoints.  These are applications of the actual boundary
arc interlacing obstruction, without convexity assumptions on the pieces.
-/

open Set

namespace Puzzling139335.N5

/-- A piece meeting the square boundary outside the bottom side cannot
also meet the open bottom side when a distinct piece contains both bottom
corners. -/
theorem bottom_boundary_contacts_impossible (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j)
    (hBL : corner 0 ∈ d.piece i) (hBR : corner 1 ∈ d.piece i)
    {z s : Plane} (hzj : z ∈ d.piece j) (hsj : s ∈ d.piece j)
    (hz : z ∈ segment ℝ (corner 0) (corner 1) \ {corner 0, corner 1})
    (hsfront : s ∈ frontier unitSquare)
    (hsnotbottom : s ∉ segment ℝ (corner 0) (corner 1)) : False := by
  exact RectangularHull.boundary_arc_contacts_impossible
    (d.jordan i) (d.jordan j) isJordanRegion_unitSquare
    (d.piece_subset i) (d.piece_subset j) (d.disjoint_interiors hij)
    (N8.side_segment_isArcBetween 0) (N8.side_segment_subset_frontier_unitSquare 0)
    hBL hBR hzj hsj hz hsfront hsnotbottom

/-- A piece containing the top-right corner cannot touch the open bottom
side when another piece contains both bottom corners. -/
theorem bottom_open_not_mem_of_top_right (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j)
    (hBL : corner 0 ∈ d.piece i) (hBR : corner 1 ∈ d.piece i)
    (hTR : corner 2 ∈ d.piece j) {z : Plane}
    (hz : z ∈ segment ℝ (corner 0) (corner 1) \ {corner 0, corner 1}) :
    z ∉ d.piece j := by
  intro hzj
  apply bottom_boundary_contacts_impossible d hij hBL hBR hzj hTR hz
  · exact corner_mem_frontier_of_subset (Subset.refl unitSquare)
      (corner_mem_unitSquare 2)
  · intro hmem
    have hends := (N8.corner_mem_side_segment_iff 0 2).mp hmem
    rcases hends with h | h
    · exact (by decide : (2 : Fin 4) ≠ 0) h
    · exact (by decide : (2 : Fin 4) ≠ 1) h

/-- The corresponding arbitrary-contact barrier for the left side,
oriented from the bottom-left to the top-left corner. -/
theorem left_boundary_contacts_impossible (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j)
    (hBL : corner 0 ∈ d.piece i) (hTL : corner 3 ∈ d.piece i)
    {z s : Plane} (hzj : z ∈ d.piece j) (hsj : s ∈ d.piece j)
    (hz : z ∈ segment ℝ (corner 0) (corner 3) \ {corner 0, corner 3})
    (hsfront : s ∈ frontier unitSquare)
    (hsnotleft : s ∉ segment ℝ (corner 0) (corner 3)) : False := by
  have hne : corner 0 ≠ corner 3 := by
    intro heq
    exact N8.adjacent_corners_ne 3 heq.symm
  have hboundary : segment ℝ (corner 0) (corner 3) ⊆ frontier unitSquare := by
    rw [segment_symm]
    exact N8.side_segment_subset_frontier_unitSquare 3
  exact RectangularHull.boundary_arc_contacts_impossible
    (d.jordan i) (d.jordan j) isJordanRegion_unitSquare
    (d.piece_subset i) (d.piece_subset j) (d.disjoint_interiors hij)
    (Schoenflies.isArcBetween_segment hne) hboundary
    hBL hTL hzj hsj hz hsfront hsnotleft

/-- A piece containing the top-right corner cannot touch the open left
side when another piece contains both left corners. -/
theorem left_open_not_mem_of_top_right (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j)
    (hBL : corner 0 ∈ d.piece i) (hTL : corner 3 ∈ d.piece i)
    (hTR : corner 2 ∈ d.piece j) {z : Plane}
    (hz : z ∈ segment ℝ (corner 0) (corner 3) \ {corner 0, corner 3}) :
    z ∉ d.piece j := by
  intro hzj
  apply left_boundary_contacts_impossible d hij hBL hTL hzj hTR hz
  · exact corner_mem_frontier_of_subset (Subset.refl unitSquare)
      (corner_mem_unitSquare 2)
  · intro hmem
    have hmem' : corner 2 ∈ segment ℝ (corner 3) (corner (3 + 1)) := by
      rw [segment_symm]
      exact hmem
    have hends := (N8.corner_mem_side_segment_iff 3 2).mp hmem'
    rcases hends with h | h
    · exact (by decide : (2 : Fin 4) ≠ 3) h
    · exact (by decide : (2 : Fin 4) ≠ 3 + 1) h

end Puzzling139335.N5
