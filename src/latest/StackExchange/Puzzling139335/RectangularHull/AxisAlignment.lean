import StackExchange.Puzzling139335.RectangularHull.Frames
import StackExchange.Puzzling139335.RectangularHull.CornerGeometry

/-!
# A cornered rectangular hull follows the square's axes

This statement concerns the actual convex hull of a piece, not a chosen
orientation for an enclosing rectangle.
-/

open Set

namespace Puzzling139335.RectangularHull

def Frame.AxisAligned (R : Frame) : Prop :=
  (R.first 0 = 0 ∧ R.second 1 = 0) ∨
    (R.first 1 = 0 ∧ R.second 0 = 0)

theorem Frame.axisAligned_of_corner_mem (R : Frame)
    (hS : R.carrier ⊆ unitSquare) {j : Fin 4} (hj : corner j ∈ R.carrier) :
    R.AxisAligned := by
  have hvS : R.vertices ⊆ unitSquare := R.vertices_subset_carrier.trans hS
  have hjv : corner j ∈ R.vertices := corner_mem_of_mem_convexHull hvS hj
  simp only [Frame.vertices, mem_insert_iff, mem_singleton_iff] at hjv
  rcases hjv with hjv | hjv | hjv | hjv
  · apply orthogonal_edges_at_corner_axis j R.first_ne_zero R.second_ne_zero R.orthogonal
    · simpa only [hjv] using hvS R.first_mem_vertices
    · simpa only [hjv] using hvS R.second_mem_vertices
  · have hU : corner j + -R.first ∈ unitSquare := by
      convert hvS R.origin_mem_vertices using 1
      rw [hjv]
      abel
    have hV : corner j + R.second ∈ unitSquare := by
      simpa only [hjv] using hvS R.both_mem_vertices
    have h := orthogonal_edges_at_corner_axis j
      (neg_ne_zero.mpr R.first_ne_zero) R.second_ne_zero
      (by simp only [inner_neg_left, R.orthogonal, neg_zero]) hU hV
    simpa only [Frame.AxisAligned, PiLp.neg_apply, neg_eq_zero] using h
  · have hU : corner j + -R.first ∈ unitSquare := by
      convert hvS R.second_mem_vertices using 1
      rw [hjv]
      abel
    have hV : corner j + -R.second ∈ unitSquare := by
      convert hvS R.first_mem_vertices using 1
      rw [hjv]
      abel
    have h := orthogonal_edges_at_corner_axis j
      (neg_ne_zero.mpr R.first_ne_zero) (neg_ne_zero.mpr R.second_ne_zero)
      (by simp only [inner_neg_left, inner_neg_right, R.orthogonal, neg_zero]) hU hV
    simpa only [Frame.AxisAligned, PiLp.neg_apply, neg_eq_zero] using h
  · have hU : corner j + R.first ∈ unitSquare := by
      convert hvS R.both_mem_vertices using 1
      rw [hjv]
      abel
    have hV : corner j + -R.second ∈ unitSquare := by
      convert hvS R.origin_mem_vertices using 1
      rw [hjv]
      abel
    have h := orthogonal_edges_at_corner_axis j R.first_ne_zero
      (neg_ne_zero.mpr R.second_ne_zero)
      (by simp only [inner_neg_right, R.orthogonal, neg_zero]) hU hV
    simpa only [Frame.AxisAligned, PiLp.neg_apply, neg_eq_zero] using h

/-- A piece whose rectangular hull reaches a square corner has an
axis-aligned hull. No assumption on its boundary is used. -/
theorem Frame.axisAligned_of_piece_corner (R : Frame) {P : Set Plane}
    (hHull : convexHull ℝ P = R.carrier) (hP : P ⊆ unitSquare)
    {j : Fin 4} (hj : corner j ∈ P) : R.AxisAligned := by
  apply R.axisAligned_of_corner_mem
  · rw [← hHull]
    exact convexHull_min hP convex_unitSquare
  · exact R.subset_carrier_of_convexHull_eq hHull hj

end Puzzling139335.RectangularHull
