import StackExchange.Puzzling139335.N6.TwoDouble.UnitRay.Normalized.Frontier
import StackExchange.Puzzling139335.N6.TwoDouble.UnitRay.Normalized.Segment
import StackExchange.Puzzling139335.DoubleCorner.HalfGerm

/-!
# Actual unit boundary rays at a normalized double corner

A forty-five-degree region germ forces an actual straight boundary ray to
lie on one of the germ's two boundary lines.  Unit length makes an axis ray
end at an adjacent square corner; a positive diagonal ray contains the
square center.  These conclusions concern the actual boundary segment.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.UnitRay

open AcuteCorner (cone45)
open DoubleCorner (upperCone45)

private theorem eq_corner_one_of_horizontal_unit {w : Plane}
    (hnorm : ‖w‖ = 1) (hx : 0 ≤ w 0) (hy : w 1 = 0) : w = corner 1 := by
  have hsq : w 0 ^ 2 + w 1 ^ 2 = 1 := by
    calc
      _ = ‖w‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      _ = 1 := by rw [hnorm]; norm_num
  have hx1 : w 0 = 1 := by
    apply (sq_eq_sq₀ hx zero_le_one).mp
    simpa only [hy, zero_pow (by decide : 2 ≠ 0), add_zero, one_pow] using hsq
  ext i
  fin_cases i
  · simpa [corner] using hx1
  · simpa [corner] using hy

private theorem eq_corner_three_of_vertical_unit {w : Plane}
    (hnorm : ‖w‖ = 1) (hx : w 0 = 0) (hy : 0 ≤ w 1) : w = corner 3 := by
  have hsq : w 0 ^ 2 + w 1 ^ 2 = 1 := by
    calc
      _ = ‖w‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      _ = 1 := by rw [hnorm]; norm_num
  have hy1 : w 1 = 1 := by
    apply (sq_eq_sq₀ hy zero_le_one).mp
    simpa only [hx, zero_pow (by decide : 2 ≠ 0), zero_add, one_pow] using hsq
  ext i
  fin_cases i
  · simpa [corner] using hx
  · simpa [corner] using hy1

/-- The lower forty-five-degree germ gives the horizontal endpoint or
actual diagonal passage through the square center. -/
theorem unitRay_cone45_endpoint_or_center {P : Set Plane} {w : Plane}
    (hgerm : SameBoundaryGerm P cone45 0)
    (hseg : segment ℝ 0 w ⊆ frontier P) (hnorm : ‖w‖ = 1) :
    w = corner 1 ∨ squareCenter ∈ frontier P := by
  obtain ⟨t, ht, _, htf⟩ := unit_segment_germ_sample
    (DoubleCorner.frontier_germ_of_germ hgerm) hseg hnorm
  have hcoords := cone45_frontier_coordinates htf
  simp only [PiLp.smul_apply, smul_eq_mul] at hcoords
  have hx : 0 ≤ w 0 := (mul_nonneg_iff_of_pos_left ht).mp hcoords.1
  rcases hcoords.2.2 with haxis | hdiag
  · have hy : w 1 = 0 := (mul_eq_zero.mp haxis).resolve_left ht.ne'
    exact Or.inl (eq_corner_one_of_horizontal_unit hnorm hx hy)
  · have hdiag' : w 0 = w 1 := mul_left_cancel₀ ht.ne' hdiag
    exact Or.inr (center_mem_of_diagonal_unit_segment hseg hnorm hx hdiag')

/-- The upper forty-five-degree germ gives the vertical endpoint or
actual diagonal passage through the square center. -/
theorem unitRay_upperCone45_endpoint_or_center {P : Set Plane} {w : Plane}
    (hgerm : SameBoundaryGerm P upperCone45 0)
    (hseg : segment ℝ 0 w ⊆ frontier P) (hnorm : ‖w‖ = 1) :
    w = corner 3 ∨ squareCenter ∈ frontier P := by
  obtain ⟨t, ht, _, htf⟩ := unit_segment_germ_sample
    (DoubleCorner.frontier_germ_of_germ hgerm) hseg hnorm
  have hcoords := upperCone45_frontier_coordinates htf
  simp only [PiLp.smul_apply, smul_eq_mul] at hcoords
  have hx : 0 ≤ w 0 := (mul_nonneg_iff_of_pos_left ht).mp hcoords.1
  have hy : 0 ≤ w 1 := (mul_nonneg_iff_of_pos_left ht).mp hcoords.2.1
  rcases hcoords.2.2 with haxis | hdiag
  · have hx0 : w 0 = 0 := (mul_eq_zero.mp haxis).resolve_left ht.ne'
    exact Or.inl (eq_corner_three_of_vertical_unit hnorm hx0 hy)
  · have hdiag' : w 0 = w 1 := mul_left_cancel₀ ht.ne' hdiag
    exact Or.inr (center_mem_of_diagonal_unit_segment hseg hnorm hx hdiag')

/-- A normalized actual unit boundary ray at either double-corner germ
ends at an adjacent square corner or contains the square center.

No global square-containment assumption is needed: the local germ already
determines the nonnegative direction of the straight ray. -/
theorem normalized_unitRay_endpoint_or_center {P : Set Plane} {w : Plane}
    (hgerm : SameBoundaryGerm P cone45 0 ∨ SameBoundaryGerm P upperCone45 0)
    (hseg : segment ℝ 0 w ⊆ frontier P) (hnorm : ‖w‖ = 1) :
    w = corner 1 ∨ w = corner 3 ∨ squareCenter ∈ frontier P := by
  rcases hgerm with hlower | hupper
  · rcases unitRay_cone45_endpoint_or_center hlower hseg hnorm with hcorner | hcenter
    · exact Or.inl hcorner
    · exact Or.inr (Or.inr hcenter)
  · rcases unitRay_upperCone45_endpoint_or_center hupper hseg hnorm with hcorner | hcenter
    · exact Or.inr (Or.inl hcorner)
    · exact Or.inr (Or.inr hcenter)

end Puzzling139335.N6.TwoDouble.UnitRay
