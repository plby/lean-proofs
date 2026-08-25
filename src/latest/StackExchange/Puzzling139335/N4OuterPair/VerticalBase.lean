import StackExchange.Puzzling139335.N4OuterPair.Midline
import StackExchange.Puzzling139335.RectangularHull.AxisSegment

/-!
# A middle copy cannot have a vertical unit base

Such a base would have an endpoint on the bottom or top side.  The actual
height barrier has already excluded every such point of either middle piece.
-/

open Set Puzzling139335.PlaneIsometries

namespace Puzzling139335.N4OuterPair

namespace Configuration

variable {d : SquareDissection}

theorem middle_base_not_vertical (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece i)
    (hAxis : linearMatrix e 0 0 = 0) : False := by
  have hp0 : e !₂[0, 0] ∈ d.piece i :=
    he ▸ mem_image_of_mem e h.bottom_left_mk
  have hp1 : e !₂[1, 0] ∈ d.piece i :=
    he ▸ mem_image_of_mem e h.bottom_right_mk
  have hunit : linearMatrix e 0 0 ^ 2 + linearMatrix e 1 0 ^ 2 = 1 := by
    simpa [pow_two] using linearMatrix_column_dot e 0 0
  have hvertical : linearMatrix e 1 0 ^ 2 = 1 := by
    simpa [hAxis] using hunit
  have hlen : ((e !₂[1, 0]) 1 - (e !₂[0, 0]) 1) ^ 2 = 1 := by
    rw [RectangularHull.affine_unit_base_coordinate_difference]
    exact hvertical
  rcases endpoints_of_mem_Icc_of_sub_sq_eq_one
      (d.piece_subset i hp1).2 (d.piece_subset i hp0).2 hlen with hends | hends
  · exact (ne_of_gt (h.middle_y_pos hc hi hp1)) hends.1
  · exact (ne_of_lt (h.middle_y_lt_one hc hi hp1)) hends.1

end Configuration

end Puzzling139335.N4OuterPair
