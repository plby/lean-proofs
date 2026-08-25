import StackExchange.Puzzling139335.N5.AxisFaces
import StackExchange.Puzzling139335.N5.SideExclusion.Normalized

/-!
# Actual remaining-piece placements have nonzero top-normal coordinates
-/

open Set

namespace Puzzling139335.N5

open PlaneIsometries

/-- No remaining-piece placement has an axis-aligned top normal.  The
strict endpoint bounds are derived from the proved side exclusions. -/
theorem Normalized.remaining_top_row_nonzero {d : SquareDissection}
    (h : Normalized d) {i : Fin 4} (hi : i = 2 ∨ i = 3)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece i) :
    linearMatrix e 1 0 ≠ 0 ∧ linearMatrix e 1 1 ≠ 0 := by
  have hzero : (0 : Plane) ∈ d.piece 0 := by
    have hcorner : corner 0 = (0 : Plane) := by
      apply plane_ext <;> norm_num [corner, Fin.ext_iff]
    exact hcorner ▸ h.bottom_left
  have hA : e 0 ∈ d.piece i := he ▸ mem_image_of_mem e hzero
  have hB : e (corner 1) ∈ d.piece i := he ▸ mem_image_of_mem e h.bottom_right
  have hApos := h.remaining_coordinates_pos hi hA
  have hBpos := h.remaining_coordinates_pos hi hB
  exact top_row_nonzero_of_positive_unit_base e
    (d.piece_subset i hA) (d.piece_subset i hB)
    hApos.1 hApos.2 hBpos.1 hBpos.2

/-- The corner-free placement case used in the final face split. -/
theorem Normalized.fourth_top_row_nonzero {d : SquareDissection}
    (h : Normalized d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 3) :
    linearMatrix e 1 0 ≠ 0 ∧ linearMatrix e 1 1 ≠ 0 :=
  h.remaining_top_row_nonzero (Or.inr rfl) e he

end Puzzling139335.N5
