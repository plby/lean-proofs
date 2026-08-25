import StackExchange.Puzzling139335.N5.StrictFrame.Placement.Form
import StackExchange.Puzzling139335.N5.SideExclusion.Normalized

/-!
# Actual placement formulas for the strict five-incidence frame

The imported predicate abbreviates only the two exact affine coordinate
formulas. All support inequalities and strict coordinate bounds are proved
from containment of the actual placed tile in the square.
-/

open Set

namespace Puzzling139335.N5

/-- Every actual placement of the normalized prototype into the
singleton-corner tile has this frame, with the initial nonstrict bounds
derived from the actual third corner and the base endpoints. -/
theorem Normalized.corner_frame_exists {d : SquareDissection} (h : Normalized d)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2) :
    0 < e.symm (corner 2) 1 ∧ ∃ c s : ℝ,
      c ^ 2 + s ^ 2 = 1 ∧ 0 ≤ s ∧ s ≤ c ∧ 0 < c ∧
      s * e.symm (corner 2) 0 ≤ c * e.symm (corner 2) 1 ∧
      c * (1 - e.symm (corner 2) 0) ≤ s * e.symm (corner 2) 1 ∧
      CornerPlacementForm e (e.symm (corner 2)) c s := by
  obtain ⟨hC, hCA, hCB⟩ := h.third_corner_preimage e he
  have hefit : e '' d.piece 0 ⊆ unitSquare := by
    rw [he]
    exact d.piece_subset 2
  exact cornerFrame_of_placement (d.piece_subset 0) h.below_diagonal
    h.bottom_left h.bottom_right hC hCA hCB e hefit (e.apply_symm_apply _)

/-- The image of the actual bottom-left endpoint lies strictly off the
bottom and left sides. In either row order this makes the frame's first
support value strictly less than one. -/
theorem Normalized.frame_sum_lt_one {d : SquareDissection} (h : Normalized d)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2)
    {C : Plane} {c s : ℝ} (hf : CornerPlacementForm e C c s) :
    c * C 0 + s * C 1 < 1 := by
  have hA : e (corner 0) ∈ d.piece 2 := by
    rw [← he]
    exact mem_image_of_mem e h.bottom_left
  exact hf.frame_sum_lt_one_of_origin_image_pos (h.piece_two_coordinates_pos hA)

end Puzzling139335.N5
