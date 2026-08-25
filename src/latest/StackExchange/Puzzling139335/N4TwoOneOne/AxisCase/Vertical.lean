import StackExchange.Puzzling139335.N4TwoOneOne.TopGap
import StackExchange.Puzzling139335.RectangularHull.AxisSegment

/-!
# A vertical image of the source base is impossible

The fourth piece rises to the top midpoint, while the source joins the bottom
corners below height one half. The height barrier therefore forbids any bottom
contact by the cornerless fourth piece. A vertical unit image of the two
source endpoints would force exactly such a contact.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

open PlaneIsometries

variable {d : SquareDissection} {θ u v : ℝ}

theorem fourth_no_bottom_contact (hcfg : Configuration d) (h : SourceData d θ u v)
    {p : Plane} (hp : p ∈ d.piece 3) (hpy : p 1 = 0) : False := by
  have hfit := d.piece_subset 3 hp
  have hx0 : p 0 ≠ 0 := by
    intro hx
    have heq : p = corner 0 := by
      apply plane_ext
      · simpa [corner] using hx
      · simpa [corner] using hpy
    exact hcfg.cornerless 0 (heq ▸ hp)
  have hx1 : p 0 ≠ 1 := by
    intro hx
    have heq : p = corner 1 := by
      apply plane_ext
      · simpa [corner] using hx
      · simpa [corner] using hpy
    exact hcfg.cornerless 1 (heq ▸ hp)
  have hbottom : Schoenflies.Plane.mk (p 0) 0 ∈ d.piece 3 := by
    have heq : p = Schoenflies.Plane.mk (p 0) 0 := plane_ext rfl hpy
    exact heq ▸ hp
  apply RectangularHull.bottom_contact_above_height_impossible
    (d.jordan 0) (d.jordan 3) (d.piece_subset 0) (d.piece_subset 3)
    (d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 3))
    (by simpa [corner, Schoenflies.Plane.mk] using h.bottom_left)
    (by simpa [corner, Schoenflies.Plane.mk] using h.bottom_right)
    (fun q hq => h.height_le_half hq)
    ⟨!₂[(1 / 2 : ℝ), 1], h.top_midpoint_mem hcfg, by norm_num⟩
    (lt_of_le_of_ne hfit.1.1 (Ne.symm hx0))
    (lt_of_le_of_ne hfit.1.2 hx1) hbottom

/-- An actual copy of the source in piece three cannot send its unit base
to the vertical direction. No hull assumption is used. -/
theorem vertical_axis_image_false (hcfg : Configuration d) (h : SourceData d θ u v)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (hAxis : linearMatrix e 0 0 = 0) : False := by
  have hA : e !₂[0, 0] ∈ d.piece 3 := by
    rw [← he]
    apply mem_image_of_mem
    simpa [corner] using h.bottom_left
  have hB : e !₂[1, 0] ∈ d.piece 3 := by
    rw [← he]
    apply mem_image_of_mem
    simpa [corner] using h.bottom_right
  have hAfit := d.piece_subset 3 hA
  have hBfit := d.piece_subset 3 hB
  have hunit : linearMatrix e 0 0 ^ 2 + linearMatrix e 1 0 ^ 2 = 1 := by
    simpa [pow_two] using linearMatrix_column_dot e 0 0
  have hlen : ((e !₂[1, 0]) 1 - (e !₂[0, 0]) 1) ^ 2 = 1 := by
    rw [RectangularHull.affine_unit_base_coordinate_difference e 1]
    simpa [hAxis] using hunit
  rcases endpoints_of_mem_Icc_of_sub_sq_eq_one hBfit.2 hAfit.2 hlen with
    ⟨hBzero, _hAone⟩ | ⟨_hBone, hAzero⟩
  · exact fourth_no_bottom_contact hcfg h hB hBzero
  · exact fourth_no_bottom_contact hcfg h hA hAzero

end Puzzling139335.N4TwoOneOne
