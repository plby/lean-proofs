import StackExchange.Puzzling139335.N4TwoOneOne.TopGap
import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# The incoming source face cannot align with the fourth piece's top

For this matrix row the image height is the source's `eCoord` plus a fixed
offset. Its actual top contact forces the offset to be at least one half.
All source coordinates are nonnegative, so the fourth piece lies in the upper
half of the square and cannot contain the center in its interior.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

theorem incoming_aligned_false {d : SquareDissection} {θ u v : ℝ}
    (hcfg : Configuration d) (h : SourceData d θ u v) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3)
    (h10 : PlaneIsometries.linearMatrix e 1 0 = Real.cos θ)
    (h11 : PlaneIsometries.linearMatrix e 1 1 = Real.sin θ) : False := by
  have hY (p : Plane) : (e p) 1 = eCoord θ p + (e 0) 1 := by
    simpa [h10, h11, eCoord] using
      congrArg (fun q : Plane => q 1)
        (PlaneIsometries.affine_apply_eq_matrix_coordinates e p)
  obtain ⟨q, hq, hqTop⟩ := he.symm ▸ h.top_midpoint_mem hcfg
  have hTopY : eCoord θ q + (e 0) 1 = 1 := by
    rw [← hY q, hqTop]
    rfl
  have hOffset : (1 / 2 : ℝ) ≤ (e 0) 1 := by
    linarith only [hTopY, (h.projection_bounds hq).1, h.u_le_half]
  have hUpper : d.piece 3 ⊆ horizontalBand (1 / 2) 1 := by
    intro p hp
    have hpS := d.piece_subset 3 hp
    obtain ⟨r, hr, rfl⟩ := he.symm ▸ hp
    refine ⟨hpS.1, ?_, hpS.2.2⟩
    rw [hY r]
    have hrS := d.piece_subset 0 hr
    have hE : 0 ≤ eCoord θ r :=
      add_nonneg (mul_nonneg h.cos_nonneg hrS.1.1)
        (mul_nonneg h.sin_nonneg hrS.2.1)
    linarith only [hOffset, hE]
  exact RectangularHull.center_not_in_interior_upper_half hUpper
    (h.center_piece_three hc)

end Puzzling139335.N4TwoOneOne
