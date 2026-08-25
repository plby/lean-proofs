import StackExchange.Puzzling139335.RectangularHull.NormalizedBands
import StackExchange.Puzzling139335.RectangularHull.Bands
import StackExchange.Puzzling139335.SquareSymmetry.CornerPermutation

/-!
# Geometric preparation for normalizing the outer bands

Square isometries preserve the absence of square corners.  Actual bottom
and top band hulls supply their extreme vertices as contacts in the pieces,
which proves the half-height bound required by `NormalizedOuterBands`.
-/

open Set

namespace Puzzling139335.RectangularHull

theorem cornerless_image_square_isometry {P : Set Plane}
    (hP : ∀ q : Fin 4, corner q ∉ P) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) :
    ∀ q : Fin 4, corner q ∉ e '' P := by
  obtain ⟨σ, hσ⟩ := SquareSymmetry.exists_corner_permutation_of_preserves_square e he
  intro q hq
  rcases hq with ⟨p, hp, heq⟩
  have hcorner : e (corner (σ.symm q)) = corner q := by
    simpa only [σ.apply_symm_apply] using hσ (σ.symm q)
  have hpeq : p = corner (σ.symm q) := e.injective (heq.trans hcorner.symm)
  exact hP (σ.symm q) (hpeq ▸ hp)

/-- Construct the normalized-band conclusions from the actual first two hulls. -/
theorem NormalizedOuterBands.of_opposite_hulls (d : SquareDissection) {h : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hbottom : convexHull ℝ (d.piece 0) = axisBox h)
    (htop : convexHull ℝ (d.piece 1) = horizontalBand (1 - h) 1)
    (hcornerless : ∀ i : Fin 4, i = 2 ∨ i = 3 → ∀ q : Fin 4, corner q ∉ d.piece i) :
    NormalizedOuterBands d h := by
  have hPV := axis_box_vertices_mem_of_hull (P := d.piece 0)
    (by norm_num : (0 : ℝ) ≤ 1) hh0.le hbottom
  have hQV := axis_box_vertices_mem_of_hull (P := d.piece 1)
    (by norm_num : (0 : ℝ) ≤ 1) (show 1 - h ≤ 1 by linarith) htop
  have hhalf : h ≤ 1 / 2 := by
    apply opposite_band_height_le_half d (by decide : (0 : Fin 4) ≠ 1) hh1
    · apply hPV
      simp [axisBoxVertices, Schoenflies.Plane.mk]
    · apply hPV
      simp [axisBoxVertices, Schoenflies.Plane.mk]
    · apply hQV
      simp [axisBoxVertices, Schoenflies.Plane.mk]
    · apply hQV
      simp [axisBoxVertices, Schoenflies.Plane.mk]
  exact ⟨hh0, hhalf, hbottom, htop, hcornerless⟩

end Puzzling139335.RectangularHull
