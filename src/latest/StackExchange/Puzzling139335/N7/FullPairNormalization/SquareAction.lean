import StackExchange.Puzzling139335.Transform
import StackExchange.Puzzling139335.CornerIncidence
import StackExchange.Puzzling139335.SquareSymmetry.Eight
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Square actions used in the full-pair normalization

Corner multiplicity is transported through an actual square symmetry.
The ordered images of the bottom endpoints identify the horizontal
reflection among all square symmetries.
-/

open Set

namespace Puzzling139335.N7.FullPairNormalization

open SquareSymmetry ReflectionSeparation

noncomputable section

/-- Transport the number of incident pieces at one specified corner. -/
theorem cornerTileCount_map_of_corner_image (d : SquareDissection)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' unitSquare = unitSquare)
    {a b : Fin 4} (hab : e (corner a) = corner b) :
    (d.map e he).cornerTileCount b = d.cornerTileCount a := by
  classical
  change (Finset.univ.filter fun i => corner b ∈ e '' d.piece i).card =
    (Finset.univ.filter fun i => corner a ∈ d.piece i).card
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hab]
  constructor
  · rintro ⟨p, hp, hpa⟩
    exact e.injective hpa ▸ hp
  · exact mem_image_of_mem e

/-- The ordered bottom-to-top endpoint correspondence singles out
reflection in the horizontal midline. -/
theorem eq_horizontal_of_bottom_endpoints (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hS : g '' unitSquare = unitSquare)
    (h0 : g (corner 0) = corner 3) (h1 : g (corner 1) = corner 2) :
    g = horizontal := by
  have hx0 : g (corner 0) 0 = 0 := by
    rw [h0]
    norm_num [corner, Fin.ext_iff]
  have hy0 : g (corner 0) 1 = 1 := by
    rw [h0]
    norm_num [corner, Fin.ext_iff]
  have hx1 : g (corner 1) 0 = 1 := by
    rw [h1]
    norm_num [corner, Fin.ext_iff]
  obtain ⟨b, hform | hform⟩ := coordinate_forms_of_maps_square_into_square g hS.subset
  · fin_cases b
    · simp [hform, cornerFlipPoint, corner, Fin.ext_iff] at hy0
    · simp [hform, cornerFlipPoint, corner, Fin.ext_iff] at hy0
    · simp [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx0
    · apply AffineIsometryEquiv.ext
      intro p
      exact hform p
  · fin_cases b
    · simp [hform, cornerFlipPoint, corner, Fin.ext_iff] at hy0
    · simp [hform, cornerFlipPoint, corner, Fin.ext_iff] at hy0
    · simp [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx0
    · simp [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx1

end

end Puzzling139335.N7.FullPairNormalization
