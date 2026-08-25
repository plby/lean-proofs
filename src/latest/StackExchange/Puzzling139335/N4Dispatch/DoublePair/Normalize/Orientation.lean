import StackExchange.Puzzling139335.SquareSymmetry.Eight
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Orienting a pair of opposite square sides

These statements concern actual affine isometries of the whole square.
They provide the coordinate normalization and the two possible square
symmetries taking both bottom corners away from the bottom side.
-/

open Set

namespace Puzzling139335.N4Dispatch.DoublePair.Normalize

open SquareSymmetry ReflectionSeparation

theorem pointReflection_center_apply (p : Plane) :
    AffineIsometryEquiv.pointReflection ℝ squareCenter p =
      (!₂[1 - p 0, 1 - p 1] : Plane) := by
  ext k
  fin_cases k <;>
    simp [AffineIsometryEquiv.pointReflection_apply, squareCenter,
      vsub_eq_sub, vadd_eq_add] <;> ring

theorem cornerFlip_two_eq_pointReflection :
    cornerFlip 2 = AffineIsometryEquiv.pointReflection ℝ squareCenter := by
  apply AffineIsometryEquiv.ext
  intro p
  rw [pointReflection_center_apply]
  norm_num [cornerFlipPoint, corner, Fin.ext_iff]

/-- A square symmetry taking neither bottom endpoint to either bottom
endpoint is the horizontal reflection or the central half-turn. -/
theorem eq_horizontal_or_pointReflection_of_bottom_disjoint
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' unitSquare = unitSquare)
    (h00 : e (corner 0) ≠ corner 0) (h01 : e (corner 0) ≠ corner 1)
    (h10 : e (corner 1) ≠ corner 0) (h11 : e (corner 1) ≠ corner 1) :
    e = horizontal ∨ e = AffineIsometryEquiv.pointReflection ℝ squareCenter := by
  obtain ⟨b, hform | hform⟩ :=
    coordinate_forms_of_maps_square_into_square e he.subset
  · fin_cases b
    · exact (h00 (by norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff])).elim
    · exact (h01 (by norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff])).elim
    · exact Or.inr ((AffineIsometryEquiv.ext hform).trans cornerFlip_two_eq_pointReflection)
    · exact Or.inl (AffineIsometryEquiv.ext hform)
  · fin_cases b
    · exact (h00 (by norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff])).elim
    · exact (h01 (by norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff])).elim
    · exact (h11 (by norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff])).elim
    · exact (h10 (by norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff])).elim

/-- An ordered square side can be placed on the ordered bottom side by
an actual isometry preserving the entire square. -/
theorem exists_side_normalizing_isometry (a : Fin 4) :
    ∃ f : Plane ≃ᵃⁱ[ℝ] Plane, f '' unitSquare = unitSquare ∧
      f (corner a) = corner 0 ∧ f (corner (a + 1)) = corner 1 := by
  have hzero : cornerFlip a (corner a) = corner 0 := by
    rw [cornerFlip_corner]
    ext k
    fin_cases k <;> norm_num [corner, Fin.ext_iff]
  have hnext : cornerFlip a (corner (a + 1)) = corner 1 ∨
      cornerFlip a (corner (a + 1)) = corner 3 := by
    fin_cases a <;> norm_num [cornerFlipPoint, corner, Fin.ext_iff, Fin.val_add]
  rcases hnext with hnext | hnext
  · exact ⟨cornerFlip a, cornerFlip_image_unitSquare a, hzero, hnext⟩
  · refine ⟨(cornerFlip a).trans diagonal, ?_, ?_, ?_⟩
    · calc
        ((cornerFlip a).trans diagonal) '' unitSquare =
            diagonal '' (cornerFlip a '' unitSquare) := by
          simp only [AffineIsometryEquiv.coe_trans, image_image, Function.comp_def]
        _ = unitSquare := by
          rw [cornerFlip_image_unitSquare, diagonal_image_unitSquare]
    · change diagonal (cornerFlip a (corner a)) = corner 0
      rw [hzero]
      ext k
      fin_cases k <;> norm_num [corner, Fin.ext_iff]
    · change diagonal (cornerFlip a (corner (a + 1))) = corner 1
      rw [hnext]
      ext k
      fin_cases k <;> norm_num [corner, Fin.ext_iff]

end Puzzling139335.N4Dispatch.DoublePair.Normalize
