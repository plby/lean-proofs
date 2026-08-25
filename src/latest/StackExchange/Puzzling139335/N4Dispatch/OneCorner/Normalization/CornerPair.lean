import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Normalizing two distinct square corners

An actual square symmetry takes the first chosen corner to the bottom-left
corner and the second to either the bottom-right or the opposite corner.
-/

open Set

namespace Puzzling139335.N4Dispatch.OneCorner.Normalization

open SquareSymmetry ReflectionSeparation

/-- Two distinct corners can be normalized to `(0, 1)` or `(0, 2)` by an
affine isometry preserving the entire square. -/
theorem exists_pair_normalizing_isometry (a b : Fin 4) (hab : a ≠ b) :
    ∃ g : Plane ≃ᵃⁱ[ℝ] Plane, ∃ k : Fin 4,
      g '' unitSquare = unitSquare ∧
      g (corner a) = corner 0 ∧ g (corner b) = corner k ∧ (k = 1 ∨ k = 2) := by
  have hzero : cornerFlip a (corner a) = corner 0 := by
    rw [cornerFlip_corner]
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hother : cornerFlip a (corner b) = corner 1 ∨
      cornerFlip a (corner b) = corner 2 ∨
      cornerFlip a (corner b) = corner 3 := by
    fin_cases a <;> fin_cases b <;>
      first
      | exact (hab rfl).elim
      | norm_num [cornerFlipPoint, corner, Fin.ext_iff]
  rcases hother with hother | hother | hother
  · exact ⟨cornerFlip a, 1, cornerFlip_image_unitSquare a, hzero, hother, Or.inl rfl⟩
  · exact ⟨cornerFlip a, 2, cornerFlip_image_unitSquare a, hzero, hother, Or.inr rfl⟩
  · refine ⟨(cornerFlip a).trans diagonal, 1, ?_, ?_, ?_, Or.inl rfl⟩
    · calc
        ((cornerFlip a).trans diagonal) '' unitSquare =
            diagonal '' (cornerFlip a '' unitSquare) := by
          simp only [AffineIsometryEquiv.coe_trans, image_image, Function.comp_def]
        _ = unitSquare := by
          rw [cornerFlip_image_unitSquare, diagonal_image_unitSquare]
    · change diagonal (cornerFlip a (corner a)) = corner 0
      rw [hzero]
      ext i
      fin_cases i <;> norm_num [corner, Fin.ext_iff]
    · change diagonal (cornerFlip a (corner b)) = corner 1
      rw [hother]
      ext i
      fin_cases i <;> norm_num [corner, Fin.ext_iff]

end Puzzling139335.N4Dispatch.OneCorner.Normalization
