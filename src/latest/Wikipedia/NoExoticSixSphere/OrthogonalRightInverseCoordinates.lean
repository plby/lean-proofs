import Wikipedia.NoExoticSixSphere.CanonicalRightInverse

/-!
# Exact change of target coordinates for the canonical normal frame

A linear target coordinate change does not change the differential's
kernel. Uniqueness of the orthogonal right inverse therefore gives an
exact frame-comparison formula, without an isometry assumption.
-/

namespace NoExoticSixSphere

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

theorem orthogonalRightInverse_target_coordinates (D : E →L[ℝ] F)
    (hD : Function.Surjective D) (A : F ≃L[ℝ] G) :
    orthogonalRightInverse (A.toContinuousLinearMap.comp D) =
      (orthogonalRightInverse D).comp A.symm.toContinuousLinearMap := by
  have hk : (A.toContinuousLinearMap.comp D).ker = D.ker := by
    ext v
    change A (D v) = 0 ↔ D v = 0
    constructor
    · intro h
      apply A.injective
      simpa only [map_zero] using h
    · intro h
      rw [h, map_zero]
  apply orthogonalRightInverse_eq_of_rightInverse _ (A.surjective.comp hD)
  · intro v
    change A (D (orthogonalRightInverse D (A.symm v))) = v
    rw [apply_orthogonalRightInverse D hD, ContinuousLinearEquiv.apply_symm_apply]
  · rintro _ ⟨v, rfl⟩
    rw [hk, ← range_orthogonalRightInverse D hD]
    exact ⟨A.symm v, rfl⟩

end NoExoticSixSphere
