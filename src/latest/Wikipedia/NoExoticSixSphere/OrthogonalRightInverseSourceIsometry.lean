import Wikipedia.NoExoticSixSphere.CanonicalRightInverse

/-!
# Exact ambient isometric coordinates for the canonical normal frame

Precomposing a surjective differential with a genuine linear isometry
transports its canonical orthogonal right inverse by the inverse isometry.
Both the right-inverse identity and orthogonality to the true kernel are
retained; this is an exact full-frame identity.
-/

namespace NoExoticSixSphere

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

theorem orthogonalRightInverse_source_isometry (D : E →L[ℝ] F)
    (hD : Function.Surjective D) (A : G ≃ₗᵢ[ℝ] E) :
    orthogonalRightInverse (D.comp A.toContinuousLinearEquiv.toContinuousLinearMap) =
      A.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (orthogonalRightInverse D) := by
  have hDA : Function.Surjective (D.comp A.toContinuousLinearEquiv.toContinuousLinearMap) :=
    hD.comp A.toContinuousLinearEquiv.surjective
  apply orthogonalRightInverse_eq_of_rightInverse
    (D.comp A.toContinuousLinearEquiv.toContinuousLinearMap) hDA
  · intro v
    change D (A (A.symm (orthogonalRightInverse D v))) = v
    rw [A.apply_symm_apply, apply_orthogonalRightInverse D hD]
  · rintro _ ⟨v, rfl⟩
    rw [Submodule.mem_orthogonal']
    intro u hu
    have hR : orthogonalRightInverse D v ∈ D.kerᗮ := by
      rw [← range_orthogonalRightInverse D hD]
      exact ⟨v, rfl⟩
    have hAu : A u ∈ D.ker := hu
    change inner ℝ (A.symm (orthogonalRightInverse D v)) u = 0
    rw [← A.inner_map_map, A.apply_symm_apply]
    rw [Submodule.mem_orthogonal'] at hR
    exact hR (A u) hAu

end NoExoticSixSphere
