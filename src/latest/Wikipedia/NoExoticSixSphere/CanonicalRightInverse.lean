import Wikipedia.NoExoticSixSphere.SmoothProjection

/-!
# The orthogonal right inverse of a surjective differential

The explicit operator `D* (D D*)⁻¹` is a right inverse with range the
orthogonal complement of `ker D`. It is the unique right inverse with this
range constraint. These facts identify induced normal frames without a
choice of pointwise bases.
-/

open Function

namespace NoExoticSixSphere

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem adjoint_injective_of_surjective (D : E →L[ℝ] F) (hD : Surjective D) :
    Injective D.adjoint := by
  apply LinearMap.ker_eq_bot.mp
  rw [← D.orthogonal_range, LinearMap.range_eq_top.mpr hD]
  exact Submodule.top_orthogonal_eq_bot

noncomputable def orthogonalRightInverse (D : E →L[ℝ] F) : F →L[ℝ] E :=
  D.adjoint.comp (gramOperator D.adjoint).inverse

theorem apply_orthogonalRightInverse (D : E →L[ℝ] F) (hD : Surjective D) (v : F) :
    D (orthogonalRightInverse D v) = v := by
  have hG := gramOperator_isInvertible D.adjoint (adjoint_injective_of_surjective D hD)
  simpa only [orthogonalRightInverse, ContinuousLinearMap.comp_apply,
    gramOperator, ContinuousLinearMap.adjoint_adjoint] using hG.self_apply_inverse v

theorem comp_orthogonalRightInverse (D : E →L[ℝ] F) (hD : Surjective D) :
    D.comp (orthogonalRightInverse D) = ContinuousLinearMap.id ℝ F := by
  ext v
  exact apply_orthogonalRightInverse D hD v

theorem orthogonalRightInverse_injective (D : E →L[ℝ] F) (hD : Surjective D) :
    Injective (orthogonalRightInverse D) := by
  intro u v h
  exact (apply_orthogonalRightInverse D hD u).symm.trans
    ((congrArg D h).trans (apply_orthogonalRightInverse D hD v))

theorem range_orthogonalRightInverse (D : E →L[ℝ] F) (hD : Surjective D) :
    (orthogonalRightInverse D).range = D.kerᗮ := by
  have hG := gramOperator_isInvertible D.adjoint (adjoint_injective_of_surjective D hD)
  have he : (orthogonalRightInverse D).range = D.adjoint.range := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact ⟨(gramOperator D.adjoint).inverse v, rfl⟩
    · rintro _ ⟨v, rfl⟩
      refine ⟨gramOperator D.adjoint v, ?_⟩
      change D.adjoint ((gramOperator D.adjoint).inverse (gramOperator D.adjoint v)) = _
      rw [hG.inverse_apply_self]
      rfl
  rw [he, D.orthogonal_ker]
  exact D.adjoint.range.topologicalClosure_eq_self.symm

theorem orthogonalRightInverse_eq_of_rightInverse (D : E →L[ℝ] F) (hD : Surjective D)
    (R : F →L[ℝ] E) (hR : ∀ v, D (R v) = v) (hrange : R.range ≤ D.kerᗮ) :
    orthogonalRightInverse D = R := by
  ext v
  apply sub_eq_zero.mp
  have hker : orthogonalRightInverse D v - R v ∈ D.ker := by
    change D (orthogonalRightInverse D v - R v) = 0
    rw [map_sub, apply_orthogonalRightInverse D hD, hR, sub_self]
  have horth : orthogonalRightInverse D v - R v ∈ D.kerᗮ := by
    apply Submodule.sub_mem
    · rw [← range_orthogonalRightInverse D hD]
      exact ⟨v, rfl⟩
    · exact hrange ⟨v, rfl⟩
  have hzero : orthogonalRightInverse D v - R v ∈ (⊥ : Submodule ℝ E) := by
    rw [← D.ker.inf_orthogonal_eq_bot]
    exact ⟨hker, horth⟩
  exact hzero

end NoExoticSixSphere
