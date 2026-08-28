import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The normal projection between nested tangent spaces

For nested Euclidean subspaces `U ≤ V`, the orthogonal projection onto the
normal space of `U` inside `V` is the difference of their projections.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare.DiskFraming

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The difference of nested orthogonal projections is the actual normal projection. -/
theorem starProjection_orthogonal_inf_eq_sub {U V : Submodule ℝ F} (h : U ≤ V) :
    (Uᗮ ⊓ V).starProjection = V.starProjection - U.starProjection := by
  ext x
  change (Uᗮ ⊓ V).starProjection x = V.starProjection x - U.starProjection x
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · refine ⟨?_, V.sub_mem (V.starProjection_apply_mem x) (h (U.starProjection_apply_mem x))⟩
    rw [← U.ker_starProjection]
    change U.starProjection (V.starProjection x - U.starProjection x) = 0
    rw [map_sub]
    have hc : U.starProjection (V.starProjection x) = U.starProjection x :=
      congrArg (fun A : F →L[ℝ] F => A x)
        (Submodule.starProjection_comp_starProjection_of_le h)
    rw [hc, Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x), sub_self]
  · have h₁ : x - V.starProjection x ∈ (Uᗮ ⊓ V)ᗮ :=
      Submodule.orthogonal_le inf_le_right (V.sub_starProjection_mem_orthogonal x)
    have h₂ : U.starProjection x ∈ (Uᗮ ⊓ V)ᗮ :=
      Submodule.orthogonal_le inf_le_left
        (U.le_orthogonal_orthogonal (U.starProjection_apply_mem x))
    convert (Uᗮ ⊓ V)ᗮ.add_mem h₁ h₂ using 1
    abel

end Wikipedia.SmoothSixDPoincare.DiskFraming
