import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureConjugation

/-! # Norm control and exponential equivariance for symplectic skew conjugation -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.OrthogonalPaths Exponential

variable {n : ℕ}

theorem norm_conjugateSkew_le (a : symplecticSubgroup n) (K : SkewSpace n) :
    ‖conjugateSkew a K‖ ≤ ‖K‖ := by
  change ‖a.val.val.val.comp (K.val.comp (a⁻¹).val.val.val)‖ ≤ ‖K.val‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg K.val)
  intro x
  change ‖a.val.val.val (K.val ((a⁻¹).val.val.val x))‖ ≤ ‖K.val‖ * ‖x‖
  rw [a.val.property]
  have h := K.val.le_opNorm ((a⁻¹).val.val.val x)
  rwa [(a⁻¹).val.property] at h

local instance conjugationNormedAlgebraRat :
    NormedAlgebra ℚ (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :=
  NormedAlgebra.restrictScalars ℚ ℝ (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))

theorem exp_conjugateSkew (a : symplecticSubgroup n) (K : SkewSpace n) :
    exp (conjugateSkew a K) = a * exp K * a⁻¹ := by
  have hs : SemiconjBy a.val.val.val K.val (conjugateSkew a K).val := by
    apply ContinuousLinearMap.ext
    intro x
    change a.val.val.val (K.val x) =
      a.val.val.val (K.val ((inverse a.val).val.val (a.val.val.val x)))
    rw [inverse_apply_self]
  have he : a * exp K = exp (conjugateSkew a K) * a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hs.exp_right
  calc
    exp (conjugateSkew a K) = exp (conjugateSkew a K) * a * a⁻¹ :=
      (mul_inv_cancel_right _ _).symm
    _ = (a * exp K) * a⁻¹ := congrArg (fun b : symplecticSubgroup n ↦ b * a⁻¹) he.symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures
