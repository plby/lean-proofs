import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixHilbertSchmidt

/-! # Unitary invariance of the complex Frobenius norm -/

noncomputable section

open scoped Matrix.Norms.Frobenius

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem frobenius_norm_sq (A : Matrix N N ℂ) :
    ‖A‖ ^ 2 = ImaginarySymmetricMatrices.squareNorm A := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Complex.sq_norm, ImaginarySymmetricMatrices.squareNorm]

theorem squareNorm_unitary_left (U : unitary (Matrix N N ℂ)) (A : Matrix N N ℂ) :
    ImaginarySymmetricMatrices.squareNorm (U.val * A) =
      ImaginarySymmetricMatrices.squareNorm A := by
  have h := NoExoticSixSphere.HilbertSchmidt.squareNorm_left (orthogonal U) (action A)
  change NoExoticSixSphere.HilbertSchmidt.squareNorm (action U.val * action A) =
    NoExoticSixSphere.HilbertSchmidt.squareNorm (action A) at h
  rw [← action_mul, squareNorm_action, squareNorm_action] at h
  linarith

theorem squareNorm_unitary_right (U : unitary (Matrix N N ℂ)) (A : Matrix N N ℂ) :
    ImaginarySymmetricMatrices.squareNorm (A * U.val) =
      ImaginarySymmetricMatrices.squareNorm A := by
  have h := NoExoticSixSphere.HilbertSchmidt.squareNorm_right (orthogonal U) (action A)
  change NoExoticSixSphere.HilbertSchmidt.squareNorm (action A * action U.val) =
    NoExoticSixSphere.HilbertSchmidt.squareNorm (action A) at h
  rw [← action_mul, squareNorm_action, squareNorm_action] at h
  linarith

theorem frobenius_norm_unitary_left (U : unitary (Matrix N N ℂ)) (A : Matrix N N ℂ) :
    ‖U.val * A‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobenius_norm_sq, frobenius_norm_sq, squareNorm_unitary_left]

theorem frobenius_norm_unitary_right (U : unitary (Matrix N N ℂ)) (A : Matrix N N ℂ) :
    ‖A * U.val‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobenius_norm_sq, frobenius_norm_sq, squareNorm_unitary_right]

theorem frobenius_norm_conjugate (U : unitary (Matrix N N ℂ)) (A : Matrix N N ℂ) :
    ‖U.val * A * star U.val‖ = ‖A‖ := by
  change ‖U.val * A * (star U).val‖ = ‖A‖
  rw [frobenius_norm_unitary_right, frobenius_norm_unitary_left]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation
