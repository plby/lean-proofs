/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Linear representations of correlated Gaussian pairs.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianPairBoundary

namespace Erdos521

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix InnerProductSpace

theorem standardGaussian_matrix_map_mean (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (∫ x, x ∂((stdGaussian (EuclideanSpace ℝ (Fin 2))).map (Matrix.toEuclideanCLM (𝕜 := ℝ) M))) = 0 := by
  rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
    integral_id_stdGaussian, map_zero]

theorem standardGaussian_matrix_map_covariance (M : Matrix (Fin 2) (Fin 2) ℝ)
    (u v : EuclideanSpace ℝ (Fin 2)) :
    covarianceBilin ((stdGaussian (EuclideanSpace ℝ (Fin 2))).map (Matrix.toEuclideanCLM (𝕜 := ℝ) M)) u v =
      u ⬝ᵥ (M * M.conjTranspose) *ᵥ v := by
  have hstar : (Matrix.toEuclideanCLM (𝕜 := ℝ) M).adjoint = Matrix.toEuclideanCLM (𝕜 := ℝ) M.conjTranspose :=
    (map_star (Matrix.toEuclideanCLM (𝕜 := ℝ)) M).symm
  rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian, innerSL_apply_apply,
    ContinuousLinearMap.adjoint_inner_left, hstar, ← ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.mul_def, ← map_mul, Matrix.inner_toEuclideanCLM]

noncomputable def pairGaussianMatrix (ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; ρ, Real.sqrt (1 - ρ ^ 2)]

theorem pairGaussianMatrix_gram {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) :
    pairGaussianMatrix ρ * (pairGaussianMatrix ρ).conjTranspose = pairCovariance ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairGaussianMatrix, pairCovariance, Matrix.mul_apply, Fin.sum_univ_two]
  nlinarith [Real.sq_sqrt (sub_nonneg.mpr hρ)]

theorem standardGaussian_map_pairGaussianMatrix {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin 2))).map (Matrix.toEuclideanCLM (𝕜 := ℝ) (pairGaussianMatrix ρ)) =
      gaussianPair ρ := by
  apply IsGaussian.ext
  · simp only [id]
    rw [standardGaussian_matrix_map_mean, gaussianPair_mean]
  · ext u v
    rw [standardGaussian_matrix_map_covariance, pairGaussianMatrix_gram hρ,
      gaussianPair, covarianceBilin_multivariateGaussian (pairCovariance_posSemidef hρ)]

theorem pairGaussianMatrix_apply (ρ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (pairGaussianMatrix ρ) x = !₂[x 0, ρ * x 0 + Real.sqrt (1 - ρ ^ 2) * x 1] := by
  ext i
  change ((pairGaussianMatrix ρ) *ᵥ WithLp.ofLp x) i = _
  fin_cases i <;> simp [pairGaussianMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem gaussianPair_signFlip_eq_standard {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) :
    gaussianPair ρ pairSignFlip = (stdGaussian (EuclideanSpace ℝ (Fin 2)))
      {x | x 0 * (ρ * x 0 + Real.sqrt (1 - ρ ^ 2) * x 1) < 0} := by
  rw [← standardGaussian_map_pairGaussianMatrix hρ,
    Measure.map_apply (by fun_prop) pairSignFlip_measurableSet]
  congr 1
  ext x
  simp [pairSignFlip, pairGaussianMatrix_apply]

end Erdos521
