/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Centered Gaussian pairs with unit marginal variances.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CorrelationLimits
import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace Erdos521

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix

def pairCovariance (ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, ρ; ρ, 1]

theorem pairCovariance_posSemidef {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) :
    (pairCovariance ρ).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · change (pairCovariance ρ).conjTranspose = pairCovariance ρ
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairCovariance]
  · intro x
    simp [pairCovariance, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 + ρ * x 1), mul_nonneg (sub_nonneg.mpr hρ) (sq_nonneg (x 1))]

noncomputable def gaussianPair (ρ : ℝ) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  multivariateGaussian 0 (pairCovariance ρ)

instance gaussianPair_isGaussian (ρ : ℝ) : IsGaussian (gaussianPair ρ) := by
  unfold gaussianPair
  infer_instance

theorem gaussianPair_mean (ρ : ℝ) : (∫ x, x ∂gaussianPair ρ) = 0 :=
  integral_id_multivariateGaussian

theorem gaussianPair_covariance {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) (t : EuclideanSpace ℝ (Fin 2)) :
    covarianceBilin (gaussianPair ρ) t t = t 0 ^ 2 + 2 * ρ * t 0 * t 1 + t 1 ^ 2 := by
  rw [gaussianPair, covarianceBilin_multivariateGaussian (pairCovariance_posSemidef hρ)]
  simp [pairCovariance, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem inverse_scale_correlation_sq_le_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (2 * Real.sqrt (a * b) / (a + b)) ^ 2 ≤ 1 := by
  rw [div_pow, mul_pow, Real.sq_sqrt (mul_pos ha hb).le]
  apply (div_le_one (by positivity : 0 < (a + b) ^ 2)).mpr
  nlinarith [sq_nonneg (a - b)]

end Erdos521
