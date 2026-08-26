/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The absolute first moment of a standard Gaussian.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianPair
import Mathlib.MeasureTheory.Integral.Gamma

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem standardGaussian_density (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal_def]

theorem integral_positive_gaussian_factor :
    (∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-x ^ 2 / 2)) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_one, Real.rpow_neg_one] at h
  convert h using 1
  congr 1
  funext x
  congr 2
  ring

theorem integral_standardGaussian_posPart :
    (∫ x : ℝ, x⁺ ∂gaussianReal 0 1) = (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have heq : (fun x : ℝ ↦ gaussianPDFReal 0 1 x • x⁺) =
      (Set.Ioi (0 : ℝ)).indicator (fun x ↦ (Real.sqrt (2 * Real.pi))⁻¹ *
        (x * Real.exp (-x ^ 2 / 2))) := by
    funext x
    by_cases hx : 0 < x
    · simp only [Set.indicator_apply, Set.mem_Ioi, hx, if_true, standardGaussian_density, smul_eq_mul,
        posPart_eq_self.mpr hx.le]
      ring
    · have hx₀ : x ≤ 0 := le_of_not_gt hx
      simp only [Set.indicator_apply, Set.mem_Ioi, hx, if_false, posPart_eq_zero.mpr hx₀, smul_zero]
  rw [heq, integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_positive_gaussian_factor, mul_one]

theorem integral_standardGaussian_abs :
    (∫ x : ℝ, |x| ∂gaussianReal 0 1) = 2 / Real.sqrt (2 * Real.pi) := by
  rw [integral_abs_eq_two_mul_integral_posPart_sub_integral (by
    exact IsGaussian.integrable_id : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1)),
    integral_standardGaussian_posPart, integral_id_gaussianReal, sub_zero]
  rfl

end Erdos521
