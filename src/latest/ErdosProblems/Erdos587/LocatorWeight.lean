import ErdosProblems.Erdos587.CompactWeights

/-! A fixed one-sided locator weight with a positive Fourier zero mode. -/

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace Erdos587

lemma schwartz_fourier_zero (g : 𝓢(ℝ, ℂ)) :
    (𝓕 g : 𝓢(ℝ, ℂ)) 0 = ∫ x : ℝ, g x := by
  change 𝓕 (g : ℝ → ℂ) 0 = _
  simp [Real.fourier_real_eq]

lemma physicalSquareWeight_integral_lower :
    (1 / 16 : ℝ) ≤ (∫ x : ℝ, physicalSquareWeight x).re := by
  have hInt : Integrable (fun x : ℝ => (physicalSquareWeight x).re) :=
    physicalSquareWeight.integrable.re
  have hplateau : ∀ x ∈ Set.Icc (5 / 32 : ℝ) (7 / 32),
      (1 : ℝ) ≤ (physicalSquareWeight x).re := by
    intro x hx
    rw [physicalSquareWeight_plateau hx]
    norm_num
  have hh := setIntegral_ge_of_const_le_real measurableSet_Icc
    (isCompact_Icc.measure_lt_top.ne) hplateau hInt.integrableOn
  rw [Real.volume_real_Icc_of_le (by norm_num : (5 / 32 : ℝ) ≤ 7 / 32)] at hh
  have hreal := integral_re (𝕜 := ℂ) (μ := volume) physicalSquareWeight.integrable
  change (∫ x : ℝ, (physicalSquareWeight x).re) =
    (∫ x : ℝ, physicalSquareWeight x).re at hreal
  rw [← hreal]
  calc
    (1 / 16 : ℝ) ≤ ∫ x in Set.Icc (5 / 32 : ℝ) (7 / 32), (physicalSquareWeight x).re := by
      norm_num at hh ⊢
      exact hh
    _ ≤ ∫ x : ℝ, (physicalSquareWeight x).re := setIntegral_le_integral hInt
      (Filter.Eventually.of_forall physicalSquareWeight_nonneg)

lemma physicalSquareWeight_fourier_zero_lower :
    (1 / 16 : ℝ) ≤ ((𝓕 physicalSquareWeight : 𝓢(ℝ, ℂ)) 0).re := by
  rw [schwartz_fourier_zero]
  exact physicalSquareWeight_integral_lower

lemma physicalSquareWeight_scaled_zero_lower {σ : ℝ} (hσ : 0 ≤ σ) :
    σ / 16 ≤ (scaledFourierCoeff physicalSquareWeight σ 0).re := by
  simp only [scaledFourierCoeff, Int.cast_zero, mul_zero, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left physicalSquareWeight_fourier_zero_lower hσ

end Erdos587
