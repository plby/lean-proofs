import ErdosProblems.Erdos421.SchwartzWindowBounds

/-! # Elementary estimates for comparing additive and logarithmic windows -/

namespace Erdos421

open FourierTransform
open scoped SchwartzMap

theorem exists_schwartz_uniform_lipschitz (φ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ (∀ t : ℝ, ‖φ t‖ ≤ C) ∧
      (∀ s t : ℝ, ‖φ s - φ t‖ ≤ C * |s - t|) := by
  obtain ⟨C, hC, hnorm, _, hlip⟩ := exists_schwartz_fourier_bounds (𝓕⁻ φ)
  rw [fourier_fourierInv_eq] at hnorm hlip
  exact ⟨C, hC, hnorm, hlip⟩

theorem exp_le_one_add_two_mul_half {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    Real.exp δ ≤ 1 + 2 * δ := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-δ)) (Real.exp_pos δ).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  have hfactor : 1 ≤ (1 + 2 * δ) * (1 - δ) := by nlinarith
  apply (mul_le_mul_iff_left₀ (by linarith : 0 < 1 - δ)).mp
  calc
    _ ≤ 1 := by nlinarith
    _ ≤ _ := hfactor

theorem log_linear_remainder {r : ℝ} (hr : 1 ≤ r) :
    |Real.log r - (r - 1)| ≤ (r - 1) ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hupper := Real.log_le_sub_one_of_pos hr0
  have hlower := Real.one_sub_inv_le_log_of_pos hr0
  have hinv : r⁻¹ ≤ 1 := (inv_le_one₀ hr0).mpr hr
  have hidentity : r - 1 - (1 - r⁻¹) = (r - 1) ^ 2 * r⁻¹ := by field_simp
  rw [abs_of_nonpos (by linarith)]
  calc
    _ ≤ r - 1 - (1 - r⁻¹) := by linarith
    _ = (r - 1) ^ 2 * r⁻¹ := hidentity
    _ ≤ (r - 1) ^ 2 * 1 := mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
    _ = _ := mul_one _

theorem log_window_argument_difference {δ r : ℝ} (hδ : 0 < δ) (hr : 1 ≤ r)
    (hrδ : r ≤ 1 + 2 * δ) :
    |(-Real.log r) / δ - (1 - r) / δ| ≤ 4 * δ := by
  have hb := log_linear_remainder hr
  have hsq : (r - 1) ^ 2 ≤ 4 * δ ^ 2 := by nlinarith [sq_nonneg (2 * δ - (r - 1))]
  rw [← sub_div, abs_div, abs_of_pos hδ]
  apply (div_le_iff₀ hδ).mpr
  have he : -Real.log r - (1 - r) = -(Real.log r - (r - 1)) := by ring
  rw [he, abs_neg]
  nlinarith

theorem reciprocal_window_ratio_difference {r δ : ℝ} (hr : 1 ≤ r)
    (hrδ : r ≤ 1 + 2 * δ) : |r⁻¹ - 1| ≤ 2 * δ := by
  have hr0 : 0 < r := by linarith
  have hinv : r⁻¹ ≤ 1 := (inv_le_one₀ hr0).mpr hr
  have hid : 1 - r⁻¹ = (r - 1) / r := by field_simp
  rw [abs_of_nonpos (by linarith)]
  calc
    _ = (r - 1) / r := by linarith
    _ ≤ r - 1 := div_le_self (by linarith) hr
    _ ≤ _ := by linarith

end Erdos421
