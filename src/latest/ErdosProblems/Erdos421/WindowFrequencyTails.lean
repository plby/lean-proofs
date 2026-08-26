import ErdosProblems.Erdos421.WindowMultiplierDecay
import ErdosProblems.Erdos421.IntegralSquareTails

/-! # Explicit tails for bounded polynomials and rapidly decaying windows -/

namespace Erdos421

open Complex MeasureTheory FourierTransform Set
open scoped SchwartzMap

theorem real_integral_Ioi_inv_square_le {f : ℝ → ℝ} {V B : ℝ} (hV : 0 < V)
    (hbound : ∀ t : ℝ, V < t → |f t| ≤ B / t ^ 2) :
    (∫ t : ℝ in Ioi V, f t) ≤ B / V := by
  have hb := norm_integral_Ioi_inv_square_le (F := fun t ↦ (f t : ℂ)) hV
    (fun t ht ↦ by simpa only [Complex.norm_real, Real.norm_eq_abs] using hbound t ht)
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs] at hb
  exact (le_abs_self _).trans hb

theorem integral_Ioi_square_product_decay_le {D W : ℝ → ℂ} {V K : ℝ}
    (hV : 0 < V) (hK : 0 ≤ K) (k : ℕ)
    (hD : ∀ t : ℝ, V < t → ‖D t‖ ≤ 1)
    (hW : ∀ t : ℝ, V < t → ‖W t‖ ≤ K / t ^ (k + 1)) :
    (∫ t : ℝ in Ioi V, ‖D t‖ ^ 2 * ‖W t‖ ^ 2) ≤ K ^ 2 / (V ^ k) ^ 2 / V := by
  apply real_integral_Ioi_inv_square_le hV
  intro t ht
  have htp : 0 < t := hV.trans ht
  have hpow : V ^ k ≤ t ^ k := pow_le_pow_left₀ hV.le ht.le k
  have hden : 0 < V ^ k * t := mul_pos (pow_pos hV k) htp
  have hratio : K / t ^ (k + 1) ≤ K / (V ^ k * t) := by
    rw [pow_succ]
    exact div_le_div_of_nonneg_left hK hden (mul_le_mul_of_nonneg_right hpow htp.le)
  have hw := pow_le_pow_left₀ (norm_nonneg (W t)) ((hW t ht).trans hratio) 2
  have hd : ‖D t‖ ^ 2 ≤ 1 := by nlinarith [hD t ht, norm_nonneg (D t)]
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  calc
    _ ≤ ‖W t‖ ^ 2 := by nlinarith [sq_nonneg (‖W t‖)]
    _ ≤ (K / (V ^ k * t)) ^ 2 := hw
    _ = _ := by rw [div_pow, mul_pow, div_div]

theorem windowMultiplier_Ioi_tail (φ : 𝓢(ℝ, ℂ)) (D : ℝ → ℂ) (k : ℕ) {C R ρ V : ℝ}
    (hC : 0 ≤ C) (hdecay : ∀ t : ℝ, |t| ^ (k + 1) * ‖𝓕 φ t‖ ≤ C)
    (hR : 0 < R) (hρ : 4 * Real.pi / R ≤ ρ) (hV : 0 < V)
    (hD : ∀ t : ℝ, ‖D t‖ ≤ 1) :
    (∫ t : ℝ in Ioi V, ‖D t‖ ^ 2 * ‖windowMultiplier φ (4 * Real.pi / R) ρ t‖ ^ 2) ≤
      (2 * C * (R / 2) ^ (k + 1)) ^ 2 / (V ^ k) ^ 2 / V := by
  apply integral_Ioi_square_product_decay_le hV (by positivity) k (fun t _ ↦ hD t)
  intro t ht
  have htp : 0 < t := hV.trans ht
  have hb := windowMultiplier_inverse_scale_decay φ (k + 1) hdecay hR hρ htp.ne'
  rwa [abs_of_pos htp] at hb

theorem windowMultiplier_Iic_tail (φ : 𝓢(ℝ, ℂ)) (D : ℝ → ℂ) (k : ℕ) {C R ρ V : ℝ}
    (hC : 0 ≤ C) (hdecay : ∀ t : ℝ, |t| ^ (k + 1) * ‖𝓕 φ t‖ ≤ C)
    (hR : 0 < R) (hρ : 4 * Real.pi / R ≤ ρ) (hV : 0 < V)
    (hD : ∀ t : ℝ, ‖D t‖ ≤ 1) :
    (∫ t : ℝ in Iic (-V), ‖D t‖ ^ 2 * ‖windowMultiplier φ (4 * Real.pi / R) ρ t‖ ^ 2) ≤
      (2 * C * (R / 2) ^ (k + 1)) ^ 2 / (V ^ k) ^ 2 / V := by
  rw [← integral_comp_neg_Ioi]
  apply integral_Ioi_square_product_decay_le hV (by positivity) k (fun t _ ↦ hD (-t))
  intro t ht
  have htp : 0 < t := hV.trans ht
  have hb := windowMultiplier_inverse_scale_decay φ (k + 1) hdecay hR hρ
    (neg_ne_zero.mpr htp.ne')
  simpa only [abs_neg, abs_of_pos htp] using hb

end Erdos421
