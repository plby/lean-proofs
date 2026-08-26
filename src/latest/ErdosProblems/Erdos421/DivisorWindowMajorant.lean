import ErdosProblems.Erdos421.DivisorWindowLogBounds

/-! # A logarithmic majorant for the actual type-I mean square -/

namespace Erdos421

open MeasureTheory FourierTransform
open scoped SchwartzMap

theorem weighted_divisor_window_log_majorant (φ : 𝓢(ℝ, ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (hφ₁ : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C / (1 + |t|))
    (hφ₂ : ∀ t : ℝ, |t| ^ 2 * ‖𝓕 φ t‖ ≤ C)
    (S : Finset ℕ) (a : ℕ → ℂ) {X M : ℕ} (hX : 0 < X) (hM : 0 < M)
    (hlog : 1 ≤ Real.log X) (hMX : M ≤ X)
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M) (ha : ∀ m ∈ S, ‖a m‖ ≤ 1)
    {Y u v : ℝ} (hY : 1 ≤ Y) (huv : u ≤ v) (hlen : v - u ≤ X) :
    (∫ x in u..v, ‖∑ m ∈ S, a m * (additiveDivisorWindow φ Y x m -
      (m : ℂ)⁻¹ * (∫ z : ℝ, φ z))‖ ^ 2) ≤
        32 * C ^ 2 * ((X : ℝ) + 512 * M ^ 2 * Real.log X) * (Real.log X) ^ 3 / Y +
        8 * C ^ 2 / (X : ℝ) ^ 3 := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hMR : (M : ℝ) ≤ X := by exact_mod_cast hMX
  have hYpos : 0 < Y := by linarith
  have hL : 0 ≤ Real.log X := by linarith
  have hH : 0 < X ^ 4 := pow_pos hX 4
  have hfull := weighted_divisor_window_mean_square φ hC hφ₁ hφ₂ S a hM hH hS ha hYpos huv
  simp only [Nat.cast_pow] at hfull
  have hfreq := divisor_window_frequency_log_le hX1 hlog hMR
  have hpref : v - u + 16 * (M : ℝ) ^ 2 * Real.log (4 * Real.pi * (X : ℝ) ^ 4 * M ^ 2 + 2) ≤
      (X : ℝ) + 512 * M ^ 2 * Real.log X := by
    have hb := mul_le_mul_of_nonneg_left hfreq (by positivity : 0 ≤ 16 * (M : ℝ) ^ 2)
    nlinarith
  have hpref0 : 0 ≤ (X : ℝ) + 512 * M ^ 2 * Real.log X := by positivity
  have hh0 : (0 : ℝ) ≤ harmonic M := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  have hh := pow_le_pow_left₀ hh0 (divisor_window_harmonic_le hlog hMR) 3
  have henergy : 2 * C ^ 2 * (harmonic M : ℝ) ^ 3 / Y ≤ 2 * C ^ 2 * (2 * Real.log X) ^ 3 / Y :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity)) hYpos.le
  have hfirst : 2 * ((v - u + 16 * (M : ℝ) ^ 2 *
      Real.log (4 * Real.pi * (X : ℝ) ^ 4 * M ^ 2 + 2)) *
      (2 * C ^ 2 * (harmonic M : ℝ) ^ 3 / Y)) ≤
      32 * C ^ 2 * ((X : ℝ) + 512 * M ^ 2 * Real.log X) * (Real.log X) ^ 3 / Y := by
    calc
      _ ≤ 2 * (((X : ℝ) + 512 * M ^ 2 * Real.log X) *
          (2 * C ^ 2 * (2 * Real.log X) ^ 3 / Y)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hpref henergy (by positivity) hpref0) (by norm_num)
      _ = _ := by ring
  have hM2 : (M : ℝ) ^ 2 ≤ (X : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg M) hMR 2
  have hden : (X : ℝ) ^ 4 ≤ Y ^ 2 * (X : ℝ) ^ 4 := by
    have hY2 : (1 : ℝ) ≤ Y ^ 2 := one_le_pow₀ hY
    nlinarith [pow_nonneg hXR.le 4]
  have herror : 2 * C * (M : ℝ) ^ 2 / (Y ^ 2 * (X : ℝ) ^ 4) ≤ 2 * C / (X : ℝ) ^ 2 := by
    calc
      _ ≤ 2 * C * (M : ℝ) ^ 2 / (X : ℝ) ^ 4 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ 2 * C * (X : ℝ) ^ 2 / (X : ℝ) ^ 4 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM2 (by positivity)) (by positivity)
      _ = _ := by field_simp
  have herror2 := pow_le_pow_left₀ (by positivity) herror 2
  have htail : 2 * (v - u) * (2 * C * (M : ℝ) ^ 2 / (Y ^ 2 * (X : ℝ) ^ 4)) ^ 2 ≤
      8 * C ^ 2 / (X : ℝ) ^ 3 := by
    calc
      _ ≤ 2 * (X : ℝ) * (2 * C / (X : ℝ) ^ 2) ^ 2 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hlen (by norm_num)) herror2
          (sq_nonneg _) (by positivity)
      _ = _ := by field_simp; ring
  exact hfull.trans (add_le_add hfirst htail)

end Erdos421
