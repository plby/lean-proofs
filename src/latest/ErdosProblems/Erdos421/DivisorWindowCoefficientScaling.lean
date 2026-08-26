import ErdosProblems.Erdos421.DivisorWindowPowerSaving

/-! # Scaling the divisor-window estimate to nonunit coefficients -/

namespace Erdos421

open MeasureTheory FourierTransform
open scoped SchwartzMap

theorem finite_weighted_norm_square_scale (S : Finset ℕ) (a : ℕ → ℂ)
    (F : ℕ → ℂ) {K : ℝ} (hK : 0 < K) :
    ‖∑ m ∈ S, a m * F m‖ ^ 2 =
      K ^ 2 * ‖∑ m ∈ S, (a m / (K : ℂ)) * F m‖ ^ 2 := by
  have hKc : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have he : (∑ m ∈ S, a m * F m) =
      (K : ℂ) * ∑ m ∈ S, (a m / (K : ℂ)) * F m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    field_simp
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK, mul_pow]

theorem weighted_divisor_window_power_bound_scaled (φ : 𝓢(ℝ, ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (hφ₁ : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C / (1 + |t|))
    (hφ₂ : ∀ t : ℝ, |t| ^ 2 * ‖𝓕 φ t‖ ≤ C)
    (S : Finset ℕ) (a : ℕ → ℂ) {X M : ℕ} (hX : 0 < X) (hM : 0 < M)
    (hlog : 1 ≤ Real.log X) (hMX : (M : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ))
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M) {K : ℝ} (hK : 0 < K)
    (ha : ∀ m ∈ S, ‖a m‖ ≤ K)
    {Y u v : ℝ} (hY : (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y) (huv : u ≤ v) (hlen : v - u ≤ X) :
    (∫ x in u..v, ‖∑ m ∈ S, a m * (additiveDivisorWindow φ Y x m -
      (m : ℂ)⁻¹ * (∫ z : ℝ, φ z))‖ ^ 2) ≤
        K ^ 2 * (20000 * C ^ 2 * (X : ℝ) ^ (19 / 20 : ℝ) * (Real.log X) ^ 4) := by
  have hb : ∀ m ∈ S, ‖a m / (K : ℂ)‖ ≤ 1 := by
    intro m hm
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK]
    exact (div_le_one hK).mpr (ha m hm)
  have hbound := weighted_divisor_window_power_bound φ hC hφ₁ hφ₂ S
    (fun m ↦ a m / (K : ℂ)) hX hM hlog hMX hS hb hY huv hlen
  simp_rw [finite_weighted_norm_square_scale S a _ hK]
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left hbound (sq_nonneg K)

end Erdos421
