import ErdosProblems.Erdos421.DivisorWindowCoefficientScaling
import ErdosProblems.Erdos421.PowerLogComparison

/-! # Full divisor-window savings for sieve-sized coefficients -/

namespace Erdos421

open MeasureTheory FourierTransform Filter Topology
open scoped SchwartzMap

theorem weighted_divisor_window_subpower_log_saving (φ : 𝓢(ℝ, ℂ)) {Q : ℝ} (hQ : 0 < Q)
    (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ (S : Finset ℕ) (a : ℕ → ℂ) (M : ℕ),
      0 < M → (M : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      (∀ m ∈ S, 0 < m ∧ m ≤ M) →
      (∀ m ∈ S, ‖a m‖ ≤ Q * (m : ℝ) ^ (1 / 100 : ℝ)) →
      ∀ (Y u v : ℝ), (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y → u ≤ v → v - u ≤ X →
      (∫ x in u..v, ‖∑ m ∈ S, a m * (additiveDivisorWindow φ Y x m -
        (m : ℂ)⁻¹ * (∫ z : ℝ, φ z))‖ ^ 2) ≤ ε * X / (Real.log X) ^ A := by
  obtain ⟨C, hC, hφ₁, hφ₂⟩ := exists_divisor_window_fourier_bounds φ
  have hsmall := eventually_power_log_saving
    (by positivity : 0 < 20000 * C ^ 2 * Q ^ 2)
    (by norm_num : (0 : ℝ) < 3 / 100) hε A 4
  have hlogs : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 1, hlogs, hsmall] with X hX hlog hsmallX
  intro S a M hM hMX hS ha Y u v hY huv hlen
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hMX' : M ≤ X := by
    exact_mod_cast hMX.trans (Real.rpow_le_self_of_one_le hX1 (by norm_num))
  have hK : 0 < Q * (X : ℝ) ^ (1 / 100 : ℝ) := by positivity
  have haK : ∀ m ∈ S, ‖a m‖ ≤ Q * (X : ℝ) ^ (1 / 100 : ℝ) := by
    intro m hm
    apply (ha m hm).trans
    apply mul_le_mul_of_nonneg_left _ hQ.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast (hS m hm).2.trans hMX')
      (by norm_num)
  have hb := weighted_divisor_window_power_bound_scaled φ hC.le hφ₁ hφ₂ S a hX hM hlog hMX
    hS hK haK hY huv hlen
  have hpow : ((X : ℝ) ^ (1 / 100 : ℝ)) ^ 2 * (X : ℝ) ^ (19 / 20 : ℝ) =
      (X : ℝ) ^ (1 - 3 / 100 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hXp, ← Real.rpow_add hXp]
    norm_num
  apply hb.trans
  calc
    _ = (20000 * C ^ 2 * Q ^ 2) *
        (((X : ℝ) ^ (1 / 100 : ℝ)) ^ 2 * (X : ℝ) ^ (19 / 20 : ℝ)) *
          (Real.log X) ^ (4 : ℕ) := by ring
    _ = (20000 * C ^ 2 * Q ^ 2) * (X : ℝ) ^ (1 - 3 / 100 : ℝ) *
        (Real.log X) ^ (4 : ℝ) := by rw [hpow]; norm_num
    _ ≤ _ := hsmallX

end Erdos421
