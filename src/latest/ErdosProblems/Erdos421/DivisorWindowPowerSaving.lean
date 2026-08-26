import ErdosProblems.Erdos421.DivisorWindowPowerParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Arbitrary logarithmic savings for the full type-I window -/

namespace Erdos421

open MeasureTheory FourierTransform Filter Topology
open scoped SchwartzMap

theorem weighted_divisor_window_power_bound (φ : 𝓢(ℝ, ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (hφ₁ : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C / (1 + |t|))
    (hφ₂ : ∀ t : ℝ, |t| ^ 2 * ‖𝓕 φ t‖ ≤ C)
    (S : Finset ℕ) (a : ℕ → ℂ) {X M : ℕ} (hX : 0 < X) (hM : 0 < M)
    (hlog : 1 ≤ Real.log X) (hMX : (M : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ))
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M) (ha : ∀ m ∈ S, ‖a m‖ ≤ 1)
    {Y u v : ℝ} (hY : (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y) (huv : u ≤ v) (hlen : v - u ≤ X) :
    (∫ x in u..v, ‖∑ m ∈ S, a m * (additiveDivisorWindow φ Y x m -
      (m : ℂ)⁻¹ * (∫ z : ℝ, φ z))‖ ^ 2) ≤
      20000 * C ^ 2 * (X : ℝ) ^ (19 / 20 : ℝ) * (Real.log X) ^ 4 := by
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hMX' : M ≤ X := by
    exact_mod_cast hMX.trans (Real.rpow_le_self_of_one_le hX1 (by norm_num))
  have hY1 : 1 ≤ Y := (Real.one_le_rpow hX1 (by norm_num : (0 : ℝ) ≤ 1 / 10)).trans hY
  exact (weighted_divisor_window_log_majorant φ hC hφ₁ hφ₂ S a hX hM hlog hMX' hS ha hY1
    huv hlen).trans (divisor_window_majorant_power_bound hX1 hlog (Nat.cast_nonneg M) hMX hY)

/-- Unconditional, uniform mean-square savings for arbitrary bounded weights
on divisors up to `X^(21/40)`, with additive window length at least `X^(1/10)`. -/
theorem weighted_divisor_window_log_saving (φ : 𝓢(ℝ, ℂ)) (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ (S : Finset ℕ) (a : ℕ → ℂ) (M : ℕ),
      0 < M → (M : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      (∀ m ∈ S, 0 < m ∧ m ≤ M) → (∀ m ∈ S, ‖a m‖ ≤ 1) →
      ∀ (Y u v : ℝ), (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y → u ≤ v → v - u ≤ X →
      (∫ x in u..v, ‖∑ m ∈ S, a m * (additiveDivisorWindow φ Y x m -
        (m : ℂ)⁻¹ * (∫ z : ℝ, φ z))‖ ^ 2) ≤ ε * X / (Real.log X) ^ A := by
  obtain ⟨C, hC, hφ₁, hφ₂⟩ := exists_divisor_window_fourier_bounds φ
  have hconst : 0 < 20000 * C ^ 2 := by positivity
  have hlim : Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ)) ^ (A + 4) / (X : ℝ) ^ (1 / 20 : ℝ))
      atTop (𝓝 0) :=
    ((isLittleO_log_rpow_rpow_atTop (A + 4)
      (by norm_num : (0 : ℝ) < 1 / 20)).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  have hlogs : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 1, hlogs,
    hlim.eventually (gt_mem_nhds (div_pos hε hconst))] with X hX hlog hsmall
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hLp : 0 < Real.log X := by linarith
  have hQ : 0 < (X : ℝ) ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hXp _
  have hs : 20000 * C ^ 2 * (Real.log X) ^ (A + 4) ≤ ε * (X : ℝ) ^ (1 / 20 : ℝ) := by
    simpa only [mul_comm] using (div_le_div_iff₀ hQ hconst).mp hsmall.le
  have hLex : (Real.log X) ^ (A + 4) = (Real.log X) ^ A * (Real.log X) ^ (4 : ℕ) := by
    rw [Real.rpow_add hLp]
    norm_num
  have hXP : (X : ℝ) ^ (19 / 20 : ℝ) * (X : ℝ) ^ (1 / 20 : ℝ) = X := by
    rw [← Real.rpow_add hXp]
    norm_num
  have hmajor : 20000 * C ^ 2 * (X : ℝ) ^ (19 / 20 : ℝ) * (Real.log X) ^ (4 : ℕ) ≤
      ε * X / (Real.log X) ^ A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hLp A)).mpr
    calc
      _ = (X : ℝ) ^ (19 / 20 : ℝ) * (20000 * C ^ 2 * (Real.log X) ^ (A + 4)) := by
        rw [hLex]
        ring
      _ ≤ (X : ℝ) ^ (19 / 20 : ℝ) * (ε * (X : ℝ) ^ (1 / 20 : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hXp.le _)
      _ = ε * X := by
        rw [show (X : ℝ) ^ (19 / 20 : ℝ) * (ε * (X : ℝ) ^ (1 / 20 : ℝ)) =
          ε * ((X : ℝ) ^ (19 / 20 : ℝ) * (X : ℝ) ^ (1 / 20 : ℝ)) by ring, hXP]
  intro S a M hM hMX hS ha Y u v hY huv hlen
  exact (weighted_divisor_window_power_bound φ hC.le hφ₁ hφ₂ S a hX hM hlog hMX hS ha hY
    huv hlen).trans hmajor

end Erdos421
