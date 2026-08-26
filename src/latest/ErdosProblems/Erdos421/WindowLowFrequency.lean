import ErdosProblems.Erdos421.SchwartzWindowMultiplier

/-! # The low-frequency contribution to a smooth-window variance -/

namespace Erdos421

open Complex MeasureTheory FourierTransform
open scoped SchwartzMap

theorem integral_symmetric_square_le_of_linear_bound {D W : ℝ → ℂ} {K U : ℝ}
    (hD : Continuous D) (hW : Continuous W) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (hDbound : ∀ t : ℝ, ‖D t‖ ≤ 1) (hWbound : ∀ t : ℝ, ‖W t‖ ≤ K * |t|) :
    (∫ t in -U..U, ‖D t‖ ^ 2 * ‖W t‖ ^ 2) ≤ 2 * K ^ 2 * U ^ 3 := by
  have hcont : Continuous (fun t : ℝ ↦ ‖D t‖ ^ 2 * ‖W t‖ ^ 2) :=
    (hD.norm.pow 2).mul (hW.norm.pow 2)
  have hbound : ∀ t ∈ Set.Icc (-U) U, ‖D t‖ ^ 2 * ‖W t‖ ^ 2 ≤ (K * U) ^ 2 := by
    intro t ht
    have habs : |t| ≤ U := abs_le.mpr ht
    have hw := (hWbound t).trans (mul_le_mul_of_nonneg_left habs hK)
    have hwsq := pow_le_pow_left₀ (norm_nonneg (W t)) hw 2
    have hdsq : ‖D t‖ ^ 2 ≤ 1 := by nlinarith [hDbound t, norm_nonneg (D t)]
    nlinarith [sq_nonneg (‖W t‖)]
  have hb := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -U ≤ U)
    (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hbound
  rw [intervalIntegral.integral_const, smul_eq_mul] at hb
  exact hb.trans_eq (by ring)

theorem windowMultiplier_low_frequency_bound (φ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hC : 0 < C) (hnorm : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C)
    (hdecay : ∀ t : ℝ, |t| * ‖𝓕 φ t‖ ≤ C)
    (hlip : ∀ s t : ℝ, ‖𝓕 φ s - 𝓕 φ t‖ ≤ C * |s - t|)
    {δ ρ U : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hU : 0 ≤ U)
    {D : ℝ → ℂ} (hD : Continuous D) (hDbound : ∀ t : ℝ, ‖D t‖ ≤ 1) :
    (∫ t in -U..U, ‖D t‖ ^ 2 * ‖windowMultiplier φ δ ρ t‖ ^ 2) ≤
      2 * (C * ρ / (2 * Real.pi)) ^ 2 * U ^ 3 := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  apply integral_symmetric_square_le_of_linear_bound hD
    (windowMultiplier_continuous φ δ ρ) (by positivity) hU hDbound
  intro t
  have hb := (windowMultiplier_bounds φ hC hnorm hdecay hlip hδ hδρ t).1
  convert hb using 1
  ring

end Erdos421
