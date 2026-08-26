import ErdosProblems.Erdos421.SchwartzWindowMultiplier

/-! # Arbitrarily high polynomial decay of a smooth-window multiplier -/

namespace Erdos421

open Complex FourierTransform
open scoped SchwartzMap

theorem windowMultiplier_decay_bound (φ : 𝓢(ℝ, ℂ)) (k : ℕ) {C : ℝ}
    (hdecay : ∀ t : ℝ, |t| ^ k * ‖𝓕 φ t‖ ≤ C)
    {δ ρ t : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (ht : t ≠ 0) :
    ‖windowMultiplier φ δ ρ t‖ ≤ 2 * C * ((2 * Real.pi) / δ) ^ k / |t| ^ k := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hρ : 0 < ρ := hδ.trans_le hδρ
  let x : ℝ := t / (2 * Real.pi)
  have hxp : 0 < |x| := abs_pos.mpr (div_ne_zero ht hpi.ne')
  have hden : 0 < (δ * |x|) ^ k := pow_pos (mul_pos hδ hxp) k
  have hd : ‖𝓕 φ (δ * x)‖ ≤ C / (δ * |x|) ^ k := by
    apply (le_div_iff₀ hden).mpr
    have h := hdecay (δ * x)
    rw [abs_mul, abs_of_pos hδ] at h
    nlinarith
  have hr : ‖𝓕 φ (ρ * x)‖ ≤ C / (δ * |x|) ^ k := by
    apply (le_div_iff₀ hden).mpr
    have h := hdecay (ρ * x)
    rw [abs_mul, abs_of_pos hρ] at h
    have hp : (δ * |x|) ^ k ≤ (ρ * |x|) ^ k := by gcongr
    have hm := mul_le_mul_of_nonneg_right hp (norm_nonneg (𝓕 φ (ρ * x)))
    nlinarith
  have hb := (norm_sub_le (𝓕 φ (δ * x)) (𝓕 φ (ρ * x))).trans (add_le_add hd hr)
  have he : C / (δ * |x|) ^ k + C / (δ * |x|) ^ k =
      2 * C * ((2 * Real.pi) / δ) ^ k / |t| ^ k := by
    dsimp only [x]
    rw [abs_div, abs_of_pos hpi, mul_pow, div_pow, div_pow]
    field_simp
    ring
  exact hb.trans_eq he

theorem windowMultiplier_inverse_scale_decay (φ : 𝓢(ℝ, ℂ)) (k : ℕ) {C : ℝ}
    (hdecay : ∀ t : ℝ, |t| ^ k * ‖𝓕 φ t‖ ≤ C)
    {R ρ t : ℝ} (hR : 0 < R) (hρ : 4 * Real.pi / R ≤ ρ) (ht : t ≠ 0) :
    ‖windowMultiplier φ (4 * Real.pi / R) ρ t‖ ≤ 2 * C * (R / 2) ^ k / |t| ^ k := by
  have hδ : 0 < 4 * Real.pi / R := by positivity
  have hb := windowMultiplier_decay_bound φ k hdecay hδ hρ ht
  have he : (2 * Real.pi) / (4 * Real.pi / R) = R / 2 := by
    have hpi := Real.pi_ne_zero
    field_simp
    ring
  rwa [he] at hb

end Erdos421
