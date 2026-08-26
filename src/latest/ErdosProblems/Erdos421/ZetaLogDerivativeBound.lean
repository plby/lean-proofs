import ErdosProblems.Erdos421.ZetaDerivativeEnvelope

/-! # An unconditional logarithmic-derivative bound across Re(s) = 1 -/

namespace Erdos421

open Complex Filter Topology

theorem riemannZeta_eventually_log_derivative_bound :
    ∃ T₀ > 1, ∀ t β : ℝ, T₀ ≤ |t| → |β - 1| ≤ logPowerZeroWidth |t| / 64 →
      ‖logDeriv riemannZeta ((β : ℂ) + t * I)‖ ≤ (2 : ℝ) ^ 52 * (Real.log |t|) ^ 2 := by
  obtain ⟨T₁, hT₁, hderiv⟩ := exists_riemannZeta_log_derivative_strip_bound
  have hD : 0 < polynomialLogarithmicExponent 12 / 2 :=
    div_pos (polynomialLogarithmicExponent_pos 12) (by norm_num)
  have hwidthlim := logPowerZeroWidth_tendsto_zero.div_const (8 : ℝ)
  simp only [zero_div] at hwidthlim
  have hsmall := hwidthlim.eventually (gt_mem_nhds hD)
  have hlogs : ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlarge : ∀ᶠ T : ℝ in atTop, ∀ t β : ℝ, |t| = T →
      |β - 1| ≤ logPowerZeroWidth T / 64 →
      ‖logDeriv riemannZeta ((β : ℂ) + t * I)‖ ≤ (2 : ℝ) ^ 52 * (Real.log T) ^ 2 := by
    filter_upwards [hsmall, hlogs, polynomialZetaEnvelope_log_amplitude_eventually,
      eventually_ge_atTop (3 : ℝ), eventually_ge_atTop (T₁ + 1),
      eventually_ge_atTop ((2 : ℝ) ^ (12 : ℕ) + 1)] with T hsmall hlog henv hT hTlow hfreq
    intro t β ht hβ
    let R : ℝ := logPowerZeroWidth T / 8
    let u : ℝ := logPowerZeroWidth T / 64
    let c : ℂ := ((1 + u : ℝ) : ℂ) + t * I
    let w : ℂ := ((β - (1 + u) : ℝ) : ℂ)
    have hwidth : 0 < logPowerZeroWidth T := logPowerZeroWidth_pos (by linarith)
    have hwidth1 := logPowerZeroWidth_le_one hlog
    have hR : 0 < R := by dsimp only [R]; positivity
    have hu : 0 < u := by dsimp only [u]; positivity
    have hR1 : R ≤ 1 := by dsimp only [R]; linarith
    have hA : 0 < 2 * Real.log T := by linarith
    have hc : 1 < c.re := by simp only [c, add_re, ofReal_re, mul_I_re, ofReal_im]; linarith
    have hci : |c.im| = T := by simpa only [c, add_im, ofReal_im, mul_I_im, ofReal_re,
      zero_add] using ht
    have hrwidth : R ≤ logPowerZeroWidth (T + R) := by
      have h := logPowerZeroWidth_half_le_shifted hT hlog hR.le hR1
      dsimp only [R]
      linarith
    have hexp : polynomialZetaEnvelope 12 R (2 * |c.im| + R) *
        (1 + 1 / (c.re - 1)) ≤ Real.exp (2 * Real.log T) := by
      have hcre : c.re - 1 = u := by
        simp only [c, add_re, ofReal_re, mul_I_re, ofReal_im]
        ring
      rw [hci, hcre]
      exact henv R hR.le hR1
    have hw : ‖w‖ ≤ R / 4 := by
      simp only [w, norm_real, Real.norm_eq_abs]
      obtain ⟨hl, hu'⟩ := abs_le.mp hβ
      apply abs_le.mpr
      dsimp only [R, u]
      constructor <;> linarith
    have hb := hderiv 12 c R (2 * Real.log T) (by decide) hc hR hA hsmall.le
      (by rw [hci]; linarith) (by rw [hci]; linarith)
      (by rwa [hci]) hexp w hw
    have he : c + w = (β : ℂ) + t * I := by
      dsimp only [c, w]
      push_cast
      ring
    rw [he] at hb
    exact hb.trans (log_derivative_radius_bound hlog)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max T₀ 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro t β ht hβ
  exact hT₀ |t| ((le_max_left T₀ 2).trans ht) t β rfl hβ

end Erdos421
