import ErdosProblems.Erdos421.ZetaLinearHeight
import ErdosProblems.Erdos421.ZetaPrimeErrorCompact
import ErdosProblems.Erdos421.ZetaLogDerivativeBound

/-! # Pole-cancelled zeta bounds in the high part of the zero-free strip -/

namespace Erdos421

open Complex Filter Topology

theorem zetaPrimeError_eventually_linear_height :
    ∃ T₀ > 1, ∀ t β : ℝ, T₀ ≤ |t| → |β - 1| ≤ logPowerZeroWidth |t| / 64 →
      riemannZeta₁ ((β : ℂ) + t * I) ≠ 0 ∧
        ‖zetaPrimeError ((β : ℂ) + t * I)‖ ≤ 2 * |t| := by
  obtain ⟨T₁, _, hζbound⟩ := riemannZeta_eventually_linear_height
  obtain ⟨T₂, _, hderiv⟩ := riemannZeta_eventually_log_derivative_bound
  obtain ⟨T₃, _, hzero⟩ := riemannZeta_eventually_ne_zero_log_power_strip
  have ht := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).const_mul ((2 : ℝ) ^ 52)
  simp only [mul_zero] at ht
  have hlarge : ∀ᶠ T : ℝ in atTop, ∀ t β : ℝ, |t| = T →
      |β - 1| ≤ logPowerZeroWidth T / 64 →
      riemannZeta₁ ((β : ℂ) + t * I) ≠ 0 ∧
        ‖zetaPrimeError ((β : ℂ) + t * I)‖ ≤ 2 * T := by
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      logPowerZeroWidth_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2)),
      eventually_ge_atTop T₁, eventually_ge_atTop T₂, eventually_ge_atTop T₃,
      eventually_ge_atTop (2 : ℝ)] with T hsave hwidth hT₁ hT₂ hT₃ hT
    intro t β htT hβ
    have hTp : 0 < T := by linarith
    have hw : 0 < logPowerZeroWidth T := logPowerZeroWidth_pos (by linarith)
    have hβlo : 31 / 32 ≤ β := by linarith [(abs_le.mp hβ).1]
    have hβzero : 1 - logPowerZeroWidth T ≤ β := by linarith [(abs_le.mp hβ).1]
    have hζ : riemannZeta ((β : ℂ) + t * I) ≠ 0 :=
      hzero t β (by rwa [htT]) (by simpa only [← htT, logPowerZeroWidth] using hβzero)
    have hs : (β : ℂ) + t * I ≠ 1 := by
      intro heq
      have hi := congrArg Complex.im heq
      simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add, one_im] at hi
      rw [hi, abs_zero] at htT
      linarith
    have hd := hderiv t β (by rwa [htT]) (by rwa [htT])
    have hz := hζbound t β (by rwa [htT]) hβlo
    rw [htT] at hd hz
    have hlog : (2 : ℝ) ^ 52 * (Real.log T) ^ 2 ≤ T := by
      have h : (2 : ℝ) ^ 52 * ((Real.log T) ^ 2 / T) < 1 := by
        simpa only [Real.rpow_two, Real.rpow_one] using hsave
      have hm := (div_lt_iff₀ hTp).mp
        (show (2 : ℝ) ^ 52 * (Real.log T) ^ 2 / T < 1 by convert h using 1; ring)
      linarith
    refine ⟨riemannZeta₁_ne_zero_of_zeta_ne_zero hs hζ, ?_⟩
    rw [zetaPrimeError_eq hs hζ]
    exact (norm_add_le _ _).trans (by linarith)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max T₀ 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro t β ht hβ
  exact hT₀ |t| ((le_max_left T₀ 2).trans ht) t β rfl hβ

end Erdos421
