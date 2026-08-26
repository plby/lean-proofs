import ErdosProblems.Erdos421.ZetaEnvelopePower
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # A coarse uniform height bound for zeta in a fixed strip -/

namespace Erdos421

open Complex Filter Topology

theorem riemannZeta_eventually_linear_height :
    ∃ T₀ > 1, ∀ t β : ℝ, T₀ ≤ |t| → 31 / 32 ≤ β →
      ‖riemannZeta ((β : ℂ) + t * I)‖ ≤ |t| := by
  let C : ℝ := 1048640
  have hC : 0 < C := by norm_num [C]
  have ht := ((isLittleO_log_rpow_rpow_atTop (1 : ℝ)
    (by norm_num : (0 : ℝ) < 31 / 32)).tendsto_div_nhds_zero).const_mul C
  simp only [mul_zero] at ht
  have hlarge : ∀ᶠ T : ℝ in atTop, ∀ t β : ℝ, |t| = T → 31 / 32 ≤ β →
      ‖riemannZeta ((β : ℂ) + t * I)‖ ≤ T := by
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop (3 : ℝ)] with T hsave hlog hT
    intro t β htT hβ
    have hTp : 0 < T := by linarith
    have hprod : C * Real.log T ≤ T ^ (31 / 32 : ℝ) := by
      have h : C * (Real.log T / T ^ (31 / 32 : ℝ)) < 1 := by
        simpa only [Real.rpow_one] using hsave
      have hd := (div_lt_iff₀ (Real.rpow_pos_of_pos hTp (31 / 32 : ℝ))).mp
        (show C * Real.log T / T ^ (31 / 32 : ℝ) < 1 by convert h using 1; ring)
      linarith
    have hsre : 1 - (1 / 32 : ℝ) ≤ ((β : ℂ) + t * I).re := by
      simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
      linarith
    have hsim : |((β : ℂ) + t * I).im| = T := by
      simpa only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add] using htT
    have hb := riemannZeta_strip_envelope 0 8 (by norm_num) (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 1 / 32)
      (by norm_num [logarithmicSavingExponent] : (1 / 32 : ℝ) ≤ logarithmicSavingExponent 0 8 / 2)
      ((β : ℂ) + t * I) hsre (by rw [hsim]; norm_num; linarith)
      (show |((β : ℂ) + t * I).im| ≤ 2 * T + 1 / 32 by rw [hsim]; linarith)
    have he := zetaStripEnvelope_dilated_bound 0 8 (by norm_num : (0 : ℝ) ≤ 1 / 32)
      (by norm_num : (1 / 32 : ℝ) ≤ 1) hT hlog
    have he' : zetaStripEnvelope 0 8 (1 / 32) (2 * T + 1 / 32) ≤
        C * T ^ (1 / 32 : ℝ) * Real.log T := by norm_num [C] at he ⊢; exact he
    have hm := mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hTp.le (1 / 32 : ℝ))
    calc
      _ ≤ C * T ^ (1 / 32 : ℝ) * Real.log T := hb.trans he'
      _ ≤ T ^ (1 / 32 : ℝ) * T ^ (31 / 32 : ℝ) := by nlinarith only [hm]
      _ = T := by rw [← Real.rpow_add hTp]; norm_num
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max T₀ 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro t β ht hβ
  exact hT₀ |t| ((le_max_left T₀ 2).trans ht) t β rfl hβ

end Erdos421
