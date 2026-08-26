import ErdosProblems.Erdos421.ZetaEnvelopeAsymptotics
import ErdosProblems.Erdos421.ZetaGrowthZeroExclusion

/-! # An unconditional logarithmic zero-free strip with any fixed constant

For every fixed `C`, the strip `Re(s) >= 1-C/log(abs(Im(s)))` contains no
zeros at sufficiently large height. This does not assert the stronger
Korobov--Vinogradov region or the required prime-weighted cancellation.
-/

namespace Erdos421

open Complex Filter Topology

theorem riemannZeta_eventually_ne_zero_log_strip (C : ℝ) :
    ∃ T₀ > 1, ∀ t β : ℝ, T₀ ≤ |t| → 1 - C / Real.log |t| ≤ β →
      riemannZeta ((β : ℂ) + t * I) ≠ 0 := by
  obtain ⟨B, hB, r₀, hr₀, hzero⟩ := exists_riemannZeta_growth_zero_exclusion
  let r : ℕ := ⌈4000 * C⌉₊
  let K : ℕ := 2 * r + 8
  let R : ℝ := logarithmicSavingExponent r K / 4
  have hK : 2 * r + 4 ≤ K := by dsimp only [K]; omega
  have hK8 : 8 ≤ K := by dsimp only [K]; omega
  have hD := logarithmicSavingExponent_pos r (by omega : 0 < K)
  have hDsmall := logarithmicSavingExponent_le_half r (by omega : 2 ≤ K)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hR1 : R ≤ 1 := by dsimp only [R]; linarith only [hDsmall]
  have hRD : R ≤ logarithmicSavingExponent r K / 2 := by
    dsimp only [R]
    linarith only [hD]
  have hCr : 4000 * C ≤ (r : ℝ) + 1 := by
    have hceil : 4000 * C ≤ (r : ℝ) := Nat.le_ceil _
    linarith only [hceil]
  have henv := zetaStripEnvelope_exp_bound_eventually r K hR hR1 hB.le
  have hradius := (zetaDetectionRadius_tendsto_zero r hR hB.le).eventually (gt_mem_nhds hr₀)
  have hamp := (zetaDetectionAmplitude_tendsto_atTop r hR).eventually (eventually_gt_atTop 0)
  have hlower := zetaDetectionRadius_log_lower_eventually r hR hB.le
  have hlogs : ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlarge : ∀ᶠ T : ℝ in atTop, ∀ t β : ℝ, |t| = T → 1 - C / Real.log T ≤ β →
      riemannZeta ((β : ℂ) + t * I) ≠ 0 := by
    filter_upwards [henv, hradius, hamp, hlower, hlogs,
      eventually_ge_atTop ((2 : ℝ) ^ (r + 1) + R)] with T henvT hradiusT hampT hlowerT hlogT hT
    intro t β ht hβ
    have hlogp : 0 < Real.log T := by linarith only [hlogT]
    have hwidth : C / Real.log T ≤ zetaDetectionRadius r R B T / 10 := by
      calc
        C / Real.log T = (4000 * C) / (4000 * Real.log T) := by ring
        _ ≤ ((r : ℝ) + 1) / (4000 * Real.log T) :=
          div_le_div_of_nonneg_right hCr (by positivity)
        _ ≤ _ := hlowerT
    apply hzero r K hK hK8 R (zetaDetectionAmplitude r R T) t β hR hRD hampT
    · rwa [ht]
    · exact hradiusT
    · simpa only [ht, zetaDetectionRadius] using henvT
    · change 1 - zetaDetectionRadius r R B T / 10 ≤ β
      linarith only [hwidth, hβ]
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max T₀ 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro t β ht hβ
  exact hT₀ |t| ((le_max_left T₀ 2).trans ht) t β rfl hβ

end Erdos421
