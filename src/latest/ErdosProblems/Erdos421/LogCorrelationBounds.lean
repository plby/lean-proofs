import ErdosProblems.Erdos421.LogDifferenceSums
import ErdosProblems.Erdos421.LogarithmicBounds

/-! # Optimized bounds for logarithmic correlations -/

namespace Erdos421

theorem logDifference_scale_algebra {M B s : ℝ} (hM : 0 < M) (hB : 0 ≤ B)
    (hBM : B ≤ 3 * M) (hs1 : 1 ≤ s) (hsM : s ≤ M) :
    (s ^ 2 / M + 3) * (2 + 12 / (s / M) + 2 * (s / M) * B ^ 3 / (M * s ^ 2)) ≤
      320 * (s + M / s) := by
  have hs : 0 < s := by linarith
  have hcube := pow_le_pow_left₀ hB hBM 3
  have hpart : 2 * B ^ 3 / (M ^ 2 * s) ≤ 54 * M / s := by
    calc
      _ ≤ 2 * (3 * M) ^ 3 / (M ^ 2 * s) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcube (by norm_num)) (by positivity)
      _ = _ := by field_simp; ring
  have hinner : 2 + 12 / (s / M) + 2 * (s / M) * B ^ 3 / (M * s ^ 2) ≤
      2 * (2 + 14 * (3 * M) / s) := by
    have heq : 2 + 12 / (s / M) + 2 * (s / M) * B ^ 3 / (M * s ^ 2) =
        2 + 12 * M / s + 2 * B ^ 3 / (M ^ 2 * s) := by field_simp
    rw [heq]
    have hq : 0 ≤ M / s := by positivity
    simp only [div_eq_mul_inv] at hpart hq ⊢
    nlinarith
  have hscale := secondDerivative_scale_algebra hM (B := 3 * M) le_rfl hs1 hsM
  calc
    _ ≤ (s ^ 2 / M + 3) * (2 * (2 + 14 * (3 * M) / s)) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 2 * ((s ^ 2 / M + 3) * (2 + 14 * (3 * M) / s)) := by ring
    _ ≤ 2 * (160 * (s + M / s)) := mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = _ := by ring

theorem logarithmicDifference_sum_norm_le (M L h : ℕ) (τ : ℝ) :
    ‖∑ n ∈ Finset.range L, oscillatoryPhase 1 (logarithmicDifferencePhase M h τ n)‖ ≤ L := by
  exact (norm_sum_le _ _).trans_eq (by simp)

theorem logarithmicDifference_sum_bound {M L h : ℕ} (hM : 0 < M) (hh : 0 < h)
    (hLH : L + h ≤ M) {τ : ℝ} (hτ : 0 < τ) :
    ‖∑ n ∈ Finset.range L, oscillatoryPhase 1 (logarithmicDifferencePhase M h τ n)‖ ≤
      320 * (Real.sqrt (τ * h / M) + M / Real.sqrt (τ * h / M)) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hhp : (0 : ℝ) < h := by exact_mod_cast hh
  have hLH' : (L + h : ℝ) ≤ M := by exact_mod_cast hLH
  have hLM : (L : ℝ) ≤ M := by linarith
  let s := Real.sqrt (τ * h / M)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hsq : s ^ 2 = τ * h / M := Real.sq_sqrt (by positivity)
  have hproduct : τ * h = M * s ^ 2 := by
    have hp := (eq_div_iff hMp.ne').mp hsq
    nlinarith
  have hquot : τ * h / (M : ℝ) ^ 2 = s ^ 2 / M := by rw [hproduct]; field_simp
  have htriv := (logarithmicDifference_sum_norm_le M L h τ).trans hLM
  change ‖∑ n ∈ Finset.range L, oscillatoryPhase 1 (logarithmicDifferencePhase M h τ n)‖ ≤
    320 * (s + M / s)
  by_cases hs1 : 1 ≤ s
  · by_cases hsM : s ≤ M
    · let B := (M + L + h + 1 : ℝ)
      let K := ⌈τ * h / (M : ℝ) ^ 2⌉₊
      have hB : 0 < B := by dsimp only [B]; positivity
      have hBM : B ≤ 3 * M := by dsimp only [B]; linarith
      have hK : (K : ℝ) + 2 ≤ s ^ 2 / M + 3 := by
        have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ τ * h / (M : ℝ) ^ 2)
        rw [hquot] at hc
        dsimp only [K]
        rw [hquot]
        linarith
      have hb := logarithmicDifference_sum_spacing_bound hM hh L hτ (div_pos hs hMp)
      change _ ≤ ((K : ℝ) + 2) *
        (2 + 12 / (s / M) + 2 * (s / M) * B ^ 3 / (τ * h)) at hb
      rw [hproduct] at hb
      exact (hb.trans (mul_le_mul_of_nonneg_right hK (by positivity))).trans
        (logDifference_scale_algebra hMp hB.le hBM hs1 hsM)
    · have hMs : (M : ℝ) ≤ s := le_of_not_ge hsM
      have hdiv : 0 ≤ (M : ℝ) / s := by positivity
      linarith
  · have hsle : s ≤ 1 := le_of_not_ge hs1
    have hdiv : (M : ℝ) ≤ M / s := (le_div_iff₀ hs).mpr (by nlinarith)
    linarith

theorem logarithmic_finiteCorrelation_bound {M N h : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (hh : 0 < h) (hhN : h ≤ N) {τ : ℝ} (hτ : 0 < τ) :
    ‖finiteCorrelation (fun n ↦ oscillatoryPhase (Real.log (M + n : ℕ)) τ) N h‖ ≤
      320 * (Real.sqrt (τ * h / M) + M / Real.sqrt (τ * h / M)) := by
  rw [logarithmic_finiteCorrelation_eq]
  exact logarithmicDifference_sum_bound hM hh (by omega) hτ

end Erdos421
