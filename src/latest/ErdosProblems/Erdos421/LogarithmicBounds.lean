import ErdosProblems.Erdos421.LogarithmicSecondDerivative

/-! # Small- and large-frequency bounds for logarithmic sums -/

namespace Erdos421

theorem secondDerivative_scale_algebra {M B s : ℝ} (hM : 0 < M)
    (hBM : B ≤ 3 * M) (hs1 : 1 ≤ s) (hsM : s ≤ M) :
    (s ^ 2 / M + 3) * (2 + 14 * B / s) ≤ 160 * (s + M / s) := by
  have hs : 0 < s := by linarith
  have h1 := mul_le_mul_of_nonneg_right hBM (sq_nonneg s)
  have h2 := mul_le_mul_of_nonneg_left hBM hM.le
  have h3 := mul_le_mul_of_nonneg_right hsM (sq_nonneg s)
  have h4 : M * s ≤ M * s ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith : s ≤ s ^ 2) hM.le
  apply (mul_le_mul_iff_right₀ (mul_pos hM hs)).mp
  have hleft : (M * s) * ((s ^ 2 / M + 3) * (2 + 14 * B / s)) =
      2 * s ^ 3 + 6 * M * s + 14 * B * s ^ 2 + 42 * M * B := by
    field_simp
    ring
  have hright : (M * s) * (160 * (s + M / s)) = 160 * M * s ^ 2 + 160 * M ^ 2 := by
    field_simp
  rw [hleft, hright]
  nlinarith [sq_nonneg M, mul_nonneg hM.le (sq_nonneg s)]

theorem logarithmicSum_norm_le (M N : ℕ) (τ : ℝ) : ‖logarithmicSum M N τ‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖oscillatoryPhase (Real.log (M + n : ℕ)) τ‖ := norm_sum_le _ _
    _ = _ := by simp

theorem logarithmicSum_large_frequency_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    {τ : ℝ} (hτM : (M : ℝ) ≤ τ) :
    ‖logarithmicSum M N τ‖ ≤ 160 * (Real.sqrt τ + M / Real.sqrt τ) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN' : (N : ℝ) ≤ M := by exact_mod_cast hN
  have hτ : 0 < τ := hM'.trans_le hτM
  let s := Real.sqrt τ
  have hs : 0 < s := Real.sqrt_pos.mpr hτ
  have hsq : s ^ 2 = τ := Real.sq_sqrt hτ.le
  by_cases hτsq : τ ≤ (M : ℝ) ^ 2
  · let B := (M + N + 1 : ℝ)
    have hB : 0 < B := by dsimp only [B]; positivity
    have hBM : B ≤ 3 * M := by dsimp only [B]; linarith
    have hs1 : 1 ≤ s := by nlinarith
    have hsM : s ≤ M := by nlinarith
    let K := ⌈τ / M⌉₊
    have hK : (K : ℝ) + 2 ≤ τ / M + 3 := by
      have h := Nat.ceil_lt_add_one (div_nonneg hτ.le hM'.le)
      dsimp only [K]
      linarith
    have h := logarithmicSum_spacing_bound hM N hτ (div_pos hs hB)
    change ‖logarithmicSum M N τ‖ ≤
      ((K : ℝ) + 2) * (2 + 12 / (s / B) + 2 * (s / B) * B ^ 2 / τ) at h
    have hpart : 2 * (s / B) * B ^ 2 / τ = 2 * B / s := by
      calc
        _ = 2 * B * s / τ := by field_simp
        _ = 2 * B / s := by rw [← hsq]; field_simp
    have heq : 2 + 12 / (s / B) + 2 * (s / B) * B ^ 2 / τ = 2 + 14 * B / s := by
      rw [div_div_eq_mul_div, hpart]
      ring
    rw [heq] at h
    have hbound := h.trans (mul_le_mul_of_nonneg_right hK (by positivity))
    have hscale := secondDerivative_scale_algebra hM' hBM hs1 hsM
    rw [hsq] at hscale
    exact hbound.trans hscale
  · have hMs : (M : ℝ) ≤ s := by nlinarith
    have hnorm := (logarithmicSum_norm_le M N τ).trans (hN'.trans hMs)
    have hdiv : 0 ≤ (M : ℝ) / s := by positivity
    change ‖logarithmicSum M N τ‖ ≤ 160 * (s + M / s)
    nlinarith

/-- The unweighted kernel bound used for Gram-row large-value estimates. -/
theorem logarithmicSum_positive_frequency_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    {τ : ℝ} (hτ : 0 < τ) :
    ‖logarithmicSum M N τ‖ ≤ 320 * ((M : ℝ) / τ + Real.sqrt τ) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN' : (N : ℝ) ≤ M := by exact_mod_cast hN
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hsq := Real.sq_sqrt hτ.le
  by_cases hτM : τ ≤ M
  · have h := logarithmicSum_small_frequency_bound hM N hτ hτM
    have hB : (M + N + 1 : ℝ) ≤ 3 * M := by linarith
    have hupper : 8 * (M + N + 1 : ℝ) / τ ≤ 24 * ((M : ℝ) / τ) := by
      calc
        _ ≤ 8 * (3 * (M : ℝ)) / τ :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 8)) hτ.le
        _ = _ := by ring
    have hnorm := h.trans hupper
    have hdiv : 0 ≤ (M : ℝ) / τ := by positivity
    nlinarith
  · have h := logarithmicSum_large_frequency_bound hM hN (le_of_not_ge hτM)
    have hdiv : (M : ℝ) / Real.sqrt τ ≤ Real.sqrt τ := by
      apply (div_le_iff₀ hs).mpr
      nlinarith
    have hpos : 0 ≤ (M : ℝ) / τ := by positivity
    nlinarith

theorem oscillatoryPhase_neg_time (ω t : ℝ) :
    oscillatoryPhase ω (-t) = starRingEnd ℂ (oscillatoryPhase ω t) := by
  simp only [oscillatoryPhase, Complex.ofReal_neg, ← Complex.exp_conj, map_mul,
    Complex.conj_I, Complex.conj_ofReal]
  congr 1
  ring

theorem logarithmicSum_neg (M N : ℕ) (τ : ℝ) :
    logarithmicSum M N (-τ) = starRingEnd ℂ (logarithmicSum M N τ) := by
  simp only [logarithmicSum, oscillatoryPhase_neg_time, map_sum]

theorem logarithmicSum_nonzero_frequency_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    {τ : ℝ} (hτ : τ ≠ 0) :
    ‖logarithmicSum M N τ‖ ≤ 320 * ((M : ℝ) / |τ| + Real.sqrt |τ|) := by
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · have h := logarithmicSum_positive_frequency_bound hM hN (neg_pos.mpr hneg)
    rw [logarithmicSum_neg, Complex.norm_conj] at h
    simpa only [abs_of_neg hneg] using h
  · simpa only [abs_of_pos hpos] using logarithmicSum_positive_frequency_bound hM hN hpos

/-- A uniform kernel estimate, including zero frequency. -/
theorem logarithmicSum_kernel_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M) (τ : ℝ) :
    ‖logarithmicSum M N τ‖ ≤ 640 * ((M : ℝ) / (1 + |τ|) + Real.sqrt |τ|) := by
  have hN' : (N : ℝ) ≤ M := by exact_mod_cast hN
  have hM' : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hden : 0 < 1 + |τ| := by positivity
  have hs : 0 ≤ Real.sqrt |τ| := Real.sqrt_nonneg _
  have hpos : 0 ≤ (M : ℝ) / (1 + |τ|) := by positivity
  by_cases ht : |τ| ≤ 1
  · have hn := (logarithmicSum_norm_le M N τ).trans hN'
    have hratio : (M : ℝ) ≤ 2 * ((M : ℝ) / (1 + |τ|)) := by
      have hm : (M : ℝ) * (1 + |τ|) ≤ 2 * M := by nlinarith
      have h := (le_div_iff₀ hden).mpr hm
      simpa only [mul_div_assoc] using h
    linarith
  · have ha : 0 < |τ| := by linarith
    have hn := logarithmicSum_nonzero_frequency_bound hM hN (abs_pos.mp ha)
    have hratio : (M : ℝ) / |τ| ≤ 2 * ((M : ℝ) / (1 + |τ|)) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ ha hden).mpr
      nlinarith
    linarith

end Erdos421
