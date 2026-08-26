import ErdosProblems.Erdos67b.MRTLogPowerEnergy

/-! # A vanishing explicit normalized major-arc error -/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

def mrtMajorArcTypicalBudget (W H Y q : ℝ) : ℝ :=
  (1 + 2 * Real.pi * W / q) * (2 * H * Y / W ^ 2 + q * (H * Y / W ^ 3 + 2 * H + Y))

def mrtMajorArcNormalizedError (W H : ℝ) : ℝ :=
  (3 + 2 * Real.pi) / W ^ 2 + 4 * Real.pi / W + (3 + 6 * Real.pi) * W / H

theorem mrtMajorArc_budget_le_normalized {W H Y q : ℝ} (hW : 1 ≤ W) (hH : 0 < H)
    (hHY : H ≤ Y) (hq : 1 ≤ q) (hqW : q ≤ W) :
    mrtMajorArcTypicalBudget W H Y q ≤ mrtMajorArcNormalizedError W H * H * Y := by
  have hWpos : 0 < W := zero_lt_one.trans_le hW
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hYpos : 0 < Y := hH.trans_le hHY
  have hcube : q / W ^ 3 ≤ 1 / W ^ 2 := by
    calc
      _ ≤ W / W ^ 3 := div_le_div_of_nonneg_right hqW (pow_nonneg hWpos.le 3)
      _ = _ := by field_simp
  have hWY : W / Y ≤ W / H := div_le_div_of_nonneg_left hWpos.le hH hHY
  have hqY : q / Y ≤ W / H :=
    (div_le_div_of_nonneg_right hqW hYpos.le).trans hWY
  have hqH : q / H ≤ W / H := div_le_div_of_nonneg_right hqW hH.le
  have hqWmul : W ≤ q * W := by nlinarith only [hq, hWpos]
  have hphase : 4 * Real.pi / (q * W) ≤ 4 * Real.pi / W :=
    div_le_div_of_nonneg_left (by positivity) hWpos hqWmul
  have htwo := mul_le_mul_of_nonneg_left hqY (by norm_num : (0 : ℝ) ≤ 2)
  have hfour := mul_le_mul_of_nonneg_left hWY (show 0 ≤ 4 * Real.pi by positivity)
  have heq : mrtMajorArcTypicalBudget W H Y q / (H * Y) =
      2 / W ^ 2 + q / W ^ 3 + 2 * q / Y + q / H +
        4 * Real.pi / (q * W) + 2 * Real.pi / W ^ 2 +
          4 * Real.pi * W / Y + 2 * Real.pi * W / H := by
    unfold mrtMajorArcTypicalBudget
    field_simp
    ring
  have hnormalized : mrtMajorArcTypicalBudget W H Y q / (H * Y) ≤
      mrtMajorArcNormalizedError W H := by
    rw [heq]
    unfold mrtMajorArcNormalizedError
    simp only [div_eq_mul_inv] at hcube htwo hqH hphase hfour ⊢
    nlinarith only [hcube, htwo, hqH, hphase, hfour]
  have hh := (div_le_iff₀ (mul_pos hH hYpos)).1 hnormalized
  simpa only [mul_assoc] using hh

theorem mrtTendsto_logPower_inv_pow {k : ℕ} (hk : 0 < k) :
    Tendsto (fun L : ℝ ↦ 1 / mrtLogPowerWindow L ^ k) atTop (𝓝 0) := by
  have hcoef : 0 < (k : ℝ) * 1024 := mul_pos (by exact_mod_cast hk) (by norm_num)
  apply (mrtTendsto_exp_neg_mul_log hcoef).congr'
  filter_upwards [] with L
  rw [mrtLogPowerWindow_pow, one_div, ← Real.exp_neg]
  congr 1
  ring

theorem mrtTendsto_logPower_window_div_exp :
    Tendsto (fun L : ℝ ↦ mrtLogPowerWindow L / Real.exp L) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ mrtTendsto_logPower_cutoff
  · exact Filter.Eventually.of_forall fun L ↦
      div_nonneg (mrtLogPowerWindow_pos L).le (Real.exp_pos L).le
  · filter_upwards [mrtEventually_logPower_geometry] with L hL
    rw [mrtLogPowerCutoff_eq]
    apply div_le_div_of_nonneg_right _ (Real.exp_pos L).le
    simpa only [pow_one] using
      pow_le_pow_right₀ (mrtLogPowerWindow_one_le hL.1) (by norm_num : 1 ≤ 10)

theorem mrtTendsto_logPower_majorArcError :
    Tendsto (fun L : ℝ ↦ mrtMajorArcNormalizedError (mrtLogPowerWindow L) (Real.exp L))
      atTop (𝓝 0) := by
  have hh := (((mrtTendsto_logPower_inv_pow (by norm_num : 0 < 2)).const_mul
    (3 + 2 * Real.pi)).add
      ((mrtTendsto_logPower_inv_pow (by norm_num : 0 < 1)).const_mul (4 * Real.pi))).add
        (mrtTendsto_logPower_window_div_exp.const_mul (3 + 6 * Real.pi))
  simp only [mul_zero, add_zero] at hh
  convert hh using 1
  ext L
  simp only [mrtMajorArcNormalizedError, pow_one]
  ring

end

end Erdos67b
