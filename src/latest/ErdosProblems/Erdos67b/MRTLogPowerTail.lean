import ErdosProblems.Erdos67b.MRTLogPowerEnergy

/-! # Paying the full far tail for all permitted partial short lengths -/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

theorem mrtWeighted_partialLength_tail_le
    {W c H h : ℝ} (hW : 1 ≤ W) (hc : 0 < c) (hc1 : c ≤ 1) (hH : 0 < H)
    (hceq : c = W ^ 10 / H) (hh : H / W ^ 3 ≤ h) :
    W ^ 6 * (c⁻¹ + Real.pi / c ^ 2) / h ^ 2 ≤ (1 + Real.pi) / W ^ 8 := by
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hh0 : 0 < h := (div_pos hH (pow_pos hW0 3)).trans_le hh
  have hprod : W ^ 7 ≤ c * h := by
    calc
      _ = (W ^ 10 / H) * (H / W ^ 3) := by field_simp
      _ ≤ (W ^ 10 / H) * h := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by rw [hceq]
  have hsq : W ^ 14 ≤ c ^ 2 * h ^ 2 := by
    have hs := pow_le_pow_left₀ (pow_nonneg hW0.le 7) hprod 2
    simpa only [mul_pow, ← pow_mul] using hs
  have hinv : c⁻¹ ≤ 1 / c ^ 2 := by
    calc
      _ = c / c ^ 2 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hc1 (sq_nonneg c)
  have hbase : (c⁻¹ + Real.pi / c ^ 2) / h ^ 2 ≤ (1 + Real.pi) / W ^ 14 := by
    calc
      _ ≤ (1 / c ^ 2 + Real.pi / c ^ 2) / h ^ 2 :=
        div_le_div_of_nonneg_right (add_le_add hinv (le_refl _)) (sq_nonneg h)
      _ = (1 + Real.pi) / (c ^ 2 * h ^ 2) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (pow_pos hW0 14) hsq
  calc
    _ = W ^ 6 * ((c⁻¹ + Real.pi / c ^ 2) / h ^ 2) := by ring
    _ ≤ W ^ 6 * ((1 + Real.pi) / W ^ 14) :=
      mul_le_mul_of_nonneg_left hbase (pow_nonneg hW0.le 6)
    _ = _ := by field_simp

theorem mrtLogPower_partialLength_tail_le {L h : ℝ} (hL : 1 ≤ L)
    (hc1 : mrtLogPowerCutoff L ≤ 1)
    (hh : Real.exp L / mrtLogPowerWindow L ^ 3 ≤ h) :
    mrtLogPowerWindow L ^ 6 *
        ((mrtLogPowerCutoff L)⁻¹ + Real.pi / mrtLogPowerCutoff L ^ 2) / h ^ 2 ≤
      (1 + Real.pi) / mrtLogPowerWindow L ^ 8 := by
  exact mrtWeighted_partialLength_tail_le (mrtLogPowerWindow_one_le hL)
    (mrtLogPowerCutoff_pos L) hc1 (Real.exp_pos L) (mrtLogPowerCutoff_eq L) hh

theorem mrtTendsto_logPower_tail_budget :
    Tendsto (fun L : ℝ ↦ (1 + Real.pi) / mrtLogPowerWindow L ^ 8) atTop (𝓝 0) := by
  have hh := (mrtTendsto_exp_neg_mul_log (by norm_num : (0 : ℝ) < 8192)).const_mul (1 + Real.pi)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [] with L
  rw [mrtLogPowerWindow_pow, div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  norm_num

end

end Erdos67b
