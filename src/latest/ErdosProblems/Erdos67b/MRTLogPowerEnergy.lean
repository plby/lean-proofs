import ErdosProblems.Erdos67b.MRTLogPowerSchedule

/-! # Paying the weighted typical energy for the logarithmic MRT schedule -/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

theorem mrFirstSmallRelativeBudget_le_window_initialEnvelope
    (eta p q : ℝ) {c W : ℝ} (hW : 1 ≤ W) (_hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hweighted : c * Real.exp q ≤ W ^ 7) :
    mrFirstSmallRelativeBudget eta p q c ≤ W ^ 7 * mrFirstSmallInitialEnvelope eta p q := by
  have hWpow : 1 ≤ W ^ 7 := one_le_pow₀ hW
  have hfirst : c * Real.exp q + 1 ≤ 2 * W ^ 7 := by linarith
  have htime : c + 1 ≤ 2 * W ^ 7 := by linarith
  have hres : 12 / mrLogBlockResolution eta p q 1 =
      12 * Real.exp (Real.log q / 3 - (1 / 6 - eta) * p) := by
    rw [show 12 / mrLogBlockResolution eta p q 1 =
      12 * (1 / mrLogBlockResolution eta p q 1) by ring, mrFirstResolution_inv_eq]
  unfold mrFirstSmallRelativeBudget
  rw [hres]
  calc
    _ ≤ 2048 * Real.exp 1 * (1 + Real.pi) * (2 * W ^ 7) *
        Real.exp (Real.log q / 3 - (1 / 6 - eta) * p) +
      8192 * Real.exp 13 * (1 + Real.pi) * (2 * W ^ 7) * Real.exp (-p) +
      128 * (1 + Real.pi) * (2 * W ^ 7) *
        (12 * Real.exp (Real.log q / 3 - (1 / 6 - eta) * p) + 2 * Real.exp (-p)) := by
      gcongr
    _ = _ := by
      unfold mrFirstSmallInitialEnvelope mrFirstSmallInitialCost mrFirstSmallTailCost
      ring

/-- Explicit decaying upper bound after multiplying the relative budget by `W^6`. -/
theorem mrtLogPower_weighted_budget_le {L : ℝ} (hL : 1 ≤ L)
    (hq0 : 0 < mrtLogPowerUpper L) (hqL : mrtLogPowerUpper L ≤ L)
    (hc1 : mrtLogPowerCutoff L ≤ 1) :
    mrtLogPowerWindow L ^ 6 *
        mrFirstSmallRelativeBudget (1 / 12) (mrtLogPowerLower L)
          (mrtLogPowerUpper L) (mrtLogPowerCutoff L) ≤
      mrFirstSmallInitialCost * Real.exp (-(11263 / 3 : ℝ) * Real.log L) +
        mrFirstSmallTailCost * Real.exp (-191488 * Real.log L) := by
  have hW := mrtLogPowerWindow_one_le hL
  have hbase := mrFirstSmallRelativeBudget_le_window_initialEnvelope
    (1 / 12) (mrtLogPowerLower L) (mrtLogPowerUpper L) hW
    (mrtLogPowerCutoff_pos L).le hc1 (mrtLogPowerCutoff_mul_exp_upper L).le
  have hlog := Real.log_le_log hq0 hqL
  have hfirst : mrtLogPowerWindow L ^ 13 *
      Real.exp (Real.log (mrtLogPowerUpper L) / 3 - (1 / 6 - 1 / 12) * mrtLogPowerLower L) ≤
        Real.exp (-(11263 / 3 : ℝ) * Real.log L) := by
    rw [mrtLogPowerWindow_pow, ← Real.exp_add]
    apply Real.exp_le_exp.2
    unfold mrtLogPowerLower
    norm_num
    linarith
  have htail : mrtLogPowerWindow L ^ 13 * Real.exp (-mrtLogPowerLower L) =
      Real.exp (-191488 * Real.log L) := by
    rw [mrtLogPowerWindow_pow, ← Real.exp_add]
    unfold mrtLogPowerLower
    congr 1
    ring
  have hK : 0 ≤ mrFirstSmallInitialCost := by unfold mrFirstSmallInitialCost; positivity
  calc
    _ ≤ mrtLogPowerWindow L ^ 6 *
        (mrtLogPowerWindow L ^ 7 *
          mrFirstSmallInitialEnvelope (1 / 12) (mrtLogPowerLower L) (mrtLogPowerUpper L)) :=
      mul_le_mul_of_nonneg_left hbase (pow_nonneg (mrtLogPowerWindow_pos L).le 6)
    _ = mrFirstSmallInitialCost * (mrtLogPowerWindow L ^ 13 *
          Real.exp (Real.log (mrtLogPowerUpper L) / 3 - (1 / 6 - 1 / 12) * mrtLogPowerLower L)) +
        mrFirstSmallTailCost * (mrtLogPowerWindow L ^ 13 * Real.exp (-mrtLogPowerLower L)) := by
      unfold mrFirstSmallInitialEnvelope
      ring
    _ ≤ mrFirstSmallInitialCost * Real.exp (-(11263 / 3 : ℝ) * Real.log L) +
        mrFirstSmallTailCost * Real.exp (-191488 * Real.log L) := by
      rw [htail]
      exact add_le_add (mul_le_mul_of_nonneg_left hfirst hK) (le_refl _)

theorem mrtTendsto_exp_neg_mul_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun L : ℝ ↦ Real.exp (-a * Real.log L)) atTop (𝓝 0) := by
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Real.tendsto_log_atTop.const_mul_atTop ha)
  simpa only [Function.comp_def, neg_mul] using hh

theorem mrtTendsto_logPower_weighted_budget :
    Tendsto (fun L : ℝ ↦ mrtLogPowerWindow L ^ 6 *
      mrFirstSmallRelativeBudget (1 / 12) (mrtLogPowerLower L)
        (mrtLogPowerUpper L) (mrtLogPowerCutoff L)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun L : ℝ ↦
      mrFirstSmallInitialCost * Real.exp (-(11263 / 3 : ℝ) * Real.log L) +
        mrFirstSmallTailCost * Real.exp (-191488 * Real.log L)) atTop (𝓝 0) := by
    have hh := ((mrtTendsto_exp_neg_mul_log (by norm_num : (0 : ℝ) < 11263 / 3)).const_mul
      mrFirstSmallInitialCost).add
        ((mrtTendsto_exp_neg_mul_log (by norm_num : (0 : ℝ) < 191488)).const_mul
          mrFirstSmallTailCost)
    simpa only [mul_zero, zero_add] using hh
  apply squeeze_zero' ?_ ?_ hlim
  · exact Filter.Eventually.of_forall fun L ↦
      mul_nonneg (pow_nonneg (mrtLogPowerWindow_pos L).le 6)
        (mrFirstSmallRelativeBudget_nonneg _ _ _ (mrtLogPowerCutoff_pos L).le)
  · filter_upwards [mrtEventually_logPower_geometry,
      mrtTendsto_logPower_cutoff.eventually (gt_mem_nhds zero_lt_one)] with L hL hc
    exact mrtLogPower_weighted_budget_le hL.1
      ((Real.exp_pos 1).trans_le hL.2.2.2.2.2.2.1) hL.2.2.2.1 hc.le

end

end Erdos67b
