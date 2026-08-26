import ErdosProblems.Erdos67b.MRTLogPowerRounding
import ErdosProblems.Erdos67b.MRTMajorArcBudget

/-! # Vanishing minor-arc budgets with the actual integer auxiliary window -/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

theorem mrtLogPowerNat_budget_le {L : ℝ} (hL : 1 ≤ L)
    (hW : 2 ≤ mrtLogPowerWindow L) :
    L ^ 5 / (mrtLogPowerNatWindow L : ℝ) ≤ 2 * Real.exp (-1019 * Real.log L) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hWpos := mrtLogPowerWindow_pos L
  have hfloor := (mrtLogPowerNatWindow_bounds hW).2.1
  calc
    _ ≤ L ^ 5 / (mrtLogPowerWindow L / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfloor
    _ = 2 * (L ^ 5 / mrtLogPowerWindow L) := by field_simp
    _ = _ := by
      have hpow : L ^ (5 : ℕ) = Real.exp ((5 : ℝ) * Real.log L) := by
        rw [show (5 : ℝ) = (5 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hLpos]
      rw [hpow, mrtLogPowerWindow, ← Real.exp_sub]
      congr 2
      ring

theorem mrtTendsto_logPowerNat_budget :
    Tendsto (fun L : ℝ ↦ L ^ 5 / (mrtLogPowerNatWindow L : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun L : ℝ ↦ 2 * Real.exp (-1019 * Real.log L)) atTop (𝓝 0) := by
    simpa using (mrtTendsto_exp_neg_mul_log (by norm_num : (0 : ℝ) < 1019)).const_mul 2
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ),
      mrtTendsto_logPower_window.eventually (eventually_ge_atTop 2)] with L hL hW
    exact mrtLogPowerNat_budget_le hL hW

theorem mrtLogPowerNat_inv_pow_le {L : ℝ} (hW : 2 ≤ mrtLogPowerWindow L) (k : ℕ) :
    1 / (mrtLogPowerNatWindow L : ℝ) ^ k ≤ 2 ^ k * (1 / mrtLogPowerWindow L ^ k) := by
  have hWpos := mrtLogPowerWindow_pos L
  have hfloor := (mrtLogPowerNatWindow_bounds hW).2.1
  calc
    _ ≤ 1 / (mrtLogPowerWindow L / 2) ^ k :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ (by positivity) hfloor k)
    _ = _ := by rw [div_pow]; field_simp

theorem mrtTendsto_logPowerNat_inv_pow {k : ℕ} (hk : 0 < k) :
    Tendsto (fun L : ℝ ↦ 1 / (mrtLogPowerNatWindow L : ℝ) ^ k) atTop (𝓝 0) := by
  have hlim : Tendsto (fun L : ℝ ↦ 2 ^ k * (1 / mrtLogPowerWindow L ^ k)) atTop (𝓝 0) := by
    simpa using (mrtTendsto_logPower_inv_pow hk).const_mul (2 ^ k)
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall fun _ ↦ by positivity
  · filter_upwards [mrtTendsto_logPower_window.eventually (eventually_ge_atTop 2)] with L hW
    exact mrtLogPowerNat_inv_pow_le hW k

theorem mrtEventually_minorArc_budgets (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧ 2 ≤ mrtLogPowerWindow L ∧
      C * L ^ 5 / (mrtLogPowerNatWindow L : ℝ) ≤ (ε / 2) ^ 4 ∧
      12 / (mrtLogPowerNatWindow L : ℝ) ^ 200 ≤ ε / 2 := by
  have hmain : Tendsto (fun L : ℝ ↦ C * L ^ 5 / (mrtLogPowerNatWindow L : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, ← mul_div_assoc] using mrtTendsto_logPowerNat_budget.const_mul C
  have herror : Tendsto (fun L : ℝ ↦ 12 / (mrtLogPowerNatWindow L : ℝ) ^ 200)
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (mrtTendsto_logPowerNat_inv_pow (by norm_num : 0 < 200)).const_mul 12
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    mrtTendsto_logPower_window.eventually (eventually_ge_atTop 2),
    hmain.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < (ε / 2) ^ 4)),
    herror.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))]
    with L hL hW hmain herror
  exact ⟨hL, hW, hmain.le, herror.le⟩

end

end Erdos67b
