import ErdosProblems.Erdos380.LowerExponentLimits

/-! # Logarithmic cost of the explicit singleton construction -/

open Filter
open scoped Topology

namespace Erdos380

theorem lowerSmoothParameter_log_cost :
    Tendsto (fun N : ℕ => lowerSmoothParameter N * Real.log (lowerSmoothParameter N) /
      Real.log (scaleBase N : ℝ)) atTop (𝓝 1000) := by
  have hY := lowerPrimeExponent_ratio.inv₀ (by positivity : (1000 / Real.log 2 : ℝ) ≠ 0)
  simp only [inv_div] at hY
  have h := ((lowerSmoothExponent_ratio.mul hY).mul scaleBase_saddle_relation).mul
    log_lowerSmoothParameter_div_loglog_scaleBase
  have hc : (1 / Real.log 2) * (Real.log 2 / 1000) * 1000000 * 1 = (1000 : ℝ) := by
    field_simp
    norm_num
  rw [hc] at h
  apply h.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    lowerPrimeExponent_tendsto_atTop.eventually (eventually_ge_atTop 1)] with N hL hS1 hY1
  have hS : 0 < Real.log (scaleBase N : ℝ) := by linarith
  have hls := Real.log_pos hS1
  have hY0 : (lowerPrimeExponent N : ℝ) ≠ 0 := by exact_mod_cast (by omega : lowerPrimeExponent N ≠ 0)
  simp only [lowerSmoothParameter]
  field_simp

theorem log_nat_div_log_scaleBase_sq_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / Real.log (scaleBase N : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have h := scaleBase_saddle_relation.div_atTop
    (Real.tendsto_log_atTop.comp log_scaleBase_tendsto_atTop)
  apply h.congr'
  filter_upwards [log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
    with N hS
  have hp := Real.log_pos hS
  simp only [Function.comp_apply]
  field_simp

theorem lowerSmoothExponent_div_prime_sq_tendsto_zero :
    Tendsto (fun N : ℕ => (lowerSmoothExponent N : ℝ) / (lowerPrimeExponent N : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hY := lowerPrimeExponent_ratio.inv₀ (by positivity : (1000 / Real.log 2 : ℝ) ≠ 0)
  simp only [inv_div] at hY
  have h := (lowerSmoothExponent_ratio.mul (hY.pow 2)).mul log_nat_div_log_scaleBase_sq_tendsto_zero
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    lowerPrimeExponent_tendsto_atTop.eventually (eventually_ge_atTop 1)] with N hL hS hY1
  have hY0 : (lowerPrimeExponent N : ℝ) ≠ 0 := by exact_mod_cast (by omega : lowerPrimeExponent N ≠ 0)
  field_simp

theorem log_scaled_lowerPrimeExponent_ratio (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.log (c * lowerPrimeExponent N) / Real.log (Real.log N))
      atTop (𝓝 (1 / 2)) := by
  have hconst : Tendsto (fun N : ℕ => Real.log c / Real.log (Real.log N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop loglog_nat_tendsto_atTop
  have h := hconst.add log_lowerPrimeExponent_ratio
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [lowerPrimeExponent_tendsto_atTop.eventually (eventually_ge_atTop 1)] with N hY
  have hY0 : (lowerPrimeExponent N : ℝ) ≠ 0 := by exact_mod_cast (by omega : lowerPrimeExponent N ≠ 0)
  rw [Real.log_mul hc.ne' hY0]
  ring

theorem log_scaled_lowerPrimeExponent_div_log_scaleBase (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.log (c * lowerPrimeExponent N) / Real.log (scaleBase N : ℝ))
      atTop (𝓝 0) := by
  have h := (log_scaled_lowerPrimeExponent_ratio c hc).mul loglog_div_log_scaleBase_tendsto_zero
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with N hL
  have hp := Real.log_pos hL
  field_simp

theorem lowerPrimeExponent_log_budget_ratio :
    Tendsto (fun N : ℕ => Real.log (20 * lowerPrimeExponent N : ℝ) /
      Real.log (lowerSmoothParameter N)) atTop (𝓝 1) := by
  have h := (log_scaled_lowerPrimeExponent_ratio 20 (by norm_num)).div log_lowerSmoothParameter_ratio
    (by norm_num : (1 / 2 : ℝ) ≠ 0)
  rw [div_self (by norm_num : (1 / 2 : ℝ) ≠ 0)] at h
  apply h.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with N hL
  have hp := Real.log_pos hL
  simp only [Pi.div_apply]
  field_simp

theorem lowerTotalExponent_rounding_error :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) - lowerTotalExponent N * Real.log 2) /
      Real.log (scaleBase N : ℝ)) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun N : ℕ => Real.log 2 / Real.log (scaleBase N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop log_scaleBase_tendsto_atTop
  have hbounds : ∀ᶠ N : ℕ in atTop,
      0 ≤ (Real.log (N : ℝ) - lowerTotalExponent N * Real.log 2) / Real.log (scaleBase N : ℝ) ∧
      (Real.log (N : ℝ) - lowerTotalExponent N * Real.log 2) / Real.log (scaleBase N : ℝ) ≤
        Real.log 2 / Real.log (scaleBase N : ℝ) := by
    filter_upwards [log_nat_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ)),
      log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hL hS
    have hlo := Nat.floor_le (show 0 ≤ (1 / Real.log 2) * Real.log (N : ℝ) by positivity)
    have hhi := Nat.lt_floor_add_one ((1 / Real.log 2) * Real.log (N : ℝ))
    change (lowerTotalExponent N : ℝ) ≤ (1 / Real.log 2) * Real.log (N : ℝ) at hlo
    change (1 / Real.log 2) * Real.log (N : ℝ) < (lowerTotalExponent N : ℝ) + 1 at hhi
    have hlo' := mul_le_mul_of_nonneg_right hlo log_two_pos.le
    have hhi' := mul_lt_mul_of_pos_right hhi log_two_pos
    have hid : (1 / Real.log 2) * Real.log (N : ℝ) * Real.log 2 = Real.log (N : ℝ) := by field_simp
    rw [hid] at hlo' hhi'
    constructor
    · exact div_nonneg (by linarith) hS.le
    · exact div_le_div_of_nonneg_right (by linarith) hS.le
  exact squeeze_zero' (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2) hmajor

theorem lowerExponent_linear_cost :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) -
      (lowerSmoothExponent N + lowerPrimeExponent N : ℕ) * Real.log 2) /
        Real.log (scaleBase N : ℝ)) atTop (𝓝 1000) := by
  have hc : Tendsto (fun N : ℕ => (2 * Real.log 2) / Real.log (scaleBase N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop log_scaleBase_tendsto_atTop
  have h := (lowerTotalExponent_rounding_error.add (lowerPrimeExponent_ratio.mul_const (Real.log 2))).add hc
  have heq : 0 + (1000 / Real.log 2) * Real.log 2 + 0 = (1000 : ℝ) := by
    field_simp
    norm_num
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_lowerExponent_padding_le] with N hN
  rw [lowerSmoothExponent, Nat.cast_add, Nat.cast_sub hN]
  push_cast
  ring

noncomputable def lowerSingletonCost (ε : ℝ) (N : ℕ) : ℝ :=
  (Real.log (N : ℝ) - (lowerSmoothExponent N + lowerPrimeExponent N : ℕ) * Real.log 2 +
    (1 + 3 * ε) * lowerSmoothParameter N * Real.log (lowerSmoothParameter N) +
      Real.log (10 * lowerPrimeExponent N : ℝ)) / Real.log (scaleBase N : ℝ)

theorem lowerSingletonCost_tendsto (ε : ℝ) :
    Tendsto (lowerSingletonCost ε) atTop (𝓝 (2000 + 3000 * ε)) := by
  have h := (lowerExponent_linear_cost.add (lowerSmoothParameter_log_cost.const_mul (1 + 3 * ε))).add
    (log_scaled_lowerPrimeExponent_div_log_scaleBase 10 (by norm_num))
  convert h using 1
  · funext N
    dsimp [lowerSingletonCost]
    ring
  · ring_nf

end Erdos380
