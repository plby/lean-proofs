import ErdosProblems.Erdos421.ZetaLogDerivativeStrip
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Size and stability of the proved zero-free width -/

namespace Erdos421

open Filter Topology

theorem logPowerZeroWidth_tendsto_zero :
    Tendsto logPowerZeroWidth atTop (𝓝 0) := by
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 15 / 16)).comp
    Real.tendsto_log_atTop
  exact h.const_div_atTop (((2 : ℝ) ^ 44)⁻¹)

theorem logPowerZeroWidth_le_one {T : ℝ} (hlog : 1 ≤ Real.log T) :
    logPowerZeroWidth T ≤ 1 := by
  have hp : 1 ≤ (Real.log T) ^ (15 / 16 : ℝ) := Real.one_le_rpow hlog (by norm_num)
  have hc : ((2 : ℝ) ^ 44)⁻¹ ≤ 1 := by norm_num
  unfold logPowerZeroWidth
  exact (div_le_self (by positivity) hp).trans hc

theorem logPowerZeroWidth_half_le_shifted {T R : ℝ} (hT : 3 ≤ T)
    (hlog : 1 ≤ Real.log T) (hR : 0 ≤ R) (hR1 : R ≤ 1) :
    logPowerZeroWidth T / 2 ≤ logPowerZeroWidth (T + R) := by
  have hTp : 0 < T := by linarith
  have hlogp : 0 < Real.log T := by linarith
  have hTR : 1 < T + R := by linarith
  have hlogTR : 0 < Real.log (T + R) := Real.log_pos hTR
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogupper : Real.log (T + R) ≤ 2 * Real.log T := by
    have h := Real.log_le_log (by linarith : 0 < T + R) (by linarith : T + R ≤ 2 * T)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTp.ne'] at h
    linarith
  have hp : (Real.log (T + R)) ^ (15 / 16 : ℝ) ≤
      2 * (Real.log T) ^ (15 / 16 : ℝ) := by
    calc
      _ ≤ (2 * Real.log T) ^ (15 / 16 : ℝ) :=
        Real.rpow_le_rpow hlogTR.le hlogupper (by norm_num)
      _ = (2 : ℝ) ^ (15 / 16 : ℝ) * (Real.log T) ^ (15 / 16 : ℝ) :=
        Real.mul_rpow (by norm_num) hlogp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (by positivity)
  have hb := div_le_div_of_nonneg_left (by positivity : 0 ≤ ((2 : ℝ) ^ 44)⁻¹)
    (Real.rpow_pos_of_pos hlogTR _) hp
  unfold logPowerZeroWidth
  convert! hb using 1
  ring

theorem logPowerZeroWidth_reciprocal_bound {T : ℝ} (hlog : 1 ≤ Real.log T) :
    1 + 1 / (logPowerZeroWidth T / 64) ≤
      (1 + 64 * (2 : ℝ) ^ 44) * Real.log T := by
  have hpow : (Real.log T) ^ (15 / 16 : ℝ) ≤ Real.log T :=
    Real.rpow_le_self_of_one_le hlog (by norm_num)
  have he : 1 + 1 / (logPowerZeroWidth T / 64) =
      1 + (64 * (2 : ℝ) ^ 44) * (Real.log T) ^ (15 / 16 : ℝ) := by
    unfold logPowerZeroWidth
    rw [one_div_div, div_div_eq_mul_div, div_inv_eq_mul]
    ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 64 * (2 : ℝ) ^ 44)
  nlinarith only [hm, hlog]

end Erdos421
