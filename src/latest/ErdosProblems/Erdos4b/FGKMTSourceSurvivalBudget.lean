/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBatchCount
import ErdosProblems.Erdos4b.FGKMTGeometricSurvival
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # A uniform full-ray budget for source survival errors -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def sourceSurvivalFloor (x : ℝ) : ℝ := geometricSurvival (sourceBatchCount x) / 2

theorem sourceSurvivalFloor_pos (x : ℝ) : 0 < sourceSurvivalFloor x :=
  div_pos (geometricSurvival_pos _) (by norm_num)

theorem sourceSurvivalFloor_le_half (x : ℝ) : sourceSurvivalFloor x ≤ 1 / 2 :=
  div_le_div_of_nonneg_right (geometricSurvival_le_one _) (by norm_num)

theorem sourceBatchCount_le_logloglog {x : ℝ} (hℓ : 1 ≤ Real.log (Real.log x)) :
    (sourceBatchCount x : ℝ) ≤ Real.log (Real.log (Real.log x)) := by
  have hlog : 0 ≤ Real.log (Real.log (Real.log x)) := Real.log_nonneg hℓ
  exact (Nat.floor_le (div_nonneg hlog (by linarith [one_le_log_five]))).trans
    (div_le_self hlog one_le_log_five)

theorem one_div_loglog_le_geometricSurvival {x : ℝ} (hℓ : 1 ≤ Real.log (Real.log x)) :
    1 / Real.log (Real.log x) ≤ geometricSurvival (sourceBatchCount x) := by
  have h := one_div_le_one_div_of_le
    (pow_pos (by norm_num : (0 : ℝ) < 5) (sourceBatchCount x)) (sourceBatchCount_pow_le hℓ)
  simpa only [geometricSurvival, one_div_pow] using h

theorem geometricSurvival_sourceBatchCount_lt {x : ℝ}
    (hℓ : 1 ≤ Real.log (Real.log x)) :
    geometricSurvival (sourceBatchCount x) < 5 / Real.log (Real.log x) := by
  have hℓ0 : 0 < Real.log (Real.log x) := zero_lt_one.trans_le hℓ
  have hpow := loglog_lt_sourceBatchCount_succ_pow hℓ
  rw [pow_succ] at hpow
  rw [geometricSurvival, one_div_pow]
  apply (div_lt_div_iff₀ (pow_pos (by norm_num) _) hℓ0).mpr
  simpa only [one_mul, mul_comm] using hpow

theorem source_survival_error_budget {x : ℝ} (hℓ : 1 ≤ Real.log (Real.log x))
    (hbudget : 8 * ((sourceBatchCount x : ℝ) + 1) ≤ Real.log (Real.log x)) :
    ((sourceBatchCount x : ℝ) + 1) * (2 * (1 / Real.log (Real.log x) ^ 2)) ≤
      geometricSurvival (sourceBatchCount x) / 4 := by
  have hℓ0 : 0 < Real.log (Real.log x) := zero_lt_one.trans_le hℓ
  apply le_trans _
    (div_le_div_of_nonneg_right (one_div_loglog_le_geometricSurvival hℓ) (by norm_num))
  rw [show ((sourceBatchCount x : ℝ) + 1) * (2 * (1 / Real.log (Real.log x) ^ 2)) =
    (2 * ((sourceBatchCount x : ℝ) + 1)) / Real.log (Real.log x) ^ 2 by ring]
  apply (div_le_iff₀ (sq_pos_of_pos hℓ0)).mpr
  have hid : (1 / Real.log (Real.log x) / 4) * Real.log (Real.log x) ^ 2 =
      Real.log (Real.log x) / 4 := by field_simp
  rw [hid]
  linarith

theorem eventually_source_survival_error_budget :
    ∀ᶠ x : ℝ in atTop,
      ((sourceBatchCount x : ℝ) + 1) * (2 * (1 / Real.log (Real.log x) ^ 2)) ≤
        geometricSurvival (sourceBatchCount x) / 4 := by
  have hℓ := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlog := hℓ.eventually
    (Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 16))
  filter_upwards [hlog, hℓ.eventually_ge_atTop 16] with x hx hlarge
  change 16 ≤ Real.log (Real.log x) at hlarge
  have hpos : 0 < Real.log (Real.log x) := by linarith
  have hℓ1 : 1 ≤ Real.log (Real.log x) := by linarith
  change ‖Real.log (Real.log (Real.log x))‖ ≤ (1 / 16) * ‖Real.log (Real.log x)‖ at hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at hx
  have hlogbound := (le_abs_self (Real.log (Real.log (Real.log x)))).trans hx
  have hm := sourceBatchCount_le_logloglog hℓ1
  apply source_survival_error_budget hℓ1
  linarith

end

end Erdos4b.FGKMT
