import ErdosProblems.Erdos327.Analytic.ScheduledProductBounds
import ErdosProblems.Erdos327.Analytic.PowerLogSummability

/-!
# Polynomial-log bounds for the schedule loss

The sieve schedule loses `4096 h_j²`, where the binary height `h_j` is
at most a constant times `log(j+1)`.  This file converts every
nonnegative real power of that loss into an explicit power of
`log(j+1)`.
-/

namespace Erdos327.Analytic

open Real

noncomputable section

/-- Uniform coefficient in the schedule-loss bound. -/
def scheduledLogLossConstant : ℝ :=
  16384 / log 2 ^ 2

theorem scheduledLogLossConstant_pos :
    0 < scheduledLogLossConstant := by
  unfold scheduledLogLossConstant
  positivity [log_pos (by norm_num : (1 : ℝ) < 2)]

/-- The schedule loss is at most an explicit constant times
`log(j+1)²`. -/
theorem scheduledLogLoss_le_log_sq
    {j : ℕ} (hj : 1 ≤ j) :
    scheduledLogLoss j ≤
      scheduledLogLossConstant *
        log (((j + 1 : ℕ) : ℝ)) ^ 2 := by
  have hh := sieveHeight_cast_sq_le hj
  unfold scheduledLogLoss scheduledLogLossConstant
  calc
    4096 * (sieveHeight j : ℝ) ^ 2
        ≤ 4096 *
            (4 * log (((j + 1 : ℕ) : ℝ)) ^ 2 /
              log 2 ^ 2) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = 16384 / log 2 ^ 2 *
          log (((j + 1 : ℕ) : ℝ)) ^ 2 := by ring

/-- Every nonnegative real power of the schedule loss is bounded by the
corresponding doubled logarithmic power. -/
theorem scheduledLogLoss_rpow_le_log_rpow
    {j : ℕ} {r : ℝ} (hj : 1 ≤ j) (hr : 0 ≤ r) :
    scheduledLogLoss j ^ r ≤
      scheduledLogLossConstant ^ r *
        log (((j + 1 : ℕ) : ℝ)) ^ (2 * r) := by
  have hbase0 : 0 ≤ scheduledLogLoss j :=
    (zero_le_one.trans (scheduledLogLoss_one_le j))
  have hlog0 :
      0 ≤ log (((j + 1 : ℕ) : ℝ)) :=
    log_nonneg
      (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le j)))
  have hconstant0 : 0 ≤ scheduledLogLossConstant :=
    scheduledLogLossConstant_pos.le
  calc
    scheduledLogLoss j ^ r ≤
        (scheduledLogLossConstant *
          log (((j + 1 : ℕ) : ℝ)) ^ 2) ^ r :=
      Real.rpow_le_rpow hbase0 (scheduledLogLoss_le_log_sq hj) hr
    _ = scheduledLogLossConstant ^ r *
          (log (((j + 1 : ℕ) : ℝ)) ^ 2) ^ r := by
      rw [Real.mul_rpow hconstant0 (sq_nonneg _)]
    _ = scheduledLogLossConstant ^ r *
          log (((j + 1 : ℕ) : ℝ)) ^ (2 * r) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hlog0]
      norm_num

end

end Erdos327.Analytic
