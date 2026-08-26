import ErdosProblems.Erdos327.Analytic.ProductEnvelopePowers
import ErdosProblems.Erdos327.Analytic.SieveScheduleLog
import ErdosProblems.Erdos327.Analytic.SourceGlobalAssembly
import ErdosProblems.Erdos327.Analytic.SieveScheduleErrors

/-!
# Uniform product bounds along the sieve schedule

This file combines the two Mertens cutoff orderings with the logarithmic
loss of the natural-power sieve schedule.
-/

namespace Erdos327.Analytic

open Real

noncomputable section

/-- The schedule loss appearing when powers of `log z_j` are replaced by
powers of `log X_j`. -/
def scheduledLogLoss (j : ℕ) : ℝ :=
  4096 * (sieveHeight j : ℝ) ^ 2

theorem scheduledLogLoss_one_le (j : ℕ) :
    1 ≤ scheduledLogLoss j := by
  unfold scheduledLogLoss
  have hh : (1 : ℝ) ≤ sieveHeight j := by
    exact_mod_cast sieveHeight_pos j
  nlinarith [sq_nonneg ((sieveHeight j : ℝ) - 1)]

/-- A cutoff below `8X` has logarithm at most four times `log X`. -/
theorem log_nat_div_log_nat_le_four_of_le_eight_mul
    {L X : ℕ} (hX : 2 ≤ X) (hLX : L ≤ 8 * X) :
    log (L : ℝ) / log (X : ℝ) ≤ 4 := by
  by_cases hL0 : L = 0
  · simp [hL0]
  have hlogX : 0 < log (X : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < X by omega))
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  have h8Xpos : (0 : ℝ) < ((8 * X : ℕ) : ℝ) := by positivity
  have hmono :
      log (L : ℝ) ≤ log ((8 * X : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hLpos)
      (by simpa only [Set.mem_Ioi] using h8Xpos)
      (by exact_mod_cast hLX)
  have hlog2X :
      log (2 : ℝ) ≤ log (X : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by norm_num)
      (by simpa only [Set.mem_Ioi] using (show (0 : ℝ) < X by positivity))
      (by exact_mod_cast hX)
  have hlog8 :
      log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hbound :
      log (L : ℝ) ≤ 4 * log (X : ℝ) := by
    norm_num at hmono
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0)
      (by positivity : (X : ℝ) ≠ 0), hlog8] at hmono
    nlinarith
  exact (div_le_iff₀ hlogX).2 (by nlinarith)

/-- Mixed blocks use `16X`, costing at most five powers in the elementary
logarithmic comparison. -/
theorem log_nat_div_log_nat_le_five_of_le_sixteen_mul
    {L X : ℕ} (hX : 2 ≤ X) (hLX : L ≤ 16 * X) :
    log (L : ℝ) / log (X : ℝ) ≤ 5 := by
  by_cases hL0 : L = 0
  · simp [hL0]
  have hlogX : 0 < log (X : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < X by omega))
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  have h16Xpos : (0 : ℝ) < ((16 * X : ℕ) : ℝ) := by positivity
  have hmono :
      log (L : ℝ) ≤ log ((16 * X : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hLpos)
      (by simpa only [Set.mem_Ioi] using h16Xpos)
      (by exact_mod_cast hLX)
  have hlog2X :
      log (2 : ℝ) ≤ log (X : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by norm_num)
      (by simpa only [Set.mem_Ioi] using (show (0 : ℝ) < X by positivity))
      (by exact_mod_cast hX)
  have hlog16 :
      log (16 : ℝ) = 4 * log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hbound :
      log (L : ℝ) ≤ 5 * log (X : ℝ) := by
    norm_num at hmono
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0)
      (by positivity : (X : ℝ) ≠ 0), hlog16] at hmono
    nlinarith
  exact (div_le_iff₀ hlogX).2 (by nlinarith)

/-- Constant covering both source cutoff orderings. -/
def sourceScheduledProductConstant : ℝ :=
  sourceLargeProductConstant +
    sourceSmallProductConstant * (4 : ℝ) ^ (3 / 4 : ℝ)

theorem sourceScheduledProductConstant_pos :
    0 < sourceScheduledProductConstant := by
  unfold sourceScheduledProductConstant
  positivity [sourceLargeProductConstant_pos,
    sourceSmallProductConstant_pos]

/-- Uniform source local-product bound along every dominant scheduled
block that can be nonempty. -/
theorem exp_sourceAllCutoffMertensEnvelope_le_scheduled
    {L j : ℕ} (hL : 3 ≤ L)
    (hdom : 32 * sieveRadius j ≤ j)
    (hLX : L ≤ 8 * dyadicScale j) :
    exp (sourceAllCutoffMertensEnvelope L (sieveCutoff j)) ≤
      sourceScheduledProductConstant *
        log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
        log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
        scheduledLogLoss j ^ (5 / 2 : ℝ) := by
  have hz : 2 ≤ sieveCutoff j :=
    two_le_sieveCutoff_of_dominance hdom
  have hX : 2 ≤ dyadicScale j :=
    hz.trans (sieveCutoff_le_dyadicScale j)
  have hlogX : 0 < log (dyadicScale j : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < dyadicScale j by omega))
  have hlogz : 0 < log (sieveCutoff j : ℝ) :=
    log_sieveCutoff_pos hdom
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hH := scheduledLogLoss_one_le j
  have hratio :
      log (dyadicScale j : ℝ) / log (sieveCutoff j : ℝ) ≤
        scheduledLogLoss j := by
    simpa [scheduledLogLoss] using
      log_dyadicScale_div_log_sieveCutoff_le hdom
  by_cases hLz : L ≤ sieveCutoff j
  · rw [sourceAllCutoffMertensEnvelope, if_pos hLz]
    have hbase :=
      exp_sourceMertensEnvelope_le_powers
        (show 2 ≤ L by omega) hz
    have hcut :=
      rpow_neg_le_ratio_rpow hlogX hlogz hH
        (by norm_num : (0 : ℝ) ≤ 7 / 4) hratio
    have hHpow :
        scheduledLogLoss j ^ (7 / 4 : ℝ) ≤
          scheduledLogLoss j ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hH (by norm_num)
    have hcut' :
        log (sieveCutoff j : ℝ) ^ (-(7 / 4 : ℝ)) ≤
          scheduledLogLoss j ^ (5 / 2 : ℝ) *
            log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) :=
      hcut.trans
        (mul_le_mul_of_nonneg_right hHpow
          (Real.rpow_nonneg hlogX.le _))
    calc
      exp (sourceMertensEnvelope L (sieveCutoff j))
          ≤ sourceLargeProductConstant *
              log (sieveCutoff j : ℝ) ^ (-(7 / 4 : ℝ)) *
              log (L : ℝ) ^ (-(3 / 4 : ℝ)) := hbase
      _ ≤ sourceLargeProductConstant *
            (scheduledLogLoss j ^ (5 / 2 : ℝ) *
              log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ))) *
            log (L : ℝ) ^ (-(3 / 4 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcut'
              sourceLargeProductConstant_pos.le)
            (Real.rpow_nonneg hlogL.le _)
      _ ≤ sourceScheduledProductConstant *
            log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ) := by
          have hc :
              sourceLargeProductConstant ≤
                sourceScheduledProductConstant := by
            unfold sourceScheduledProductConstant
            exact le_add_of_nonneg_right
              (mul_nonneg sourceSmallProductConstant_pos.le
                (Real.rpow_nonneg (by norm_num) _))
          have hnonneg :
              0 ≤ log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
                log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
                scheduledLogLoss j ^ (5 / 2 : ℝ) := by
            exact mul_nonneg
              (mul_nonneg (Real.rpow_nonneg hlogX.le _)
                (Real.rpow_nonneg hlogL.le _))
              (Real.rpow_nonneg (zero_le_one.trans hH) _)
          calc
            sourceLargeProductConstant *
                  (scheduledLogLoss j ^ (5 / 2 : ℝ) *
                    log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ))) *
                  log (L : ℝ) ^ (-(3 / 4 : ℝ)) =
                sourceLargeProductConstant *
                  (log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
                    log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
                    scheduledLogLoss j ^ (5 / 2 : ℝ)) := by ring
            _ ≤ sourceScheduledProductConstant *
                  (log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
                    log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
                    scheduledLogLoss j ^ (5 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right hc hnonneg
            _ = _ := by ring
  · have hzL : sieveCutoff j < L := Nat.lt_of_not_ge hLz
    rw [sourceAllCutoffMertensEnvelope, if_neg hLz]
    have hbase :=
      exp_sourceSmallCutoffMertensEnvelope_le_power hz
    have hcut :=
      rpow_neg_le_ratio_rpow hlogX hlogz hH
        (by norm_num : (0 : ℝ) ≤ 5 / 2) hratio
    have hLratio :
        log (L : ℝ) / log (dyadicScale j : ℝ) ≤ 4 :=
      log_nat_div_log_nat_le_four_of_le_eight_mul hX hLX
    have hscaleL :=
      rpow_neg_le_ratio_rpow hlogL hlogX
        (by norm_num : (1 : ℝ) ≤ 4)
        (by norm_num : (0 : ℝ) ≤ 3 / 4) hLratio
    have hsplit :
        log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) =
          log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (dyadicScale j : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_add hlogX]
      congr 1
      ring
    have htarget :
        log (sieveCutoff j : ℝ) ^ (-(5 / 2 : ℝ)) ≤
          scheduledLogLoss j ^ (5 / 2 : ℝ) *
            ((4 : ℝ) ^ (3 / 4 : ℝ) *
              log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
              log (L : ℝ) ^ (-(3 / 4 : ℝ))) := by
      calc
        log (sieveCutoff j : ℝ) ^ (-(5 / 2 : ℝ))
            ≤ scheduledLogLoss j ^ (5 / 2 : ℝ) *
                log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) := hcut
        _ = scheduledLogLoss j ^ (5 / 2 : ℝ) *
              (log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
                log (dyadicScale j : ℝ) ^ (-(3 / 4 : ℝ))) := by
              rw [hsplit]
        _ ≤ scheduledLogLoss j ^ (5 / 2 : ℝ) *
              (log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
                ((4 : ℝ) ^ (3 / 4 : ℝ) *
                  log (L : ℝ) ^ (-(3 / 4 : ℝ)))) := by
              gcongr
        _ = _ := by ring
    calc
      exp (sourceSmallCutoffMertensEnvelope (sieveCutoff j))
          ≤ sourceSmallProductConstant *
              log (sieveCutoff j : ℝ) ^ (-(5 / 2 : ℝ)) := hbase
      _ ≤ sourceSmallProductConstant *
            (scheduledLogLoss j ^ (5 / 2 : ℝ) *
              ((4 : ℝ) ^ (3 / 4 : ℝ) *
                log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
                log (L : ℝ) ^ (-(3 / 4 : ℝ)))) := by
          exact mul_le_mul_of_nonneg_left htarget
            sourceSmallProductConstant_pos.le
      _ ≤ sourceScheduledProductConstant *
            log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ) := by
          let common :=
            log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
              log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
              scheduledLogLoss j ^ (5 / 2 : ℝ)
          have hcommon : 0 ≤ common := by
            dsimp [common]
            exact mul_nonneg
              (mul_nonneg (Real.rpow_nonneg hlogX.le _)
                (Real.rpow_nonneg hlogL.le _))
              (Real.rpow_nonneg (zero_le_one.trans hH) _)
          have hcoef :
              sourceSmallProductConstant * (4 : ℝ) ^ (3 / 4 : ℝ) ≤
                sourceScheduledProductConstant := by
            unfold sourceScheduledProductConstant
            exact le_add_of_nonneg_left sourceLargeProductConstant_pos.le
          calc
            sourceSmallProductConstant *
                  (scheduledLogLoss j ^ (5 / 2 : ℝ) *
                    ((4 : ℝ) ^ (3 / 4 : ℝ) *
                      log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
                      log (L : ℝ) ^ (-(3 / 4 : ℝ)))) =
                (sourceSmallProductConstant * (4 : ℝ) ^ (3 / 4 : ℝ)) *
                  common := by dsimp [common]; ring
            _ ≤ sourceScheduledProductConstant * common :=
              mul_le_mul_of_nonneg_right hcoef hcommon
            _ = _ := by dsimp [common]; ring

end

end Erdos327.Analytic
