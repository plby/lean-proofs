import ErdosProblems.Erdos327.Analytic.SourceScheduledSummation
import ErdosProblems.Erdos327.Analytic.ScheduledLogLossPowers
import ErdosProblems.Erdos327.Analytic.DyadicTerminalArithmetic

/-!
# Summation of the source Euler main term

This file separates the bulk range, where the dyadic scale is no larger
than the residual scale, from the terminal range.  In the bulk range the
two negative cutoff powers combine to the certified exponent
`sourceCanonicalBudgetExponent - 5/2 < -1`.
-/

namespace Erdos327.Analytic

open Filter Finset Real

noncomputable section

/-- Cutoff-independent coefficient in the normalized source bulk
profile. -/
def sourceBulkRawConstant (K : ℝ) : ℝ :=
  16 * sourceBudgetConstant K *
    sourceScheduledProductConstant *
    residualMomentConstant (1 / 4 : ℝ)

theorem sourceBulkRawConstant_pos (K : ℝ) :
    0 < sourceBulkRawConstant K := by
  unfold sourceBulkRawConstant sourceBudgetConstant
  exact mul_pos
    (mul_pos
      (mul_pos (by positivity) (exp_pos _))
      sourceScheduledProductConstant_pos)
    (residualMomentConstant_pos _)

/-- In the bulk range `X ≤ Y`, cancellation of the two roughness-scale
powers leaves exactly `1 / log L`, while the dyadic logarithm has power
`-5/2`. -/
theorem sourceScheduledNormalizedBlockMain_le_bulk_raw
    {L N j : ℕ} {K : ℝ}
    (hL : 3 ≤ L)
    (hLX : L ≤ dyadicScale j)
    (hXY : dyadicScale j ≤ 2 * N / dyadicScale j ^ 2) :
    sourceScheduledNormalizedBlockMain L N K j ≤
      sourceBulkRawConstant K * ((N : ℝ) / log L) *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
        scheduledLogLoss j ^ (5 / 2 : ℝ) := by
  let X : ℕ := dyadicScale j
  let Y : ℕ := 2 * N / X ^ 2
  have hX2 : 2 ≤ X := by
    dsimp [X]
    omega
  have hY2 : 2 ≤ Y := by
    dsimp [Y, X]
    omega
  have hlogX : 0 < log (X : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogLrpow :
      0 < log (L : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_pos_of_pos hlogL _
  have hsqYNat :
      X ^ 2 * Y ≤ 2 * N := by
    dsimp [X, Y]
    exact dyadic_sq_mul_residualCutoff_le N j
  have hsqY :
      (X : ℝ) ^ 2 * (Y : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hsqYNat
  have hprofile0 :
      0 ≤
        sourceBudgetConstant K *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        sourceScheduledProductConstant *
        residualMomentConstant (1 / 4 : ℝ) *
        log (X : ℝ) ^ (-(5 / 2 : ℝ)) *
        scheduledLogLoss j ^ (5 / 2 : ℝ) /
        log (L : ℝ) := by
    apply div_nonneg _ hlogL.le
    have ha : 0 ≤ sourceBudgetConstant K := by
      unfold sourceBudgetConstant
      positivity
    have hb :
        0 ≤ (((j + 3 : ℕ) : ℝ) ^
          sourceCanonicalBudgetExponent) :=
      Real.rpow_nonneg (by positivity) _
    have hc : 0 ≤ sourceScheduledProductConstant :=
      sourceScheduledProductConstant_pos.le
    have hd : 0 ≤ residualMomentConstant (1 / 4 : ℝ) :=
      (residualMomentConstant_pos _).le
    have he : 0 ≤ log (X : ℝ) ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_nonneg hlogX.le _
    have hf : 0 ≤ scheduledLogLoss j ^ (5 / 2 : ℝ) :=
      Real.rpow_nonneg
        (zero_le_one.trans (scheduledLogLoss_one_le j)) _
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg ha hb) hc)
          hd)
        he)
      hf
  unfold sourceScheduledNormalizedBlockMain
  dsimp only
  rw [min_eq_left hXY]
  change
    (sourceBudgetConstant K *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
        (8 * (X : ℝ) ^ 2 *
          (sourceScheduledProductConstant *
            log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ))) *
        (residualMomentConstant (1 / 4 : ℝ) *
          ((Y : ℝ) / log L) *
          (log (X : ℝ) / log (L : ℝ)) ^
            (-(3 / 4 : ℝ))) ≤ _
  rw [Real.div_rpow hlogX.le hlogL.le,
    show -(3 / 4 : ℝ) = -(3 / 4 : ℝ) by rfl]
  have hxcombine :
      log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
          log (X : ℝ) ^ (-(3 / 4 : ℝ)) =
        log (X : ℝ) ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_add hlogX]
    norm_num
  have heq :
      (sourceBudgetConstant K *
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
          (8 * (X : ℝ) ^ 2 *
            (sourceScheduledProductConstant *
              log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
              log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
              scheduledLogLoss j ^ (5 / 2 : ℝ))) *
          (residualMomentConstant (1 / 4 : ℝ) *
            ((Y : ℝ) / log L) *
            (log (X : ℝ) ^ (-(3 / 4 : ℝ)) /
              log (L : ℝ) ^ (-(3 / 4 : ℝ)))) =
        8 *
          (sourceBudgetConstant K *
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
            sourceScheduledProductConstant *
            residualMomentConstant (1 / 4 : ℝ) *
            (log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
              log (X : ℝ) ^ (-(3 / 4 : ℝ))) *
            scheduledLogLoss j ^ (5 / 2 : ℝ) /
            log (L : ℝ)) *
          ((X : ℝ) ^ 2 * (Y : ℝ)) := by
    field_simp [hlogL.ne', hlogLrpow.ne']
  rw [heq]
  calc
    8 *
          (sourceBudgetConstant K *
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
            sourceScheduledProductConstant *
            residualMomentConstant (1 / 4 : ℝ) *
            (log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
              log (X : ℝ) ^ (-(3 / 4 : ℝ))) *
            scheduledLogLoss j ^ (5 / 2 : ℝ) /
            log (L : ℝ)) *
          ((X : ℝ) ^ 2 * (Y : ℝ))
        =
      8 *
          (sourceBudgetConstant K *
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
            sourceScheduledProductConstant *
            residualMomentConstant (1 / 4 : ℝ) *
            log (X : ℝ) ^ (-(5 / 2 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ) /
            log (L : ℝ)) *
          ((X : ℝ) ^ 2 * (Y : ℝ)) := by rw [hxcombine]
    _
        ≤ 8 *
          (sourceBudgetConstant K *
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
            sourceScheduledProductConstant *
            residualMomentConstant (1 / 4 : ℝ) *
            log (X : ℝ) ^ (-(5 / 2 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ) /
            log (L : ℝ)) *
          (2 * (N : ℝ)) := by
      have hprofile0' :
          0 ≤
            sourceBudgetConstant K *
              (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
              sourceScheduledProductConstant *
              residualMomentConstant (1 / 4 : ℝ) *
              log (X : ℝ) ^ (-(5 / 2 : ℝ)) *
              scheduledLogLoss j ^ (5 / 2 : ℝ) /
              log (L : ℝ) := hprofile0
      exact mul_le_mul_of_nonneg_left hsqY
        (mul_nonneg (by norm_num) hprofile0')
    _ = sourceBulkRawConstant K * ((N : ℝ) / log L) *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ) := by
      unfold sourceBulkRawConstant
      dsimp [X]
      ring

/-- Constant in the source bulk power-log profile. -/
def sourceBulkProfileConstant (K : ℝ) : ℝ :=
  sourceBulkRawConstant K *
    (3 : ℝ) ^ sourceCanonicalBudgetExponent *
    (2 : ℝ) ^ (5 / 2 : ℝ) *
    log (2 : ℝ) ^ (-(5 / 2 : ℝ)) *
    scheduledLogLossConstant ^ (5 / 2 : ℝ)

theorem sourceBulkProfileConstant_pos (K : ℝ) :
    0 < sourceBulkProfileConstant K := by
  unfold sourceBulkProfileConstant
  exact mul_pos
    (mul_pos
      (mul_pos
        (mul_pos (sourceBulkRawConstant_pos K)
          (Real.rpow_pos_of_pos (by norm_num) _))
        (Real.rpow_pos_of_pos (by norm_num) _))
      (Real.rpow_pos_of_pos
        (log_pos (by norm_num : (1 : ℝ) < 2)) _))
    (Real.rpow_pos_of_pos scheduledLogLossConstant_pos _)

/-- The normalized source bulk block is bounded by one summable
power-log profile. -/
theorem sourceScheduledNormalizedBlockMain_le_bulk_profile
    {L N j : ℕ} {K : ℝ}
    (hL : 3 ≤ L) (hj : 1 ≤ j)
    (hLX : L ≤ dyadicScale j)
    (hXY : dyadicScale j ≤ 2 * N / dyadicScale j ^ 2) :
    sourceScheduledNormalizedBlockMain L N K j ≤
      sourceBulkProfileConstant K * ((N : ℝ) / log L) *
        (((j + 1 : ℕ) : ℝ) ^
          (sourceCanonicalBudgetExponent - 5 / 2)) *
        log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) := by
  have hraw :=
    sourceScheduledNormalizedBlockMain_le_bulk_raw
      (K := K) hL hLX hXY
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hjreal : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hj1real : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hlogTwo : 0 < log (2 : ℝ) :=
    log_pos (by norm_num)
  have hbudgetExp : 0 ≤ sourceCanonicalBudgetExponent := by
    unfold sourceCanonicalBudgetExponent
    positivity [sourceAnatomySlope_nonneg]
  have hindexNat : j + 3 ≤ 3 * (j + 1) := by omega
  have hindex :
      (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) ≤
        (3 : ℝ) ^ sourceCanonicalBudgetExponent *
          (((j + 1 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) := by
    have hpow :=
      Real.rpow_le_rpow
        (x := ((j + 3 : ℕ) : ℝ))
        (y := (3 : ℝ) * ((j + 1 : ℕ) : ℝ))
        (z := sourceCanonicalBudgetExponent)
        (by positivity)
        (by exact_mod_cast hindexNat)
        hbudgetExp
    rw [Real.mul_rpow (by norm_num) hj1real.le] at hpow
    exact hpow
  have hratio :
      (((j + 1 : ℕ) : ℝ) / (j : ℝ)) ≤ 2 := by
    apply (div_le_iff₀ hjreal).2
    exact_mod_cast (show j + 1 ≤ 2 * j by omega)
  have hjpow :
      (j : ℝ) ^ (-(5 / 2 : ℝ)) ≤
        (2 : ℝ) ^ (5 / 2 : ℝ) *
          (((j + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) :=
    rpow_neg_le_ratio_rpow hj1real hjreal
      (by norm_num) (by norm_num) hratio
  have hlogScale :
      log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) ≤
        ((2 : ℝ) ^ (5 / 2 : ℝ) *
          (((j + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)))) *
        log (2 : ℝ) ^ (-(5 / 2 : ℝ)) := by
    rw [log_dyadicScale,
      Real.mul_rpow hjreal.le hlogTwo.le]
    exact mul_le_mul_of_nonneg_right hjpow
      (Real.rpow_nonneg hlogTwo.le _)
  have hloss :=
    scheduledLogLoss_rpow_le_log_rpow
      (j := j) (r := (5 / 2 : ℝ)) hj (by norm_num)
  have hloss' :
      scheduledLogLoss j ^ (5 / 2 : ℝ) ≤
        scheduledLogLossConstant ^ (5 / 2 : ℝ) *
          log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) := by
    convert hloss using 1 <;> norm_num
  have hprofile0 :
      0 ≤ sourceBulkRawConstant K * ((N : ℝ) / log L) := by
    exact mul_nonneg (sourceBulkRawConstant_pos K).le
      (div_nonneg (Nat.cast_nonneg N) hlogL.le)
  have hloss0 :
      0 ≤ scheduledLogLoss j ^ (5 / 2 : ℝ) :=
    Real.rpow_nonneg
      (zero_le_one.trans (scheduledLogLoss_one_le j)) _
  calc
    sourceScheduledNormalizedBlockMain L N K j
        ≤ sourceBulkRawConstant K * ((N : ℝ) / log L) *
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
            log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ) := hraw
    _ ≤ sourceBulkRawConstant K * ((N : ℝ) / log L) *
          ((3 : ℝ) ^ sourceCanonicalBudgetExponent *
            (((j + 1 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
          (((2 : ℝ) ^ (5 / 2 : ℝ) *
              (((j + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)))) *
            log (2 : ℝ) ^ (-(5 / 2 : ℝ))) *
          (scheduledLogLossConstant ^ (5 / 2 : ℝ) *
            log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) := by
      let A : ℝ := sourceBulkRawConstant K * ((N : ℝ) / log L)
      let B : ℝ :=
        (3 : ℝ) ^ sourceCanonicalBudgetExponent *
          (((j + 1 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)
      let C : ℝ :=
        ((2 : ℝ) ^ (5 / 2 : ℝ) *
            (((j + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)))) *
          log (2 : ℝ) ^ (-(5 / 2 : ℝ))
      let D : ℝ :=
        scheduledLogLossConstant ^ (5 / 2 : ℝ) *
          log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)
      have hB0 : 0 ≤ B := by
        dsimp [B]
        exact mul_nonneg
          (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg hj1real.le _)
      have hC0 : 0 ≤ C := by
        dsimp [C]
        exact mul_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (by norm_num) _)
            (Real.rpow_nonneg hj1real.le _))
          (Real.rpow_nonneg hlogTwo.le _)
      change
        A *
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
            log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ) ≤
          A * B * C * D
      calc
        A * (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
              log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
              scheduledLogLoss j ^ (5 / 2 : ℝ)
            ≤ A * B *
              log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
              scheduledLogLoss j ^ (5 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hindex hprofile0)
              (Real.rpow_nonneg (by positivity) _))
            hloss0
        _ ≤ A * B * C *
              scheduledLogLoss j ^ (5 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogScale
              (mul_nonneg hprofile0 hB0))
            hloss0
        _ ≤ A * B * C * D :=
          mul_le_mul_of_nonneg_left hloss'
            (mul_nonneg (mul_nonneg hprofile0 hB0) hC0)
    _ = sourceBulkProfileConstant K * ((N : ℝ) / log L) *
          (((j + 1 : ℕ) : ℝ) ^
            (sourceCanonicalBudgetExponent - 5 / 2)) *
          log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) := by
      unfold sourceBulkProfileConstant
      rw [show
          sourceCanonicalBudgetExponent - 5 / 2 =
            sourceCanonicalBudgetExponent + (-(5 / 2 : ℝ)) by ring,
        Real.rpow_add hj1real]
      ring

/-- Certified exponent of the source bulk profile. -/
def sourceBulkPowerExponent : ℝ :=
  sourceCanonicalBudgetExponent - 5 / 2

theorem sourceBulkPowerExponent_lt_neg_one :
    sourceBulkPowerExponent < -1 := by
  unfold sourceBulkPowerExponent
  linarith [sourceCanonicalBudgetExponent_lt_three_halves]

/-- The universal source bulk profile is summable. -/
theorem summable_sourceBulkProfile :
    Summable (fun j : ℕ ↦
      (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
        log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) :=
  summable_nat_add_one_rpow_mul_log_rpow
    sourceBulkPowerExponent_lt_neg_one (by norm_num)

/-- Its finite tails have arbitrarily small mass. -/
theorem exists_sourceBulkProfile_tail_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ J' ≥ J, ∀ M : ℕ,
      (∑ j ∈ Ico J' M,
        (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) < ε :=
  exists_powerLogProfile_tail_lt
    sourceBulkPowerExponent_lt_neg_one (by norm_num) hε

/-- Indices in the normalized source bulk range. -/
def sourceBulkIndexSet (L N J M : ℕ) : Finset ℕ :=
  (Ico J M).filter fun j ↦
    32 * sieveRadius j ≤ j ∧
      L ≤ dyadicScale j ∧
      dyadicScale j ≤ 2 * N / dyadicScale j ^ 2

/-- The source Euler main sum over the bulk range is controlled by the
universal summable profile. -/
theorem sum_sourceEulerMain_bulk_le_profile
    {L N J M : ℕ} {K : ℝ}
    (hL : 3 ≤ L) (hJ : 1 ≤ J) :
    (∑ j ∈ sourceBulkIndexSet L N J M,
      sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j) ≤
      sourceBulkProfileConstant K * ((N : ℝ) / log L) *
        (∑ j ∈ Ico J M,
          (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) := by
  let C : ℝ := sourceBulkProfileConstant K * ((N : ℝ) / log L)
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (sourceBulkProfileConstant_pos K).le
      (div_nonneg (Nat.cast_nonneg N) hlogL.le)
  calc
    (∑ j ∈ sourceBulkIndexSet L N J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j)
        ≤
      ∑ j ∈ sourceBulkIndexSet L N J M,
        C *
          ((((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) := by
      apply sum_le_sum
      intro j hj
      rw [sourceBulkIndexSet, mem_filter] at hj
      rcases hj.2 with ⟨hdom, hLX, hXY⟩
      have hj1 : 1 ≤ j := hJ.trans (mem_Ico.mp hj.1).1
      have hLY : L ≤ 2 * N / dyadicScale j ^ 2 :=
        hLX.trans hXY
      have hY2 : 2 ≤ 2 * N / dyadicScale j ^ 2 := by omega
      exact
        (sourceScheduledEulerBlockMain_le_normalized
          (K := K) hL hdom hLX hLY hY2).trans
        (by
          simpa [C, sourceBulkPowerExponent, mul_assoc] using
            (sourceScheduledNormalizedBlockMain_le_bulk_profile
              (K := K) hL hj1 hLX hXY))
    _ ≤
      ∑ j ∈ Ico J M,
        C *
          ((((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) := by
      rw [sourceBulkIndexSet]
      refine sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro j hj
        exact (mem_filter.mp hj).1
      intro j hjIco hjNot
      exact mul_nonneg hC0
        (mul_nonneg
          (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg (Real.log_natCast_nonneg _) _))
    _ = sourceBulkProfileConstant K * ((N : ℝ) / log L) *
        (∑ j ∈ Ico J M,
          (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) := by
      rw [mul_sum]

/-- Uniform source bulk estimate at the exact rough-density scale. -/
theorem exists_sourceBulk_start_for_roughDensity
    (K : ℝ) :
    ∃ J : ℕ, 1 ≤ J ∧
      ∀ L N M : ℕ, 3 ≤ L →
        (∑ j ∈ sourceBulkIndexSet L N J M,
          sourceScheduledEulerBlockMain
            L N sourceAnatomySlope K j) ≤
          (N : ℝ) * Erdos327.roughDensity L / 64 := by
  have hC := sourceBulkProfileConstant_pos K
  have hε :
      0 <
        mertensLowerConstant /
          (64 * sourceBulkProfileConstant K) := by
    positivity [mertensLowerConstant_pos]
  obtain ⟨J₀, hJ₀⟩ :=
    exists_sourceBulkProfile_tail_lt hε
  let J := max J₀ 1
  refine ⟨J, le_max_right _ _, ?_⟩
  intro L N M hL
  have htail :
      (∑ j ∈ Ico J M,
        (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) ≤
        mertensLowerConstant /
          (64 * sourceBulkProfileConstant K) :=
    (hJ₀ J (le_max_left _ _) M).le
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hmain :=
    sum_sourceEulerMain_bulk_le_profile
      (L := L) (N := N) (J := J) (M := M)
      (K := K) hL (le_max_right J₀ 1)
  have hfactor0 :
      0 ≤ sourceBulkProfileConstant K *
        ((N : ℝ) / log L) := by
    exact mul_nonneg hC.le
      (div_nonneg (Nat.cast_nonneg N) hlogL.le)
  have hmertens :=
    mertensLowerConstant_div_log_le_roughDensity hL
  calc
    (∑ j ∈ sourceBulkIndexSet L N J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j)
        ≤ sourceBulkProfileConstant K *
            ((N : ℝ) / log L) *
          (∑ j ∈ Ico J M,
            (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) :=
      hmain
    _ ≤ sourceBulkProfileConstant K *
          ((N : ℝ) / log L) *
          (mertensLowerConstant /
            (64 * sourceBulkProfileConstant K)) :=
      mul_le_mul_of_nonneg_left htail hfactor0
    _ = (N : ℝ) *
          (mertensLowerConstant / log L) / 64 := by
      field_simp [hC.ne', hlogL.ne']
    _ ≤ (N : ℝ) * Erdos327.roughDensity L / 64 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmertens
          (Nat.cast_nonneg N))
        (by norm_num)

/-! ## Terminal normalized range -/

/-- Dyadic endpoint exponent in the source terminal convolution. -/
def sourceTerminalDyadicExponent : ℝ :=
  sourceCanonicalBudgetExponent - 7 / 4

/-- Residual endpoint exponent in the source terminal convolution. -/
def sourceTerminalResidualExponent : ℝ := -(3 / 4 : ℝ)

theorem sourceTerminalDyadicExponent_lt_zero :
    sourceTerminalDyadicExponent < 0 := by
  unfold sourceTerminalDyadicExponent
  linarith [sourceCanonicalBudgetExponent_lt_three_halves]

theorem sourceCanonicalBudgetExponent_gt_three_fourths :
    3 / 4 < sourceCanonicalBudgetExponent := by
  unfold sourceCanonicalBudgetExponent sourceAnatomySlope
  rw [Real.log_four_eq]
  nlinarith [Real.log_two_gt_d9]

theorem sourceTerminalDyadicExponent_gt_neg_one :
    -1 < sourceTerminalDyadicExponent := by
  unfold sourceTerminalDyadicExponent
  linarith [sourceCanonicalBudgetExponent_gt_three_fourths]

theorem sourceTerminalResidualExponent_mem :
    -1 < sourceTerminalResidualExponent ∧
      sourceTerminalResidualExponent < 0 := by
  norm_num [sourceTerminalResidualExponent]

theorem sourceTerminalExponent_sum_lt_zero :
    sourceTerminalDyadicExponent +
        sourceTerminalResidualExponent + 1 < 0 := by
  unfold sourceTerminalDyadicExponent
    sourceTerminalResidualExponent
  linarith [sourceCanonicalBudgetExponent_lt_three_halves]

/-- In the normalized terminal range `Y ≤ X`, the two endpoint powers
remain separate. -/
theorem sourceScheduledNormalizedBlockMain_le_terminal_raw
    {L N j : ℕ} {K : ℝ}
    (hL : 3 ≤ L)
    (hLX : L ≤ dyadicScale j)
    (hLY : L ≤ 2 * N / dyadicScale j ^ 2)
    (hYX : 2 * N / dyadicScale j ^ 2 ≤ dyadicScale j) :
    sourceScheduledNormalizedBlockMain L N K j ≤
      sourceBulkRawConstant K * ((N : ℝ) / log L) *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
        log (2 * N / dyadicScale j ^ 2 : ℕ) ^
          sourceTerminalResidualExponent *
        scheduledLogLoss j ^ (5 / 2 : ℝ) := by
  let X : ℕ := dyadicScale j
  let Y : ℕ := 2 * N / X ^ 2
  have hlogX : 0 < log (X : ℝ) :=
    log_pos (by
      exact_mod_cast (show 1 < X by
        dsimp [X]
        omega))
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by
      exact_mod_cast (show 1 < Y by
        dsimp [Y, X]
        omega))
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogLrpow :
      0 < log (L : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_pos_of_pos hlogL _
  have hsqYNat :
      X ^ 2 * Y ≤ 2 * N := by
    dsimp [X, Y]
    exact dyadic_sq_mul_residualCutoff_le N j
  have hsqY :
      (X : ℝ) ^ 2 * (Y : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hsqYNat
  have hprofile0 :
      0 ≤ sourceBudgetConstant K *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
          sourceScheduledProductConstant *
          residualMomentConstant (1 / 4 : ℝ) *
          log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
          log (Y : ℝ) ^ sourceTerminalResidualExponent *
          scheduledLogLoss j ^ (5 / 2 : ℝ) /
          log (L : ℝ) := by
    apply div_nonneg _ hlogL.le
    have ha : 0 ≤ sourceBudgetConstant K := by
      unfold sourceBudgetConstant
      positivity
    have hb :
        0 ≤ (((j + 3 : ℕ) : ℝ) ^
          sourceCanonicalBudgetExponent) :=
      Real.rpow_nonneg (by positivity) _
    have hc : 0 ≤ sourceScheduledProductConstant :=
      sourceScheduledProductConstant_pos.le
    have hd : 0 ≤ residualMomentConstant (1 / 4 : ℝ) :=
      (residualMomentConstant_pos _).le
    have he : 0 ≤ log (X : ℝ) ^ (-(7 / 4 : ℝ)) :=
      Real.rpow_nonneg hlogX.le _
    have hf :
        0 ≤ log (Y : ℝ) ^ sourceTerminalResidualExponent :=
      Real.rpow_nonneg hlogY.le _
    have hg : 0 ≤ scheduledLogLoss j ^ (5 / 2 : ℝ) :=
      Real.rpow_nonneg
        (zero_le_one.trans (scheduledLogLoss_one_le j)) _
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg ha hb) hc)
            hd)
          he)
        hf)
      hg
  unfold sourceScheduledNormalizedBlockMain
  dsimp only
  rw [min_eq_right hYX]
  change
    (sourceBudgetConstant K *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
        (8 * (X : ℝ) ^ 2 *
          (sourceScheduledProductConstant *
            log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ))) *
        (residualMomentConstant (1 / 4 : ℝ) *
          ((Y : ℝ) / log L) *
          (log (Y : ℝ) / log (L : ℝ)) ^
            (-(3 / 4 : ℝ))) ≤ _
  rw [Real.div_rpow hlogY.le hlogL.le]
  have heq :
      (sourceBudgetConstant K *
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
          (8 * (X : ℝ) ^ 2 *
            (sourceScheduledProductConstant *
              log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
              log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
              scheduledLogLoss j ^ (5 / 2 : ℝ))) *
          (residualMomentConstant (1 / 4 : ℝ) *
            ((Y : ℝ) / log L) *
            (log (Y : ℝ) ^ (-(3 / 4 : ℝ)) /
              log (L : ℝ) ^ (-(3 / 4 : ℝ)))) =
        8 *
          (sourceBudgetConstant K *
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
            sourceScheduledProductConstant *
            residualMomentConstant (1 / 4 : ℝ) *
            log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (Y : ℝ) ^ sourceTerminalResidualExponent *
            scheduledLogLoss j ^ (5 / 2 : ℝ) /
            log (L : ℝ)) *
          ((X : ℝ) ^ 2 * (Y : ℝ)) := by
    unfold sourceTerminalResidualExponent
    field_simp [hlogL.ne', hlogLrpow.ne']
  rw [heq]
  calc
    8 *
          (sourceBudgetConstant K *
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
            sourceScheduledProductConstant *
            residualMomentConstant (1 / 4 : ℝ) *
            log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (Y : ℝ) ^ sourceTerminalResidualExponent *
            scheduledLogLoss j ^ (5 / 2 : ℝ) /
            log (L : ℝ)) *
          ((X : ℝ) ^ 2 * (Y : ℝ))
        ≤
      8 *
          (sourceBudgetConstant K *
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
            sourceScheduledProductConstant *
            residualMomentConstant (1 / 4 : ℝ) *
            log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (Y : ℝ) ^ sourceTerminalResidualExponent *
            scheduledLogLoss j ^ (5 / 2 : ℝ) /
            log (L : ℝ)) *
          (2 * (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hsqY
        (mul_nonneg (by norm_num) hprofile0)
    _ = sourceBulkRawConstant K * ((N : ℝ) / log L) *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
          log (2 * N / dyadicScale j ^ 2 : ℕ) ^
            sourceTerminalResidualExponent *
          scheduledLogLoss j ^ (5 / 2 : ℝ) := by
      unfold sourceBulkRawConstant
      dsimp [X, Y]
      ring

end

end Erdos327.Analytic
