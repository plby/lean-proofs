import ErdosProblems.Erdos327.Analytic.SourceMainSummation

/-!
# Summation of the source terminal range

This module turns the normalized terminal estimate into a two-ended
power profile.  The dyadic endpoint has exponent
`sourceTerminalDyadicExponent`, while the residual endpoint has exponent
`sourceTerminalResidualExponent`.  The logarithmic schedule loss is then
absorbed into half of the strict exponent gap.
-/

namespace Erdos327.Analytic

open Filter Finset Real

noncomputable section

/-- Explicit coefficient in the source terminal power-log profile. -/
def sourceTerminalProfileConstant (K : ℝ) : ℝ :=
  sourceBulkRawConstant K *
    (3 : ℝ) ^ sourceCanonicalBudgetExponent *
    (2 : ℝ) ^ (7 / 4 : ℝ) *
    log (2 : ℝ) ^ (-(7 / 4 : ℝ)) *
    (2 : ℝ) ^ (-sourceTerminalResidualExponent) *
    log (2 : ℝ) ^ sourceTerminalResidualExponent *
    scheduledLogLossConstant ^ (5 / 2 : ℝ)

theorem sourceTerminalProfileConstant_pos (K : ℝ) :
    0 < sourceTerminalProfileConstant K := by
  unfold sourceTerminalProfileConstant
  positivity [sourceBulkRawConstant_pos K, scheduledLogLossConstant_pos,
    log_pos (by norm_num : (1 : ℝ) < 2)]

theorem source_terminal_budget_index_le
    {j : ℕ} :
    (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) ≤
      (3 : ℝ) ^ sourceCanonicalBudgetExponent *
        (((j + 1 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) := by
  have hbudgetExp : 0 ≤ sourceCanonicalBudgetExponent := by
    unfold sourceCanonicalBudgetExponent
    positivity [sourceAnatomySlope_nonneg]
  have hindexNat : j + 3 ≤ 3 * (j + 1) := by omega
  have hpow :=
    Real.rpow_le_rpow
      (x := ((j + 3 : ℕ) : ℝ))
      (y := (3 : ℝ) * ((j + 1 : ℕ) : ℝ))
      (z := sourceCanonicalBudgetExponent)
      (by positivity)
      (by exact_mod_cast hindexNat)
      hbudgetExp
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hpow
  exact hpow

theorem source_terminal_dyadic_log_le
    {j : ℕ} (hj : 1 ≤ j) :
    log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) ≤
      (2 : ℝ) ^ (7 / 4 : ℝ) *
        (((j + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ))) *
        log (2 : ℝ) ^ (-(7 / 4 : ℝ)) := by
  have hjreal : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hj1real : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hlogTwo : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hratio :
      (((j + 1 : ℕ) : ℝ) / (j : ℝ)) ≤ 2 := by
    apply (div_le_iff₀ hjreal).2
    exact_mod_cast (show j + 1 ≤ 2 * j by omega)
  have hjpow :
      (j : ℝ) ^ (-(7 / 4 : ℝ)) ≤
        (2 : ℝ) ^ (7 / 4 : ℝ) *
          (((j + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ))) :=
    rpow_neg_le_ratio_rpow hj1real hjreal
      (by norm_num) (by norm_num) hratio
  rw [log_dyadicScale,
    Real.mul_rpow hjreal.le hlogTwo.le]
  exact mul_le_mul_of_nonneg_right hjpow
    (Real.rpow_nonneg hlogTwo.le _)

theorem source_terminal_residual_log_le
    {Q j : ℕ}
    (hY : 2 ≤ Q / dyadicScale j ^ 2) :
    log (Q / dyadicScale j ^ 2 : ℕ) ^
        sourceTerminalResidualExponent ≤
      (2 : ℝ) ^ (-sourceTerminalResidualExponent) *
        (((dyadicResidualIndex Q j + 1 : ℕ) : ℝ) ^
          sourceTerminalResidualExponent) *
        log (2 : ℝ) ^ sourceTerminalResidualExponent := by
  let k := dyadicResidualIndex Q j
  have hkposNat : 0 < k := by
    dsimp [k]
    exact dyadicResidualIndex_pos hY
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkposNat
  have hk1pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hlogTwo : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hres :=
    residualIndex_mul_log_two_le_log_residual hY
  have hq : sourceTerminalResidualExponent ≤ 0 :=
    sourceTerminalResidualExponent_mem.2.le
  have hlogpow :
      log (Q / dyadicScale j ^ 2 : ℕ) ^
          sourceTerminalResidualExponent ≤
        ((k : ℝ) * log 2) ^ sourceTerminalResidualExponent := by
    apply Real.rpow_le_rpow_of_nonpos
      (mul_pos hkpos hlogTwo)
      ?_ hq
    simpa [k] using hres
  have hratio :
      (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ≤ 2 := by
    apply (div_le_iff₀ hkpos).2
    exact_mod_cast (show k + 1 ≤ 2 * k by omega)
  have hkpow :
      (k : ℝ) ^ sourceTerminalResidualExponent ≤
        (2 : ℝ) ^ (-sourceTerminalResidualExponent) *
          (((k + 1 : ℕ) : ℝ) ^
            sourceTerminalResidualExponent) := by
    have h :=
      rpow_neg_le_ratio_rpow hk1pos hkpos
        (by norm_num) (neg_nonneg.mpr hq) hratio
    simpa only [neg_neg] using h
  calc
    log (Q / dyadicScale j ^ 2 : ℕ) ^
          sourceTerminalResidualExponent
        ≤ ((k : ℝ) * log 2) ^
            sourceTerminalResidualExponent := hlogpow
    _ = (k : ℝ) ^ sourceTerminalResidualExponent *
          log 2 ^ sourceTerminalResidualExponent := by
      rw [Real.mul_rpow hkpos.le hlogTwo.le]
    _ ≤
        ((2 : ℝ) ^ (-sourceTerminalResidualExponent) *
          (((k + 1 : ℕ) : ℝ) ^
            sourceTerminalResidualExponent)) *
          log 2 ^ sourceTerminalResidualExponent :=
      mul_le_mul_of_nonneg_right hkpow
        (Real.rpow_nonneg hlogTwo.le _)
    _ = (2 : ℝ) ^ (-sourceTerminalResidualExponent) *
          (((dyadicResidualIndex Q j + 1 : ℕ) : ℝ) ^
            sourceTerminalResidualExponent) *
          log 2 ^ sourceTerminalResidualExponent := by
      simp only [k]

/-- Pointwise terminal profile before absorbing the logarithmic schedule
loss. -/
theorem sourceScheduledNormalizedBlockMain_le_terminal_profile
    {L N j : ℕ} {K : ℝ}
    (hL : 3 ≤ L) (hj : 1 ≤ j)
    (hLX : L ≤ dyadicScale j)
    (hLY : L ≤ 2 * N / dyadicScale j ^ 2)
    (hYX : 2 * N / dyadicScale j ^ 2 ≤ dyadicScale j) :
    sourceScheduledNormalizedBlockMain L N K j ≤
      sourceTerminalProfileConstant K * ((N : ℝ) / log L) *
        (((j + 1 : ℕ) : ℝ) ^ sourceTerminalDyadicExponent) *
        (((dyadicResidualIndex (2 * N) j + 1 : ℕ) : ℝ) ^
          sourceTerminalResidualExponent) *
        log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) := by
  have hraw :=
    sourceScheduledNormalizedBlockMain_le_terminal_raw
      (K := K) hL hLX hLY hYX
  have hbudget := source_terminal_budget_index_le (j := j)
  have hdyadic := source_terminal_dyadic_log_le hj
  have hY2 : 2 ≤ 2 * N / dyadicScale j ^ 2 := by omega
  have hresidual :=
    source_terminal_residual_log_le
      (Q := 2 * N) (j := j) hY2
  have hloss :=
    scheduledLogLoss_rpow_le_log_rpow
      (j := j) (r := (5 / 2 : ℝ)) hj (by norm_num)
  have hloss' :
      scheduledLogLoss j ^ (5 / 2 : ℝ) ≤
        scheduledLogLossConstant ^ (5 / 2 : ℝ) *
          log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) := by
    convert hloss using 1; norm_num
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hA0 :
      0 ≤ sourceBulkRawConstant K * ((N : ℝ) / log L) := by
    exact mul_nonneg (sourceBulkRawConstant_pos K).le
      (div_nonneg (Nat.cast_nonneg N) hlogL.le)
  have hbudgetR0 :
      0 ≤ (((j + 3 : ℕ) : ℝ) ^
        sourceCanonicalBudgetExponent) :=
    Real.rpow_nonneg (by positivity) _
  have hdyadicR0 :
      0 ≤ log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hresidualR0 :
      0 ≤ log (2 * N / dyadicScale j ^ 2 : ℕ) ^
        sourceTerminalResidualExponent :=
    Real.rpow_nonneg (by positivity) _
  have hlossR0 :
      0 ≤ scheduledLogLoss j ^ (5 / 2 : ℝ) :=
    Real.rpow_nonneg
      (zero_le_one.trans (scheduledLogLoss_one_le j)) _
  calc
    sourceScheduledNormalizedBlockMain L N K j
        ≤ sourceBulkRawConstant K * ((N : ℝ) / log L) *
            (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
            log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (2 * N / dyadicScale j ^ 2 : ℕ) ^
              sourceTerminalResidualExponent *
            scheduledLogLoss j ^ (5 / 2 : ℝ) := hraw
    _ ≤ sourceBulkRawConstant K * ((N : ℝ) / log L) *
          ((3 : ℝ) ^ sourceCanonicalBudgetExponent *
            (((j + 1 : ℕ) : ℝ) ^
              sourceCanonicalBudgetExponent)) *
          ((2 : ℝ) ^ (7 / 4 : ℝ) *
            (((j + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ))) *
            log (2 : ℝ) ^ (-(7 / 4 : ℝ))) *
          ((2 : ℝ) ^ (-sourceTerminalResidualExponent) *
            (((dyadicResidualIndex (2 * N) j + 1 : ℕ) : ℝ) ^
              sourceTerminalResidualExponent) *
            log (2 : ℝ) ^ sourceTerminalResidualExponent) *
          (scheduledLogLossConstant ^ (5 / 2 : ℝ) *
            log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) := by
      calc
        _ ≤ sourceBulkRawConstant K * ((N : ℝ) / log L) *
              ((3 : ℝ) ^ sourceCanonicalBudgetExponent *
                (((j + 1 : ℕ) : ℝ) ^
                  sourceCanonicalBudgetExponent)) *
              log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
              log (2 * N / dyadicScale j ^ 2 : ℕ) ^
                sourceTerminalResidualExponent *
              scheduledLogLoss j ^ (5 / 2 : ℝ) := by
          gcongr
        _ ≤ sourceBulkRawConstant K * ((N : ℝ) / log L) *
              ((3 : ℝ) ^ sourceCanonicalBudgetExponent *
                (((j + 1 : ℕ) : ℝ) ^
                  sourceCanonicalBudgetExponent)) *
              ((2 : ℝ) ^ (7 / 4 : ℝ) *
                (((j + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ))) *
                log (2 : ℝ) ^ (-(7 / 4 : ℝ))) *
              log (2 * N / dyadicScale j ^ 2 : ℕ) ^
                sourceTerminalResidualExponent *
              scheduledLogLoss j ^ (5 / 2 : ℝ) := by
          gcongr
        _ ≤ sourceBulkRawConstant K * ((N : ℝ) / log L) *
              ((3 : ℝ) ^ sourceCanonicalBudgetExponent *
                (((j + 1 : ℕ) : ℝ) ^
                  sourceCanonicalBudgetExponent)) *
              ((2 : ℝ) ^ (7 / 4 : ℝ) *
                (((j + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ))) *
                log (2 : ℝ) ^ (-(7 / 4 : ℝ))) *
              ((2 : ℝ) ^ (-sourceTerminalResidualExponent) *
                (((dyadicResidualIndex (2 * N) j + 1 : ℕ) : ℝ) ^
                  sourceTerminalResidualExponent) *
                log (2 : ℝ) ^ sourceTerminalResidualExponent) *
              scheduledLogLoss j ^ (5 / 2 : ℝ) := by
          gcongr
        _ ≤ sourceBulkRawConstant K * ((N : ℝ) / log L) *
              ((3 : ℝ) ^ sourceCanonicalBudgetExponent *
                (((j + 1 : ℕ) : ℝ) ^
                  sourceCanonicalBudgetExponent)) *
              ((2 : ℝ) ^ (7 / 4 : ℝ) *
                (((j + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ))) *
                log (2 : ℝ) ^ (-(7 / 4 : ℝ))) *
              ((2 : ℝ) ^ (-sourceTerminalResidualExponent) *
                (((dyadicResidualIndex (2 * N) j + 1 : ℕ) : ℝ) ^
                  sourceTerminalResidualExponent) *
                log (2 : ℝ) ^ sourceTerminalResidualExponent) *
              (scheduledLogLossConstant ^ (5 / 2 : ℝ) *
                log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) := by
          gcongr
    _ = sourceTerminalProfileConstant K * ((N : ℝ) / log L) *
          (((j + 1 : ℕ) : ℝ) ^ sourceTerminalDyadicExponent) *
          (((dyadicResidualIndex (2 * N) j + 1 : ℕ) : ℝ) ^
            sourceTerminalResidualExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) := by
      unfold sourceTerminalProfileConstant
        sourceTerminalDyadicExponent
      rw [show
          sourceCanonicalBudgetExponent - 7 / 4 =
            sourceCanonicalBudgetExponent + (-(7 / 4 : ℝ)) by ring,
        Real.rpow_add (by positivity :
          (0 : ℝ) < ((j + 1 : ℕ) : ℝ))]
      ring

/-- Half of the strict terminal convolution gap, used to absorb the
fifth power of the schedule logarithm. -/
def sourceTerminalLogAbsorption : ℝ :=
  -(sourceTerminalDyadicExponent +
      sourceTerminalResidualExponent + 1) / 2

theorem sourceTerminalLogAbsorption_pos :
    0 < sourceTerminalLogAbsorption := by
  unfold sourceTerminalLogAbsorption
  linarith [sourceTerminalExponent_sum_lt_zero]

/-- Dyadic exponent after absorbing the schedule logarithm. -/
def sourceTerminalAbsorbedDyadicExponent : ℝ :=
  sourceTerminalDyadicExponent + sourceTerminalLogAbsorption

theorem sourceTerminalAbsorbedDyadicExponent_gt_neg_one :
    -1 < sourceTerminalAbsorbedDyadicExponent := by
  unfold sourceTerminalAbsorbedDyadicExponent
  linarith [sourceTerminalDyadicExponent_gt_neg_one,
    sourceTerminalLogAbsorption_pos]

theorem sourceTerminalAbsorbedDyadicExponent_lt_zero :
    sourceTerminalAbsorbedDyadicExponent < 0 := by
  unfold sourceTerminalAbsorbedDyadicExponent
    sourceTerminalLogAbsorption
  linarith [sourceTerminalDyadicExponent_lt_zero,
    sourceTerminalResidualExponent_mem.1]

theorem sourceTerminalAbsorbedExponent_sum_lt_zero :
    sourceTerminalAbsorbedDyadicExponent +
        sourceTerminalResidualExponent + 1 < 0 := by
  unfold sourceTerminalAbsorbedDyadicExponent
    sourceTerminalLogAbsorption
  linarith [sourceTerminalExponent_sum_lt_zero]

/-- A universal index after which the fifth power of the schedule
logarithm is absorbed by the chosen positive exponent. -/
theorem exists_sourceTerminalLogAbsorption_start :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ j ≥ J,
      log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) ≤
        (((j + 1 : ℕ) : ℝ) ^ sourceTerminalLogAbsorption) := by
  have hev :=
    eventually_log_add_one_rpow_le_rpow
      (5 : ℝ) sourceTerminalLogAbsorption_pos
  rcases (eventually_atTop.1 hev) with ⟨J₀, hJ₀⟩
  let J := max J₀ 1
  refine ⟨J, le_max_right _ _, ?_⟩
  intro j hj
  exact hJ₀ j ((le_max_left J₀ 1).trans hj)

/-- Pointwise terminal profile after absorbing the logarithmic loss. -/
theorem sourceScheduledNormalizedBlockMain_le_terminal_absorbed
    {L N j : ℕ} {K : ℝ}
    (hL : 3 ≤ L) (hj : 1 ≤ j)
    (hLX : L ≤ dyadicScale j)
    (hLY : L ≤ 2 * N / dyadicScale j ^ 2)
    (hYX : 2 * N / dyadicScale j ^ 2 ≤ dyadicScale j)
    (hlog :
      log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) ≤
        (((j + 1 : ℕ) : ℝ) ^ sourceTerminalLogAbsorption)) :
    sourceScheduledNormalizedBlockMain L N K j ≤
      sourceTerminalProfileConstant K * ((N : ℝ) / log L) *
        (((j + 1 : ℕ) : ℝ) ^
          sourceTerminalAbsorbedDyadicExponent) *
        (((dyadicResidualIndex (2 * N) j + 1 : ℕ) : ℝ) ^
          sourceTerminalResidualExponent) := by
  have hprofile :=
    sourceScheduledNormalizedBlockMain_le_terminal_profile
      (K := K) hL hj hLX hLY hYX
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hprefix0 :
      0 ≤ sourceTerminalProfileConstant K * ((N : ℝ) / log L) *
        (((j + 1 : ℕ) : ℝ) ^ sourceTerminalDyadicExponent) *
        (((dyadicResidualIndex (2 * N) j + 1 : ℕ) : ℝ) ^
          sourceTerminalResidualExponent) := by
    positivity [sourceTerminalProfileConstant_pos K]
  calc
    sourceScheduledNormalizedBlockMain L N K j
        ≤ sourceTerminalProfileConstant K * ((N : ℝ) / log L) *
            (((j + 1 : ℕ) : ℝ) ^ sourceTerminalDyadicExponent) *
            (((dyadicResidualIndex (2 * N) j + 1 : ℕ) : ℝ) ^
              sourceTerminalResidualExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) := hprofile
    _ ≤ sourceTerminalProfileConstant K * ((N : ℝ) / log L) *
          (((j + 1 : ℕ) : ℝ) ^ sourceTerminalDyadicExponent) *
          (((dyadicResidualIndex (2 * N) j + 1 : ℕ) : ℝ) ^
            sourceTerminalResidualExponent) *
          (((j + 1 : ℕ) : ℝ) ^
            sourceTerminalLogAbsorption) :=
      mul_le_mul_of_nonneg_left hlog hprefix0
    _ = sourceTerminalProfileConstant K * ((N : ℝ) / log L) *
          (((j + 1 : ℕ) : ℝ) ^
            sourceTerminalAbsorbedDyadicExponent) *
          (((dyadicResidualIndex (2 * N) j + 1 : ℕ) : ℝ) ^
            sourceTerminalResidualExponent) := by
      unfold sourceTerminalAbsorbedDyadicExponent
      rw [Real.rpow_add (by positivity :
        (0 : ℝ) < ((j + 1 : ℕ) : ℝ))]
      ring

/-- In the strict terminal range, the absorbed dyadic endpoint is
controlled by the ambient binary logarithm. -/
theorem source_terminal_dyadic_endpoint_le
    {Q j : ℕ}
    (hYpos : 1 ≤ Q / dyadicScale j ^ 2)
    (hterminal : Q / dyadicScale j ^ 2 < dyadicScale j) :
    (((j + 1 : ℕ) : ℝ) ^
        sourceTerminalAbsorbedDyadicExponent) ≤
      (3 : ℝ) ^ (-sourceTerminalAbsorbedDyadicExponent) *
        (((Nat.log 2 Q + 1 : ℕ) : ℝ) ^
          sourceTerminalAbsorbedDyadicExponent) := by
  have hn :=
    log_lt_three_mul_index_of_residual_lt_scale
      hYpos hterminal
  have hj1pos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hn1pos :
      (0 : ℝ) < ((Nat.log 2 Q + 1 : ℕ) : ℝ) := by positivity
  have hratio :
      (((Nat.log 2 Q + 1 : ℕ) : ℝ) /
          ((j + 1 : ℕ) : ℝ)) ≤ 3 := by
    apply (div_le_iff₀ hj1pos).2
    exact_mod_cast
      (show Nat.log 2 Q + 1 ≤ 3 * (j + 1) by omega)
  have h :=
    rpow_neg_le_ratio_rpow hn1pos hj1pos
      (by norm_num)
      (neg_nonneg.mpr
        sourceTerminalAbsorbedDyadicExponent_lt_zero.le)
      hratio
  simpa only [neg_neg] using h

/-- Indices in the normalized strict source terminal range. -/
def sourceTerminalIndexSet (L N J M : ℕ) : Finset ℕ :=
  (Ico J M).filter fun j ↦
    32 * sieveRadius j ≤ j ∧
      L ≤ dyadicScale j ∧
      L ≤ 2 * N / dyadicScale j ^ 2 ∧
      2 * N / dyadicScale j ^ 2 < dyadicScale j

/-- Explicit coefficient after summing the terminal residual indices. -/
def sourceTerminalSumConstant (K : ℝ) : ℝ :=
  sourceTerminalProfileConstant K *
    (3 : ℝ) ^ (-sourceTerminalAbsorbedDyadicExponent) *
    partialRpowConstant sourceTerminalResidualExponent

theorem sourceTerminalSumConstant_pos (K : ℝ) :
    0 < sourceTerminalSumConstant K := by
  unfold sourceTerminalSumConstant
  positivity [sourceTerminalProfileConstant_pos K,
    partialRpowConstant_pos sourceTerminalResidualExponent_mem.1]

/-- The complete strict terminal Euler-main sum has a negative power of
the ambient binary logarithm.  The estimate is uniform in the upper
summation endpoint. -/
theorem sum_sourceEulerMain_terminal_le_log_rpow
    {L N J M : ℕ} {K : ℝ}
    (hL : 3 ≤ L) (hJ : 1 ≤ J)
    (habs : ∀ j ≥ J,
      log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) ≤
        (((j + 1 : ℕ) : ℝ) ^ sourceTerminalLogAbsorption)) :
    (∑ j ∈ sourceTerminalIndexSet L N J M,
      sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j) ≤
      sourceTerminalSumConstant K * ((N : ℝ) / log L) *
        (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
          (sourceTerminalAbsorbedDyadicExponent +
            sourceTerminalResidualExponent + 1)) := by
  let s := sourceTerminalIndexSet L N J M
  let A := sourceTerminalProfileConstant K * ((N : ℝ) / log L)
  let B :=
    (3 : ℝ) ^ (-sourceTerminalAbsorbedDyadicExponent) *
      (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
        sourceTerminalAbsorbedDyadicExponent)
  let f : ℕ → ℝ := fun j ↦
    (((dyadicResidualIndex (2 * N) j + 1 : ℕ) : ℝ) ^
      sourceTerminalResidualExponent)
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity [sourceTerminalProfileConstant_pos K]
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hs :
      ∀ j ∈ s, 2 * j ≤ Nat.log 2 (2 * N) := by
    intro j hj
    simp only [s, sourceTerminalIndexSet, mem_filter] at hj
    have hY2 : 2 ≤ 2 * N / dyadicScale j ^ 2 := by
      omega
    exact (two_mul_index_lt_log_of_two_le_residual hY2).le
  have hresSum :
      (∑ j ∈ s, f j) ≤
        partialRpowConstant sourceTerminalResidualExponent *
          (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
            (sourceTerminalResidualExponent + 1)) := by
    simpa [f] using
      (sum_dyadicResidualIndex_rpow_le
        (s := s) hs sourceTerminalResidualExponent_mem.1
        sourceTerminalResidualExponent_mem.2.le)
  calc
    (∑ j ∈ sourceTerminalIndexSet L N J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j)
        ≤ ∑ j ∈ s,
            A *
              (((j + 1 : ℕ) : ℝ) ^
                sourceTerminalAbsorbedDyadicExponent) *
              f j := by
      apply sum_le_sum
      intro j hj
      simp only [sourceTerminalIndexSet, mem_filter] at hj
      rcases hj.2 with ⟨hdom, hLX, hLY, hterminal⟩
      have hj1 : 1 ≤ j := hJ.trans (mem_Ico.mp hj.1).1
      have hY2 : 2 ≤ 2 * N / dyadicScale j ^ 2 := by omega
      exact
        (sourceScheduledEulerBlockMain_le_normalized
          (K := K) hL hdom hLX hLY hY2).trans
        (by
          simpa [A, f, mul_assoc] using
            (sourceScheduledNormalizedBlockMain_le_terminal_absorbed
              (K := K) hL hj1 hLX hLY hterminal.le
              (habs j (mem_Ico.mp hj.1).1)))
    _ ≤ ∑ j ∈ s, A * B * f j := by
      apply sum_le_sum
      intro j hj
      have hjSet := hj
      simp only [s, sourceTerminalIndexSet, mem_filter] at hjSet
      rcases hjSet.2 with ⟨_, _, hLY, hterminal⟩
      have hendpoint :=
        source_terminal_dyadic_endpoint_le
          (Q := 2 * N) (j := j)
          (by omega) hterminal
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hendpoint hA0)
        (by
          dsimp [f]
          positivity)
    _ = A * B * (∑ j ∈ s, f j) := by
      rw [mul_sum]
    _ ≤ A * B *
          (partialRpowConstant sourceTerminalResidualExponent *
            (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
              (sourceTerminalResidualExponent + 1))) :=
      mul_le_mul_of_nonneg_left hresSum (mul_nonneg hA0 hB0)
    _ = sourceTerminalSumConstant K * ((N : ℝ) / log L) *
          (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
            (sourceTerminalAbsorbedDyadicExponent +
              sourceTerminalResidualExponent + 1)) := by
      unfold sourceTerminalSumConstant
      dsimp [A, B]
      let T : ℝ := ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)
      have hT : 0 < T := by dsimp [T]; positivity
      have hpowers :
          T ^ sourceTerminalAbsorbedDyadicExponent *
              T ^ (sourceTerminalResidualExponent + 1) =
            T ^ (sourceTerminalAbsorbedDyadicExponent +
              sourceTerminalResidualExponent + 1) := by
        rw [← Real.rpow_add hT]
        congr 1
        ring
      change
        sourceTerminalProfileConstant K * ((N : ℝ) / log L) *
              ((3 : ℝ) ^ (-sourceTerminalAbsorbedDyadicExponent) *
                T ^ sourceTerminalAbsorbedDyadicExponent) *
            (partialRpowConstant sourceTerminalResidualExponent *
              T ^ (sourceTerminalResidualExponent + 1)) =
          sourceTerminalProfileConstant K *
                (3 : ℝ) ^ (-sourceTerminalAbsorbedDyadicExponent) *
                partialRpowConstant sourceTerminalResidualExponent *
              ((N : ℝ) / log L) *
            T ^ (sourceTerminalAbsorbedDyadicExponent +
              sourceTerminalResidualExponent + 1)
      calc
        _ = sourceTerminalProfileConstant K *
              (3 : ℝ) ^ (-sourceTerminalAbsorbedDyadicExponent) *
              partialRpowConstant sourceTerminalResidualExponent *
              ((N : ℝ) / log L) *
              (T ^ sourceTerminalAbsorbedDyadicExponent *
                T ^ (sourceTerminalResidualExponent + 1)) := by ring
        _ = _ := by rw [hpowers]

/-- The binary logarithm of `2N`, shifted by one, tends to infinity. -/
theorem tendsto_natLogTwo_two_mul_add_one_atTop :
    Tendsto (fun N : ℕ ↦ Nat.log 2 (2 * N) + 1) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop (2 ^ b)] with N hN
  have hpow : 2 ^ b ≤ 2 * N := by omega
  have hblog : b ≤ Nat.log 2 (2 * N) :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  omega

/-- The negative terminal binary-log profile tends to zero. -/
theorem tendsto_sourceTerminalLogProfile :
    Tendsto
      (fun N : ℕ ↦
        (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
          (sourceTerminalAbsorbedDyadicExponent +
            sourceTerminalResidualExponent + 1)))
      atTop (nhds 0) := by
  have hbase :
      Tendsto
        (fun N : ℕ ↦
          (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      tendsto_natLogTwo_two_mul_add_one_atTop
  have h :=
    (tendsto_rpow_neg_atTop
      (y := -(sourceTerminalAbsorbedDyadicExponent +
        sourceTerminalResidualExponent + 1))
      (neg_pos.mpr sourceTerminalAbsorbedExponent_sum_lt_zero)).comp
      hbase
  convert h using 1
  funext N
  congr 1
  ring

/-- After one universal dyadic start and an `N`-threshold depending only
on the requested accuracy and the analytic constant, the full strict
terminal sum is an arbitrarily small multiple of `N / log L`. -/
theorem exists_sourceTerminal_start_for_epsilon
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J N₀ : ℕ, 1 ≤ J ∧
      ∀ L N M : ℕ, 3 ≤ L → N₀ ≤ N →
        (∑ j ∈ sourceTerminalIndexSet L N J M,
          sourceScheduledEulerBlockMain
            L N sourceAnatomySlope K j) ≤
          ε * ((N : ℝ) / log L) := by
  obtain ⟨J, hJ, habs⟩ :=
    exists_sourceTerminalLogAbsorption_start
  have hC : 0 < sourceTerminalSumConstant K :=
    sourceTerminalSumConstant_pos K
  have hthreshold :
      0 < ε / sourceTerminalSumConstant K :=
    div_pos hε hC
  have hev :
      ∀ᶠ N : ℕ in atTop,
        (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
          (sourceTerminalAbsorbedDyadicExponent +
            sourceTerminalResidualExponent + 1)) <
          ε / sourceTerminalSumConstant K :=
    (tendsto_order.1 tendsto_sourceTerminalLogProfile).2
      _ hthreshold
  rcases (eventually_atTop.1 hev) with ⟨N₀, hN₀⟩
  refine ⟨J, N₀, hJ, ?_⟩
  intro L N M hL hN
  have hmain :=
    sum_sourceEulerMain_terminal_le_log_rpow
      (L := L) (N := N) (J := J) (M := M)
      (K := K) hL hJ habs
  have hprofile :=
    (lt_div_iff₀ hC).mp (hN₀ N hN)
  have hprofile' :
      sourceTerminalSumConstant K *
          (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
            (sourceTerminalAbsorbedDyadicExponent +
              sourceTerminalResidualExponent + 1)) ≤ ε := by
    simpa [mul_comm] using hprofile.le
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hfactor0 : 0 ≤ (N : ℝ) / log L :=
    div_nonneg (Nat.cast_nonneg N) hlogL.le
  calc
    (∑ j ∈ sourceTerminalIndexSet L N J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j)
        ≤ sourceTerminalSumConstant K * ((N : ℝ) / log L) *
            (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
              (sourceTerminalAbsorbedDyadicExponent +
                sourceTerminalResidualExponent + 1)) := hmain
    _ =
        (sourceTerminalSumConstant K *
          (((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^
            (sourceTerminalAbsorbedDyadicExponent +
              sourceTerminalResidualExponent + 1))) *
          ((N : ℝ) / log L) := by ring
    _ ≤ ε * ((N : ℝ) / log L) :=
      mul_le_mul_of_nonneg_right hprofile' hfactor0

/-- Uniform strict-terminal estimate at the rough-density scale used by
the final source assembly. -/
theorem exists_sourceTerminal_start_for_roughDensity
    (K : ℝ) :
    ∃ J N₀ : ℕ, 1 ≤ J ∧
      ∀ L N M : ℕ, 3 ≤ L → N₀ ≤ N →
        (∑ j ∈ sourceTerminalIndexSet L N J M,
          sourceScheduledEulerBlockMain
            L N sourceAnatomySlope K j) ≤
          (N : ℝ) * Erdos327.roughDensity L / 64 := by
  have hε : 0 < mertensLowerConstant / 64 := by
    positivity [mertensLowerConstant_pos]
  obtain ⟨J, N₀, hJ, hterminal⟩ :=
    exists_sourceTerminal_start_for_epsilon K hε
  refine ⟨J, N₀, hJ, ?_⟩
  intro L N M hL hN
  have hmain := hterminal L N M hL hN
  have hmertens :=
    mertensLowerConstant_div_log_le_roughDensity hL
  calc
    (∑ j ∈ sourceTerminalIndexSet L N J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j)
        ≤ (mertensLowerConstant / 64) *
            ((N : ℝ) / log L) := hmain
    _ = (N : ℝ) *
          (mertensLowerConstant / log L) / 64 := by ring
    _ ≤ (N : ℝ) * Erdos327.roughDensity L / 64 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmertens
          (Nat.cast_nonneg N))
        (by norm_num)

end

end Erdos327.Analytic
