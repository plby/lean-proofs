import ErdosProblems.Erdos327.Analytic.SourceMainSummation
import ErdosProblems.Erdos327.Analytic.AsymptoticParameterSelection

/-!
# Boundary summation for the source Euler main term

This file treats the two ranges in which the normalized residual
estimate is unavailable.  The short transition range has
`X < L ≤ 8X`; the small-residual range has
`0 < 2N / X² < L`.  In both ranges the exact residual length is retained.
-/

namespace Erdos327.Analytic

open Filter Finset Real Topology

noncomputable section

/-- Cutoff-independent coefficient for both exact-length boundary
estimates. -/
def sourceBoundaryRawConstant (K : ℝ) : ℝ :=
  16 * sourceBudgetConstant K * sourceScheduledProductConstant

theorem sourceBoundaryRawConstant_pos (K : ℝ) :
    0 < sourceBoundaryRawConstant K := by
  unfold sourceBoundaryRawConstant sourceBudgetConstant
  positivity [sourceScheduledProductConstant_pos]

/-- In every potentially nonempty scheduled block, replacing the exact
residual moment by its interval length gives a scale-free `N` bound.
The only loss is the elementary comparison `log L ≤ 4 log X`. -/
theorem sourceScheduledEulerBlockMain_le_boundary_raw
    {L N j : ℕ} {K : ℝ}
    (hL : 3 ≤ L)
    (hdom : 32 * sieveRadius j ≤ j)
    (hXL : dyadicScale j < L)
    (hnear : L ≤ 8 * dyadicScale j) :
    sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j ≤
      sourceBoundaryRawConstant K * (N : ℝ) *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
        scheduledLogLoss j ^ (5 / 2 : ℝ) := by
  let X : ℕ := dyadicScale j
  let Y : ℕ := 2 * N / X ^ 2
  have hX2 : 2 ≤ X := by
    dsimp [X]
    exact
      (two_le_sieveCutoff_of_dominance hdom).trans
        (sieveCutoff_le_dyadicScale j)
  have hlogX : 0 < log (X : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogXL : log (X : ℝ) ≤ log (L : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using (show (0 : ℝ) < X by positivity))
      (by simpa only [Set.mem_Ioi] using (show (0 : ℝ) < L by positivity))
      (by exact_mod_cast hXL.le)
  have hcut :
      log (L : ℝ) ^ (-(3 / 4 : ℝ)) ≤
        log (X : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hlogX hlogXL (by norm_num)
  have hres :=
    sourceDyadicResidualMoment_le L X Y
  have hbase :=
    sourceScheduledEulerBlockMain_le_product
      (N := N) (K := K) hL hdom hnear
  have hbudgetConst0 : 0 ≤ sourceBudgetConstant K := by
    unfold sourceBudgetConstant
    exact (exp_pos _).le
  have hindex0 :
      0 ≤ (((j + 3 : ℕ) : ℝ) ^
        sourceCanonicalBudgetExponent) :=
    Real.rpow_nonneg (by positivity) _
  have hbudget0 :
      0 ≤ sourceBudgetConstant K *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) := by
    exact mul_nonneg hbudgetConst0 hindex0
  have hprod0 :
      0 ≤ sourceScheduledProductConstant *
        log (X : ℝ) ^ (-(7 / 4 : ℝ)) := by
    exact mul_nonneg sourceScheduledProductConstant_pos.le
      (Real.rpow_nonneg hlogX.le _)
  have hlogLpow0 :
      0 ≤ log (L : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_nonneg hlogL.le _
  have hloss0 :
      0 ≤ scheduledLogLoss j ^ (5 / 2 : ℝ) :=
    Real.rpow_nonneg
      (zero_le_one.trans (scheduledLogLoss_one_le j)) _
  have hpref0 :
      0 ≤
        (sourceBudgetConstant K *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
        (8 * (X : ℝ) ^ 2 *
          (sourceScheduledProductConstant *
            log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ))) := by
    exact mul_nonneg hbudget0
      (mul_nonneg (by positivity)
        (mul_nonneg
          (mul_nonneg hprod0 hlogLpow0)
          hloss0))
  have hlength :
      sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j ≤
        (sourceBudgetConstant K *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
        (8 * (X : ℝ) ^ 2 *
          (sourceScheduledProductConstant *
            log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ))) *
        (Y : ℝ) := by
    exact hbase.trans
      (mul_le_mul_of_nonneg_left hres hpref0)
  have hsqYNat : X ^ 2 * Y ≤ 2 * N := by
    dsimp [X, Y]
    exact dyadic_sq_mul_residualCutoff_le N j
  have hsqY :
      (X : ℝ) ^ 2 * (Y : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hsqYNat
  have hcombine :
      log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
          log (X : ℝ) ^ (-(3 / 4 : ℝ)) =
        log (X : ℝ) ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_add hlogX]
    norm_num
  have hcommon0 :
      0 ≤
        sourceBudgetConstant K *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
          sourceScheduledProductConstant *
          log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hbudget0
          sourceScheduledProductConstant_pos.le)
        (Real.rpow_nonneg hlogX.le _))
      hloss0
  calc
    sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j ≤
      (sourceBudgetConstant K *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
      (8 * (X : ℝ) ^ 2 *
        (sourceScheduledProductConstant *
          log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
          log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ))) *
      (Y : ℝ) := hlength
    _ ≤
      (sourceBudgetConstant K *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
      (8 * (X : ℝ) ^ 2 *
        (sourceScheduledProductConstant *
          log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
          log (X : ℝ) ^ (-(3 / 4 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ))) *
      (Y : ℝ) := by
        have hinner :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcut hprod0) hloss0
        have hsieve :=
          mul_le_mul_of_nonneg_left hinner
            (by positivity : 0 ≤ 8 * (X : ℝ) ^ 2)
        have hbudgeted :=
          mul_le_mul_of_nonneg_left hsieve hbudget0
        exact mul_le_mul_of_nonneg_right hbudgeted
          (Nat.cast_nonneg Y)
    _ =
      (8 *
        sourceBudgetConstant K *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        sourceScheduledProductConstant *
        (log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
          log (X : ℝ) ^ (-(3 / 4 : ℝ))) *
        scheduledLogLoss j ^ (5 / 2 : ℝ)) *
        ((X : ℝ) ^ 2 * (Y : ℝ)) := by ring
    _ ≤
      (8 *
        sourceBudgetConstant K *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        sourceScheduledProductConstant *
        (log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
          log (X : ℝ) ^ (-(3 / 4 : ℝ))) *
        scheduledLogLoss j ^ (5 / 2 : ℝ)) *
        (2 * (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hsqY
      have hpow3 :
          0 ≤ log (X : ℝ) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_nonneg hlogX.le _
      have hnonneg :
          0 ≤ 8 *
            (sourceBudgetConstant K *
              (((j + 3 : ℕ) : ℝ) ^
                sourceCanonicalBudgetExponent) *
              sourceScheduledProductConstant *
              log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
              scheduledLogLoss j ^ (5 / 2 : ℝ)) *
            log (X : ℝ) ^ (-(3 / 4 : ℝ)) :=
        mul_nonneg
          (mul_nonneg (by norm_num) hcommon0) hpow3
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hnonneg
    _ =
      sourceBoundaryRawConstant K * (N : ℝ) *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
        scheduledLogLoss j ^ (5 / 2 : ℝ) := by
      rw [hcombine]
      unfold sourceBoundaryRawConstant
      dsimp [X]
      ring

/-- The three-index transition window `X < L ≤ 8X`, with schedule
dominance recorded for direct use in the Euler estimate. -/
def sourceTransitionIndexSet (L J M : ℕ) : Finset ℕ :=
  (Ico J M).filter fun j ↦
    32 * sieveRadius j ≤ j ∧
      dyadicScale j < L ∧ L ≤ 8 * dyadicScale j

/-- Any two transition indices differ by less than three. -/
theorem sourceTransition_indices_lt_add_three
    {L i j : ℕ}
    (hi : dyadicScale i < L)
    (hnear : L ≤ 8 * dyadicScale j) :
    i < j + 3 := by
  have hpow :
      2 ^ i < 2 ^ (j + 3) := by
    calc
      2 ^ i = dyadicScale i := by rfl
      _ < L := hi
      _ ≤ 8 * dyadicScale j := hnear
      _ = 2 ^ (j + 3) := by
        simp [dyadicScale, pow_add]
        ring
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow

/-- The transition really consists of at most three dyadic blocks,
uniformly in all cutoffs and endpoints. -/
theorem card_sourceTransitionIndexSet_le_three
    (L J M : ℕ) :
    (sourceTransitionIndexSet L J M).card ≤ 3 := by
  let s := sourceTransitionIndexSet L J M
  by_cases hs : s.Nonempty
  · let i := s.min' hs
    have hsubset : s ⊆ Ico i (i + 3) := by
      intro j hj
      have hiMem : i ∈ s := Finset.min'_mem s hs
      have hij : i ≤ j := Finset.min'_le s j hj
      dsimp [s] at hiMem hj
      rw [sourceTransitionIndexSet, mem_filter] at hiMem hj
      exact mem_Ico.mpr
        ⟨hij,
          sourceTransition_indices_lt_add_three
            hj.2.2.1 hiMem.2.2.2⟩
    have hcard := Finset.card_le_card hsubset
    simpa [s] using hcard
  · have hs0 : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp [s, hs0]

/-- Constant converting a scheduled index expression with dyadic
logarithmic power `-r` into a power-log profile in `j+1`. -/
def sourceScheduledIndexProfileConstant (r : ℝ) : ℝ :=
  (3 : ℝ) ^ sourceCanonicalBudgetExponent *
    (2 : ℝ) ^ r * log (2 : ℝ) ^ (-r) *
    scheduledLogLossConstant ^ (5 / 2 : ℝ)

theorem sourceScheduledIndexProfileConstant_pos (r : ℝ) :
    0 < sourceScheduledIndexProfileConstant r := by
  unfold sourceScheduledIndexProfileConstant
  positivity [scheduledLogLossConstant_pos,
    Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- Uniform conversion of the scheduled source index losses to a single
power-log profile. -/
theorem sourceScheduledIndexProfile_le
    {j : ℕ} {r : ℝ} (hj : 1 ≤ j) (hr : 0 ≤ r) :
    (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        log (dyadicScale j : ℝ) ^ (-r) *
        scheduledLogLoss j ^ (5 / 2 : ℝ) ≤
      sourceScheduledIndexProfileConstant r *
        (((j + 1 : ℕ) : ℝ) ^
          (sourceCanonicalBudgetExponent - r)) *
        log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) := by
  have hjreal : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hj1real : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hlogTwo : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hbudgetExp : 0 ≤ sourceCanonicalBudgetExponent := by
    unfold sourceCanonicalBudgetExponent
    positivity [sourceAnatomySlope_nonneg]
  have hindexNat : j + 3 ≤ 3 * (j + 1) := by omega
  have hindex :
      (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) ≤
        (3 : ℝ) ^ sourceCanonicalBudgetExponent *
          (((j + 1 : ℕ) : ℝ) ^
            sourceCanonicalBudgetExponent) := by
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
      (j : ℝ) ^ (-r) ≤
        (2 : ℝ) ^ r *
          (((j + 1 : ℕ) : ℝ) ^ (-r)) :=
    rpow_neg_le_ratio_rpow hj1real hjreal
      (by norm_num) hr hratio
  have hlogScale :
      log (dyadicScale j : ℝ) ^ (-r) ≤
        ((2 : ℝ) ^ r *
          (((j + 1 : ℕ) : ℝ) ^ (-r))) *
        log (2 : ℝ) ^ (-r) := by
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
  have hindex0 :
      0 ≤ (3 : ℝ) ^ sourceCanonicalBudgetExponent *
        (((j + 1 : ℕ) : ℝ) ^
          sourceCanonicalBudgetExponent) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hj1real.le _)
  have hscale0 :
      0 ≤ ((2 : ℝ) ^ r *
          (((j + 1 : ℕ) : ℝ) ^ (-r))) *
        log (2 : ℝ) ^ (-r) :=
    mul_nonneg
      (mul_nonneg
        (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg hj1real.le _))
      (Real.rpow_nonneg hlogTwo.le _)
  have hloss0 :
      0 ≤ scheduledLogLoss j ^ (5 / 2 : ℝ) :=
    Real.rpow_nonneg
      (zero_le_one.trans (scheduledLogLoss_one_le j)) _
  calc
    (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-r) *
          scheduledLogLoss j ^ (5 / 2 : ℝ)
        ≤
      ((3 : ℝ) ^ sourceCanonicalBudgetExponent *
          (((j + 1 : ℕ) : ℝ) ^
            sourceCanonicalBudgetExponent)) *
        (((2 : ℝ) ^ r *
            (((j + 1 : ℕ) : ℝ) ^ (-r))) *
          log (2 : ℝ) ^ (-r)) *
        (scheduledLogLossConstant ^ (5 / 2 : ℝ) *
          log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)) := by
      calc
        (((j + 3 : ℕ) : ℝ) ^
              sourceCanonicalBudgetExponent) *
            log (dyadicScale j : ℝ) ^ (-r) *
            scheduledLogLoss j ^ (5 / 2 : ℝ)
            ≤
          ((3 : ℝ) ^ sourceCanonicalBudgetExponent *
              (((j + 1 : ℕ) : ℝ) ^
                sourceCanonicalBudgetExponent)) *
            log (dyadicScale j : ℝ) ^ (-r) *
            scheduledLogLoss j ^ (5 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hindex
              (Real.rpow_nonneg (by positivity) _))
            hloss0
        _ ≤
          ((3 : ℝ) ^ sourceCanonicalBudgetExponent *
              (((j + 1 : ℕ) : ℝ) ^
                sourceCanonicalBudgetExponent)) *
            (((2 : ℝ) ^ r *
                (((j + 1 : ℕ) : ℝ) ^ (-r))) *
              log (2 : ℝ) ^ (-r)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogScale hindex0)
            hloss0
        _ ≤ _ :=
          mul_le_mul_of_nonneg_left hloss'
            (mul_nonneg hindex0 hscale0)
    _ =
      sourceScheduledIndexProfileConstant r *
        (((j + 1 : ℕ) : ℝ) ^
          (sourceCanonicalBudgetExponent - r)) *
        log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) := by
      unfold sourceScheduledIndexProfileConstant
      rw [show
          sourceCanonicalBudgetExponent - r =
            sourceCanonicalBudgetExponent + (-r) by ring,
        Real.rpow_add hj1real]
      ring

/-- A slightly weakened transition exponent after absorbing the five
powers of `log(j+1)`. -/
def sourceTransitionAbsorbedExponent : ℝ :=
  (sourceBulkPowerExponent - 1) / 2

/-- Positive power used to absorb the schedule logarithms. -/
def sourceTransitionLogAbsorption : ℝ :=
  sourceTransitionAbsorbedExponent - sourceBulkPowerExponent

theorem sourceTransitionLogAbsorption_pos :
    0 < sourceTransitionLogAbsorption := by
  unfold sourceTransitionLogAbsorption
    sourceTransitionAbsorbedExponent
  linarith [sourceBulkPowerExponent_lt_neg_one]

theorem sourceTransitionAbsorbedExponent_lt_neg_one :
    sourceTransitionAbsorbedExponent < -1 := by
  unfold sourceTransitionAbsorbedExponent
  linarith [sourceBulkPowerExponent_lt_neg_one]

/-- Once the schedule logarithm has been absorbed, a transition index is
bounded directly by a negative power of `log L`. -/
theorem sourceTransitionIndexProfile_le_logCutoff
    {L j : ℕ}
    (hL : 3 ≤ L) (hj : 1 ≤ j)
    (hnear : L ≤ 8 * dyadicScale j)
    (hloss :
      log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) ≤
        (((j + 1 : ℕ) : ℝ) ^
          sourceTransitionLogAbsorption)) :
    (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
        scheduledLogLoss j ^ (5 / 2 : ℝ) ≤
      sourceScheduledIndexProfileConstant (5 / 2 : ℝ) *
        (3 * log (2 : ℝ)) ^
          (-sourceTransitionAbsorbedExponent) *
        log (L : ℝ) ^ sourceTransitionAbsorbedExponent := by
  have hprofile :=
    sourceScheduledIndexProfile_le
      (j := j) (r := (5 / 2 : ℝ)) hj (by norm_num)
  have hj1 : 0 < (((j + 1 : ℕ) : ℝ)) := by positivity
  have hp0 : sourceBulkPowerExponent < 0 :=
    sourceBulkPowerExponent_lt_neg_one.trans (by norm_num)
  have hδ0 := sourceTransitionLogAbsorption_pos
  have hcombine :
      (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
          (((j + 1 : ℕ) : ℝ) ^
            sourceTransitionLogAbsorption) =
        (((j + 1 : ℕ) : ℝ) ^
          sourceTransitionAbsorbedExponent) := by
    rw [← Real.rpow_add hj1]
    unfold sourceTransitionLogAbsorption
    ring_nf
  have hlogTwo : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hscale :
      8 * dyadicScale j = 2 ^ (j + 3) := by
    simp [dyadicScale, pow_add]
    ring
  have hlogScale :
      log (8 * (dyadicScale j : ℝ)) =
        (((j + 3 : ℕ) : ℝ)) * log 2 := by
    have hscaleReal :
        (8 : ℝ) * (dyadicScale j : ℝ) =
          ((2 ^ (j + 3) : ℕ) : ℝ) := by
      exact_mod_cast hscale
    rw [hscaleReal]
    simp [Real.log_pow]
  have hlogNear :
      log (L : ℝ) ≤
        (((j + 3 : ℕ) : ℝ)) * log 2 := by
    rw [← hlogScale]
    exact Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using (show (0 : ℝ) < L by positivity))
      (by
        simpa only [Set.mem_Ioi] using
          (mul_pos (by norm_num : (0 : ℝ) < 8)
            (by exact_mod_cast dyadicScale_pos j)))
      (by exact_mod_cast hnear)
  have hthree :
      (((j + 3 : ℕ) : ℝ)) ≤
        3 * (((j + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show j + 3 ≤ 3 * (j + 1) by omega)
  have hbase :
      log (L : ℝ) / (3 * log (2 : ℝ)) ≤
        (((j + 1 : ℕ) : ℝ)) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hlogTwo)).2
    calc
      log (L : ℝ) ≤
          (((j + 3 : ℕ) : ℝ)) * log 2 := hlogNear
      _ ≤
          (3 * (((j + 1 : ℕ) : ℝ))) * log 2 :=
        mul_le_mul_of_nonneg_right hthree hlogTwo.le
      _ = (((j + 1 : ℕ) : ℝ)) *
          (3 * log (2 : ℝ)) := by ring
  have hbasePos :
      0 < log (L : ℝ) / (3 * log (2 : ℝ)) := by positivity
  have hpow :
      (((j + 1 : ℕ) : ℝ) ^
          sourceTransitionAbsorbedExponent) ≤
        (log (L : ℝ) / (3 * log (2 : ℝ))) ^
          sourceTransitionAbsorbedExponent :=
    Real.rpow_le_rpow_of_nonpos hbasePos hbase
      (by
        linarith [sourceTransitionAbsorbedExponent_lt_neg_one])
  have hsplit :
      (log (L : ℝ) / (3 * log (2 : ℝ))) ^
          sourceTransitionAbsorbedExponent =
        (3 * log (2 : ℝ)) ^
            (-sourceTransitionAbsorbedExponent) *
          log (L : ℝ) ^
            sourceTransitionAbsorbedExponent := by
    rw [Real.div_rpow hlogL.le
      (mul_pos (by norm_num) hlogTwo).le,
      Real.rpow_neg (mul_pos (by norm_num) hlogTwo).le]
    ring
  have hC0 :
      0 ≤ sourceScheduledIndexProfileConstant (5 / 2 : ℝ) :=
    (sourceScheduledIndexProfileConstant_pos _).le
  calc
    (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ)
        ≤
      sourceScheduledIndexProfileConstant (5 / 2 : ℝ) *
        (((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
        log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) := by
      simpa [sourceBulkPowerExponent] using hprofile
    _ ≤
      sourceScheduledIndexProfileConstant (5 / 2 : ℝ) *
        ((((j + 1 : ℕ) : ℝ) ^ sourceBulkPowerExponent) *
          (((j + 1 : ℕ) : ℝ) ^
            sourceTransitionLogAbsorption)) := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hloss
            (Real.rpow_nonneg hj1.le
              sourceBulkPowerExponent)) hC0)
    _ =
      sourceScheduledIndexProfileConstant (5 / 2 : ℝ) *
        (((j + 1 : ℕ) : ℝ) ^
          sourceTransitionAbsorbedExponent) := by rw [hcombine]
    _ ≤
      sourceScheduledIndexProfileConstant (5 / 2 : ℝ) *
        (log (L : ℝ) / (3 * log (2 : ℝ))) ^
          sourceTransitionAbsorbedExponent :=
      mul_le_mul_of_nonneg_left hpow hC0
    _ =
      sourceScheduledIndexProfileConstant (5 / 2 : ℝ) *
        (3 * log (2 : ℝ)) ^
          (-sourceTransitionAbsorbedExponent) *
        log (L : ℝ) ^ sourceTransitionAbsorbedExponent := by
      rw [hsplit]
      ring

/-- Sum form of the exact-length transition estimate.  The summand on
the right is the universal source power-log profile before converting
`log(2^j)` to `j log 2`. -/
theorem sum_sourceEulerMain_transition_le_raw
    {L N J M : ℕ} {K : ℝ} (hL : 3 ≤ L) :
    (∑ j ∈ sourceTransitionIndexSet L J M,
      sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j) ≤
      sourceBoundaryRawConstant K * (N : ℝ) *
        (∑ j ∈ sourceTransitionIndexSet L J M,
          (((j + 3 : ℕ) : ℝ) ^
              sourceCanonicalBudgetExponent) *
            log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ)) := by
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  rw [sourceTransitionIndexSet, mem_filter] at hj
  simpa [mul_assoc] using
    (sourceScheduledEulerBlockMain_le_boundary_raw
      (N := N) (K := K) hL hj.2.1 hj.2.2.1 hj.2.2.2)

/-- Constant in the final transition comparison with rough density. -/
def sourceTransitionAsymptoticConstant (K : ℝ) : ℝ :=
  3 * sourceBoundaryRawConstant K *
    sourceScheduledIndexProfileConstant (5 / 2 : ℝ) *
    (3 * log (2 : ℝ)) ^
      (-sourceTransitionAbsorbedExponent)

theorem sourceTransitionAsymptoticConstant_pos (K : ℝ) :
    0 < sourceTransitionAsymptoticConstant K := by
  unfold sourceTransitionAsymptoticConstant
  exact mul_pos
    (mul_pos
      (mul_pos (by norm_num)
        (sourceBoundaryRawConstant_pos K))
      (sourceScheduledIndexProfileConstant_pos _))
    (Real.rpow_pos_of_pos
      (mul_pos (by norm_num)
        (Real.log_pos (by norm_num : (1 : ℝ) < 2))) _)

/-- Uniformly in `N` and in the summation endpoints, the entire
three-block transition range is eventually below its allotted rough
density budget. -/
theorem eventually_sum_sourceEulerMain_transition_le_roughDensity
    (K : ℝ) :
    ∀ᶠ L : ℕ in atTop,
      ∀ N J M : ℕ,
        (∑ j ∈ sourceTransitionIndexSet L J M,
          sourceScheduledEulerBlockMain
            L N sourceAnatomySlope K j) ≤
          (N : ℝ) * Erdos327.roughDensity L / 64 := by
  have habsEventually :=
    eventually_log_add_one_rpow_le_rpow
      (5 : ℝ) sourceTransitionLogAbsorption_pos
  rcases (eventually_atTop.1 habsEventually) with ⟨J₀, hJ₀⟩
  let JT : ℕ := max J₀ 1
  have hη :
      1 < -sourceTransitionAbsorbedExponent := by
    linarith [sourceTransitionAbsorbedExponent_lt_neg_one]
  have hasymptotic :=
    eventually_const_mul_log_rpow_neg_mul_loglog_rpow_le_roughDensity
      (C := sourceTransitionAsymptoticConstant K)
      (D := 64)
      (η := -sourceTransitionAbsorbedExponent)
      (m := 0)
      (sourceTransitionAsymptoticConstant_pos K).le
      (by norm_num)
      hη
  have hasymptotic' :
      ∀ᶠ L : ℕ in atTop,
        sourceTransitionAsymptoticConstant K *
            log (L : ℝ) ^
              sourceTransitionAbsorbedExponent ≤
          Erdos327.roughDensity L / 64 := by
    filter_upwards [hasymptotic, eventually_ge_atTop 3] with L hL hL3
    have hloglog0 :
        log (log (L : ℝ)) ^ (0 : ℝ) = 1 := by
      rw [Real.rpow_zero]
    simpa [hloglog0] using hL
  have hcutoff :
      ∀ᶠ L : ℕ in atTop, 8 * dyadicScale JT < L :=
    eventually_gt_atTop (8 * dyadicScale JT)
  filter_upwards
    [hasymptotic', hcutoff, eventually_ge_atTop 3] with
      L hasym hfar hL
  intro N J M
  let s := sourceTransitionIndexSet L J M
  let B : ℝ :=
    sourceScheduledIndexProfileConstant (5 / 2 : ℝ) *
      (3 * log (2 : ℝ)) ^
        (-sourceTransitionAbsorbedExponent) *
      log (L : ℝ) ^ sourceTransitionAbsorbedExponent
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg
        (sourceScheduledIndexProfileConstant_pos _).le
        (Real.rpow_nonneg
          (mul_nonneg (by norm_num)
            (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le) _))
      (Real.rpow_nonneg
        (Real.log_pos
          (by exact_mod_cast (show 1 < L by omega))).le _)
  have hpoint :
      ∀ j ∈ s,
        (((j + 3 : ℕ) : ℝ) ^
            sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ) ≤ B := by
    intro j hj
    have hj' := hj
    dsimp [s] at hj'
    rw [sourceTransitionIndexSet, mem_filter] at hj'
    have hJTj : JT < j := by
      by_contra hnot
      have hjJT : j ≤ JT := Nat.le_of_not_gt hnot
      have hmono := dyadicScale_mono hjJT
      have : L ≤ 8 * dyadicScale JT :=
        hj'.2.2.2.trans (Nat.mul_le_mul_left 8 hmono)
      omega
    have hj1 : 1 ≤ j := by
      have : 1 ≤ JT := le_max_right J₀ 1
      omega
    have hjJ₀ : J₀ ≤ j := by
      have : J₀ ≤ JT := le_max_left J₀ 1
      omega
    exact sourceTransitionIndexProfile_le_logCutoff
      hL hj1 hj'.2.2.2 (hJ₀ j hjJ₀)
  have hsumCard :
      (∑ j ∈ s,
        (((j + 3 : ℕ) : ℝ) ^
            sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ)) ≤
        s.card • B :=
    Finset.sum_le_card_nsmul s _ B hpoint
  have hcard : s.card ≤ 3 := by
    dsimp [s]
    exact card_sourceTransitionIndexSet_le_three L J M
  have hsum :
      (∑ j ∈ s,
        (((j + 3 : ℕ) : ℝ) ^
            sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ)) ≤
        3 * B := by
    calc
      _ ≤ s.card • B := hsumCard
      _ = (s.card : ℝ) * B := by simp
      _ ≤ 3 * B :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast hcard) hB0
  have hraw :=
    sum_sourceEulerMain_transition_le_raw
      (L := L) (N := N) (J := J) (M := M)
      (K := K) hL
  have hfactor0 :
      0 ≤ sourceBoundaryRawConstant K * (N : ℝ) :=
    mul_nonneg (sourceBoundaryRawConstant_pos K).le
      (Nat.cast_nonneg N)
  calc
    (∑ j ∈ sourceTransitionIndexSet L J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j)
        ≤ sourceBoundaryRawConstant K * (N : ℝ) *
          (∑ j ∈ sourceTransitionIndexSet L J M,
            (((j + 3 : ℕ) : ℝ) ^
                sourceCanonicalBudgetExponent) *
              log (dyadicScale j : ℝ) ^ (-(5 / 2 : ℝ)) *
              scheduledLogLoss j ^ (5 / 2 : ℝ)) := hraw
    _ ≤ sourceBoundaryRawConstant K * (N : ℝ) *
          (3 * B) :=
      mul_le_mul_of_nonneg_left hsum hfactor0
    _ = (N : ℝ) *
          (sourceTransitionAsymptoticConstant K *
            log (L : ℝ) ^
              sourceTransitionAbsorbedExponent) := by
      unfold sourceTransitionAsymptoticConstant
      dsimp [B]
      ring
    _ ≤ (N : ℝ) *
          (Erdos327.roughDensity L / 64) :=
      mul_le_mul_of_nonneg_left hasym (Nat.cast_nonneg N)
    _ = (N : ℝ) * Erdos327.roughDensity L / 64 := by ring

/-! ## Small residual range -/

/-- Raw coefficient when the residual length, rather than a normalized
residual Mertens estimate, is used. -/
def sourceSmallResidualRawConstant (K : ℝ) : ℝ :=
  16 * sourceBudgetConstant K * sourceScheduledProductConstant

theorem sourceSmallResidualRawConstant_pos (K : ℝ) :
    0 < sourceSmallResidualRawConstant K := by
  unfold sourceSmallResidualRawConstant sourceBudgetConstant
  positivity [sourceScheduledProductConstant_pos]

/-- Exact residual length bound, retaining the separate cutoff powers.
This is the pointwise input for the fixed-`L` small-residual argument. -/
theorem sourceScheduledEulerBlockMain_le_smallResidual_raw
    {L N j : ℕ} {K : ℝ}
    (hL : 3 ≤ L)
    (hdom : 32 * sieveRadius j ≤ j)
    (hnear : L ≤ 8 * dyadicScale j) :
    sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j ≤
      sourceSmallResidualRawConstant K * (N : ℝ) *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
        log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
        scheduledLogLoss j ^ (5 / 2 : ℝ) := by
  let X : ℕ := dyadicScale j
  let Y : ℕ := 2 * N / X ^ 2
  have hbase :=
    sourceScheduledEulerBlockMain_le_product
      (N := N) (K := K) hL hdom hnear
  have hres := sourceDyadicResidualMoment_le L X Y
  have hX2 : 2 ≤ X := by
    dsimp [X]
    exact
      (two_le_sieveCutoff_of_dominance hdom).trans
        (sieveCutoff_le_dyadicScale j)
  have hlogX : 0 < log (X : ℝ) := by
    apply log_pos
    exact_mod_cast (show 1 < X by omega)
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hbudget0 :
      0 ≤ sourceBudgetConstant K *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) := by
    exact mul_nonneg
      (by unfold sourceBudgetConstant; exact (exp_pos _).le)
      (Real.rpow_nonneg (by positivity) _)
  have hsieveFactors0 :
      0 ≤ sourceScheduledProductConstant *
          log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
          log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg sourceScheduledProductConstant_pos.le
          (Real.rpow_nonneg hlogX.le _))
        (Real.rpow_nonneg hlogL.le _))
      (Real.rpow_nonneg
        (zero_le_one.trans (scheduledLogLoss_one_le j)) _)
  have hpref0 :
      0 ≤
        (sourceBudgetConstant K *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
        (8 * (X : ℝ) ^ 2 *
          (sourceScheduledProductConstant *
            log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ))) :=
    mul_nonneg hbudget0
      (mul_nonneg (by positivity) hsieveFactors0)
  have hlength :
      sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j ≤
        (sourceBudgetConstant K *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
        (8 * (X : ℝ) ^ 2 *
          (sourceScheduledProductConstant *
            log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ))) *
        (Y : ℝ) :=
    hbase.trans (mul_le_mul_of_nonneg_left hres hpref0)
  have hsqYNat : X ^ 2 * Y ≤ 2 * N := by
    dsimp [X, Y]
    exact dyadic_sq_mul_residualCutoff_le N j
  have hsqY :
      (X : ℝ) ^ 2 * (Y : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hsqYNat
  calc
    sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j ≤
      (sourceBudgetConstant K *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
      (8 * (X : ℝ) ^ 2 *
        (sourceScheduledProductConstant *
          log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
          log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ))) *
      (Y : ℝ) := hlength
    _ =
      (8 * sourceBudgetConstant K *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        sourceScheduledProductConstant *
        log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
        log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
        scheduledLogLoss j ^ (5 / 2 : ℝ)) *
        ((X : ℝ) ^ 2 * (Y : ℝ)) := by ring
    _ ≤
      (8 * sourceBudgetConstant K *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        sourceScheduledProductConstant *
        log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
        log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
        scheduledLogLoss j ^ (5 / 2 : ℝ)) *
        (2 * (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hsqY
      have hcoef0 :
          0 ≤ 8 *
            (sourceBudgetConstant K *
              (((j + 3 : ℕ) : ℝ) ^
                sourceCanonicalBudgetExponent)) *
            (sourceScheduledProductConstant *
              log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
              log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
              scheduledLogLoss j ^ (5 / 2 : ℝ)) :=
        mul_nonneg (mul_nonneg (by norm_num) hbudget0)
          hsieveFactors0
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hcoef0
    _ =
      sourceSmallResidualRawConstant K * (N : ℝ) *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
        log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
        scheduledLogLoss j ^ (5 / 2 : ℝ) := by
      unfold sourceSmallResidualRawConstant
      dsimp [X]
      ring

/-- Indices whose exact residual interval is nonempty but shorter than
the fixed roughness cutoff. -/
def sourceSmallResidualIndexSet
    (L N J M : ℕ) : Finset ℕ :=
  (Ico J M).filter fun j ↦
    32 * sieveRadius j ≤ j ∧
      L ≤ dyadicScale j ∧
      0 < 2 * N / dyadicScale j ^ 2 ∧
      2 * N / dyadicScale j ^ 2 < L

/-- Sum form of the small-residual exact-length estimate. -/
theorem sum_sourceEulerMain_smallResidual_le_raw
    {L N J M : ℕ} {K : ℝ} (hL : 3 ≤ L) :
    (∑ j ∈ sourceSmallResidualIndexSet L N J M,
      sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j) ≤
      sourceSmallResidualRawConstant K * (N : ℝ) *
        log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
        (∑ j ∈ sourceSmallResidualIndexSet L N J M,
          (((j + 3 : ℕ) : ℝ) ^
              sourceCanonicalBudgetExponent) *
            log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ)) := by
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  rw [sourceSmallResidualIndexSet, mem_filter] at hj
  have hnear : L ≤ 8 * dyadicScale j :=
    hj.2.2.1.trans (by omega)
  have hpoint :=
    sourceScheduledEulerBlockMain_le_smallResidual_raw
      (N := N) (K := K) hL hj.2.1 hnear
  calc
    sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j ≤
      sourceSmallResidualRawConstant K * (N : ℝ) *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) *
        log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
        log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
        scheduledLogLoss j ^ (5 / 2 : ℝ) := hpoint
    _ =
      sourceSmallResidualRawConstant K * (N : ℝ) *
        log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
        ((((j + 3 : ℕ) : ℝ) ^
            sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ)) := by ring

/-- Once `N` dominates one fixed dyadic scale, every earlier residual
cutoff is at least `L`.  Thus small-residual indices escape every fixed
prefix as `N → ∞`. -/
theorem sourceResidualCutoff_ge_of_index_le
    {L N i J : ℕ}
    (hiJ : i ≤ J)
    (hN : L * dyadicScale J ^ 2 ≤ N) :
    L ≤ 2 * N / dyadicScale i ^ 2 := by
  have hscale : dyadicScale i ≤ dyadicScale J :=
    dyadicScale_mono hiJ
  have hsq : dyadicScale i ^ 2 ≤ dyadicScale J ^ 2 :=
    Nat.pow_le_pow_left hscale 2
  have hmul :
      L * dyadicScale i ^ 2 ≤ 2 * N := by
    calc
      L * dyadicScale i ^ 2 ≤
          L * dyadicScale J ^ 2 :=
        Nat.mul_le_mul_left L hsq
      _ ≤ N := hN
      _ ≤ 2 * N := by omega
  exact
    (Nat.le_div_iff_mul_le
      (Nat.pow_pos (dyadicScale_pos i))).2 hmul

/-- Membership in the positive small-residual range forces the dyadic
index past any fixed scale already dominated by `N`. -/
theorem index_gt_of_smallResidual_of_large_N
    {L N i J : ℕ}
    (hsmall : 2 * N / dyadicScale i ^ 2 < L)
    (hN : L * dyadicScale J ^ 2 ≤ N) :
    J < i := by
  by_contra hnot
  have hiJ : i ≤ J := Nat.le_of_not_gt hnot
  exact (Nat.not_le_of_gt hsmall)
    (sourceResidualCutoff_ge_of_index_le hiJ hN)

/-- Along positive residual cutoffs, increasing the dyadic index strictly
decreases the residual interval length. -/
theorem sourceResidualCutoff_strictAnti
    {N i j : ℕ}
    (hij : i < j)
    (hi : 0 < 2 * N / dyadicScale i ^ 2) :
    2 * N / dyadicScale j ^ 2 <
      2 * N / dyadicScale i ^ 2 := by
  have hsucc : i + 1 ≤ j := by omega
  have hscale :
      2 * dyadicScale i ≤ dyadicScale j := by
    have hmono := dyadicScale_mono hsucc
    simpa [dyadicScale, pow_succ, mul_comm, mul_left_comm,
      mul_assoc] using hmono
  have hden :
      4 * dyadicScale i ^ 2 ≤ dyadicScale j ^ 2 := by
    calc
      4 * dyadicScale i ^ 2 =
          (2 * dyadicScale i) ^ 2 := by ring
      _ ≤ dyadicScale j ^ 2 := Nat.pow_le_pow_left hscale 2
  have hdenPos : 0 < 4 * dyadicScale i ^ 2 :=
    Nat.mul_pos (by norm_num) (Nat.pow_pos (dyadicScale_pos i))
  have hfirst :
      2 * N / dyadicScale j ^ 2 ≤
        2 * N / (4 * dyadicScale i ^ 2) :=
    Nat.div_le_div_left hden hdenPos
  have heq :
      2 * N / (4 * dyadicScale i ^ 2) =
        (2 * N / dyadicScale i ^ 2) / 4 := by
    rw [Nat.div_div_eq_div_mul]
    congr 1
    ring
  calc
    2 * N / dyadicScale j ^ 2 ≤
        2 * N / (4 * dyadicScale i ^ 2) := hfirst
    _ = (2 * N / dyadicScale i ^ 2) / 4 := heq
    _ < 2 * N / dyadicScale i ^ 2 :=
      Nat.div_lt_self hi (by norm_num)

/-- There are at most `L` positive small-residual dyadic blocks.  The
proof injects indices into their distinct residual lengths
`1, …, L-1`. -/
theorem card_sourceSmallResidualIndexSet_le
    (L N J M : ℕ) :
    (sourceSmallResidualIndexSet L N J M).card ≤ L := by
  let s := sourceSmallResidualIndexSet L N J M
  let f : ℕ → ℕ := fun j ↦ 2 * N / dyadicScale j ^ 2
  have hinj : Set.InjOn f s := by
    intro i hi j hj heq
    by_contra hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hi' : 0 < f i := by
        have hiFin : i ∈ s := hi
        dsimp [s] at hiFin
        rw [sourceSmallResidualIndexSet, mem_filter] at hiFin
        exact hiFin.2.2.2.1
      have hstrict :=
        sourceResidualCutoff_strictAnti hijlt hi'
      exact (Nat.ne_of_lt hstrict) heq.symm
    · have hj' : 0 < f j := by
        have hjFin : j ∈ s := hj
        dsimp [s] at hjFin
        rw [sourceSmallResidualIndexSet, mem_filter] at hjFin
        exact hjFin.2.2.2.1
      have hstrict :=
        sourceResidualCutoff_strictAnti hjilt hj'
      exact (Nat.ne_of_lt hstrict) heq
  have hsubset : s.image f ⊆ Ico 1 L := by
    intro y hy
    rw [mem_image] at hy
    rcases hy with ⟨j, hj, rfl⟩
    dsimp [s] at hj
    rw [sourceSmallResidualIndexSet, mem_filter] at hj
    exact mem_Ico.mpr ⟨hj.2.2.2.1, hj.2.2.2.2⟩
  calc
    s.card = (s.image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Ico 1 L).card := Finset.card_le_card hsubset
    _ ≤ L := by simp

/-- The remaining dyadic power in the small-residual profile is
strictly negative. -/
def sourceSmallResidualPowerExponent : ℝ :=
  sourceCanonicalBudgetExponent - 7 / 4

theorem sourceSmallResidualPowerExponent_lt_zero :
    sourceSmallResidualPowerExponent < 0 := by
  unfold sourceSmallResidualPowerExponent
  linarith [sourceCanonicalBudgetExponent_lt_three_halves]

/-- The power-log profile left by the exact-length small-residual bound
tends to zero. -/
theorem tendsto_sourceSmallResidualPowerLog :
    Tendsto
      (fun j : ℕ ↦
        (((j + 1 : ℕ) : ℝ) ^
          sourceSmallResidualPowerExponent) *
        log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ))
      atTop (𝓝 0) := by
  have hη : 0 < -sourceSmallResidualPowerExponent := by
    linarith [sourceSmallResidualPowerExponent_lt_zero]
  have ht :=
    tendsto_rpow_neg_mul_log_rpow_atTop hη (5 : ℝ)
  have hcast :
      Tendsto (fun j : ℕ ↦ (((j + 1 : ℕ) : ℝ)))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_add_atTop_nat 1)
  refine (ht.comp hcast).congr' ?_
  filter_upwards with j
  norm_num

/-- For fixed `L` and `K`, the complete positive small-residual range is
`o(N)`, uniformly in the finite summation endpoints. -/
theorem eventually_sum_sourceEulerMain_smallResidual_le
    (L : ℕ) (K : ℝ) (hL : 3 ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ J M : ℕ,
        (∑ j ∈ sourceSmallResidualIndexSet L N J M,
          sourceScheduledEulerBlockMain
            L N sourceAnatomySlope K j) ≤
          ε * (N : ℝ) := by
  let C : ℝ :=
    sourceSmallResidualRawConstant K *
      log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
      (L : ℝ) *
      sourceScheduledIndexProfileConstant (7 / 4 : ℝ)
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos
      (mul_pos
        (mul_pos (sourceSmallResidualRawConstant_pos K)
          (Real.rpow_pos_of_pos hlogL _))
        (by exact_mod_cast (show 0 < L by omega)))
      (sourceScheduledIndexProfileConstant_pos _)
  have hsmall :
      ∀ᶠ j : ℕ in atTop,
        (((j + 1 : ℕ) : ℝ) ^
            sourceSmallResidualPowerExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ) <
            ε / C :=
    (tendsto_order.1 tendsto_sourceSmallResidualPowerLog).2
      (ε / C) (div_pos hε hC)
  rcases (eventually_atTop.1 hsmall) with ⟨J₀, hJ₀⟩
  filter_upwards
    [eventually_ge_atTop (L * dyadicScale J₀ ^ 2)] with N hN
  intro J M
  let s := sourceSmallResidualIndexSet L N J M
  let g : ℕ → ℝ := fun j ↦
    (((j + 1 : ℕ) : ℝ) ^
      sourceSmallResidualPowerExponent) *
      log (((j + 1 : ℕ) : ℝ)) ^ (5 : ℝ)
  have hindex :
      ∀ j ∈ s,
        (((j + 3 : ℕ) : ℝ) ^
            sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ) ≤
        sourceScheduledIndexProfileConstant (7 / 4 : ℝ) *
          g j := by
    intro j hj
    have hj' := hj
    dsimp [s] at hj'
    rw [sourceSmallResidualIndexSet, mem_filter] at hj'
    have hjJ₀ :
        J₀ < j :=
      index_gt_of_smallResidual_of_large_N
        hj'.2.2.2.2 hN
    have hj1 : 1 ≤ j := by omega
    simpa only [g, sourceSmallResidualPowerExponent, mul_assoc] using
      (sourceScheduledIndexProfile_le
        (j := j) (r := (7 / 4 : ℝ)) hj1 (by norm_num))
  have hgtail :
      ∀ j ∈ s, g j ≤ ε / C := by
    intro j hj
    have hj' := hj
    dsimp [s] at hj'
    rw [sourceSmallResidualIndexSet, mem_filter] at hj'
    have hjJ₀ :
        J₀ < j :=
      index_gt_of_smallResidual_of_large_N
        hj'.2.2.2.2 hN
    exact (hJ₀ j hjJ₀.le).le
  have hprofilePoint :
      ∀ j ∈ s,
        (((j + 3 : ℕ) : ℝ) ^
            sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ) ≤
        sourceScheduledIndexProfileConstant (7 / 4 : ℝ) *
          (ε / C) := by
    intro j hj
    exact (hindex j hj).trans
      (mul_le_mul_of_nonneg_left (hgtail j hj)
        (sourceScheduledIndexProfileConstant_pos _).le)
  have hsumCard :=
    Finset.sum_le_card_nsmul s _
      (sourceScheduledIndexProfileConstant (7 / 4 : ℝ) *
        (ε / C)) hprofilePoint
  have hcard : s.card ≤ L := by
    dsimp [s]
    exact card_sourceSmallResidualIndexSet_le L N J M
  have htarget0 :
      0 ≤ sourceScheduledIndexProfileConstant (7 / 4 : ℝ) *
        (ε / C) :=
    mul_nonneg
      (sourceScheduledIndexProfileConstant_pos _).le
      (div_nonneg hε.le hC.le)
  have hsum :
      (∑ j ∈ s,
        (((j + 3 : ℕ) : ℝ) ^
            sourceCanonicalBudgetExponent) *
          log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ)) ≤
        (L : ℝ) *
          (sourceScheduledIndexProfileConstant (7 / 4 : ℝ) *
            (ε / C)) := by
    calc
      _ ≤ s.card •
          (sourceScheduledIndexProfileConstant (7 / 4 : ℝ) *
            (ε / C)) := hsumCard
      _ = (s.card : ℝ) *
          (sourceScheduledIndexProfileConstant (7 / 4 : ℝ) *
            (ε / C)) := by simp
      _ ≤ (L : ℝ) *
          (sourceScheduledIndexProfileConstant (7 / 4 : ℝ) *
            (ε / C)) :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast hcard) htarget0
  have hraw :=
    sum_sourceEulerMain_smallResidual_le_raw
      (L := L) (N := N) (J := J) (M := M)
      (K := K) hL
  have houter0 :
      0 ≤ sourceSmallResidualRawConstant K * (N : ℝ) *
        log (L : ℝ) ^ (-(3 / 4 : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg (sourceSmallResidualRawConstant_pos K).le
        (Nat.cast_nonneg N))
      (Real.rpow_nonneg hlogL.le _)
  calc
    (∑ j ∈ sourceSmallResidualIndexSet L N J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j)
        ≤ sourceSmallResidualRawConstant K * (N : ℝ) *
          log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
          (∑ j ∈ sourceSmallResidualIndexSet L N J M,
            (((j + 3 : ℕ) : ℝ) ^
                sourceCanonicalBudgetExponent) *
              log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
              scheduledLogLoss j ^ (5 / 2 : ℝ)) := hraw
    _ ≤ sourceSmallResidualRawConstant K * (N : ℝ) *
          log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
          ((L : ℝ) *
            (sourceScheduledIndexProfileConstant (7 / 4 : ℝ) *
              (ε / C))) :=
      mul_le_mul_of_nonneg_left hsum houter0
    _ = (N : ℝ) * C * (ε / C) := by
      dsimp [C]
      ring
    _ = ε * (N : ℝ) := by
      field_simp [hC.ne']

end

end Erdos327.Analytic
