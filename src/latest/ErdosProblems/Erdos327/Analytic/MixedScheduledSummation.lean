import ErdosProblems.Erdos327.Analytic.ScheduledReduction
import ErdosProblems.Erdos327.Analytic.SieveScheduleErrors
import ErdosProblems.Erdos327.Analytic.ProductEnvelopePowers
import ErdosProblems.Erdos327.Analytic.SieveScheduleLog
import ErdosProblems.Erdos327.Analytic.ScheduledProductBounds
import ErdosProblems.Erdos327.Analytic.AsymptoticParameterSelection
import ErdosProblems.Erdos327.Analytic.PowerLogSummability
import ErdosProblems.Erdos327.Analytic.ScheduledInitialVanishing

/-!
# Quantitative estimates for the mixed scheduled sum

This module isolates the two unconditional estimates needed before the
main mixed Euler-product term can be summed: the finite-sieve truncation
errors and the exact residual fallback.
-/

namespace Erdos327.Analytic

open Filter Finset Real

open scoped BigOperators

noncomputable section

/-- The logarithmic exponent which results after multiplying the regularity
prefactor, the three-form Euler product, and the rough residual Euler
product at the certified numerical parameters. -/
def mixedCanonicalCrossExponent : ℝ :=
  sourceAnatomySlope * log mixedSourceWeightBase +
    oddAnatomySlope * log mixedOddWeightBase +
    mixedSourceWeightBase⁻¹ +
    mixedOddWeightBase⁻¹ +
    2 * (mixedSourceWeightBase * mixedOddWeightBase)⁻¹ - 4

/-- Reciprocal parameter on the source coordinate. -/
def mixedCanonicalAlpha : ℝ := mixedSourceWeightBase⁻¹

/-- Reciprocal parameter on the odd coordinate. -/
def mixedCanonicalBeta : ℝ := mixedOddWeightBase⁻¹

/-- Reciprocal parameter on the common residual coordinate. -/
def mixedCanonicalS : ℝ :=
  (mixedSourceWeightBase * mixedOddWeightBase)⁻¹

/-- Logarithmic power of the scheduled prime cutoff in the large-product
branch. -/
def mixedCanonicalProductExponent : ℝ :=
  mixedCanonicalAlpha + mixedCanonicalBeta + mixedCanonicalS - 3

/-- Logarithmic power of the roughness cutoff in the large-product branch. -/
def mixedCanonicalRoughnessExponent : ℝ :=
  1 - mixedCanonicalAlpha - mixedCanonicalBeta - mixedCanonicalS

/-- Power contributed by the two regularity thresholds. -/
def mixedCanonicalRegularityExponent : ℝ :=
  sourceAnatomySlope * log mixedSourceWeightBase +
    oddAnatomySlope * log mixedOddWeightBase

/-- Logarithmic power of the residual transition scale. -/
def mixedCanonicalResidualExponent : ℝ :=
  mixedCanonicalS - 1

/-- Power of the dyadic logarithmic scale after inserting the regularity
prefactor and the large-product estimate. -/
def mixedCanonicalDyadicExponent : ℝ :=
  mixedCanonicalRegularityExponent +
    mixedCanonicalProductExponent

/-- The numerical certificate needed to sum the normalized mixed main term. -/
theorem mixedCanonicalCrossExponent_lt_neg_one :
    mixedCanonicalCrossExponent < -1 := by
  simpa [mixedCanonicalCrossExponent, sourceAnatomySlope,
    oddAnatomySlope, mixedSourceWeightBase, mixedOddWeightBase] using
    Erdos327.cross_exponent_lt_neg_one

theorem mixedCanonicalS_pos : 0 < mixedCanonicalS := by
  norm_num [mixedCanonicalS, mixedSourceWeightBase,
    mixedOddWeightBase]

theorem mixedCanonicalS_lt_one : mixedCanonicalS < 1 := by
  norm_num [mixedCanonicalS, mixedSourceWeightBase,
    mixedOddWeightBase]

theorem mixedCanonicalProductExponent_lt_zero :
    mixedCanonicalProductExponent < 0 := by
  norm_num [mixedCanonicalProductExponent, mixedCanonicalAlpha,
    mixedCanonicalBeta, mixedCanonicalS, mixedSourceWeightBase,
    mixedOddWeightBase]

theorem mixedCanonicalProductExponent_gt_neg_two :
    -2 < mixedCanonicalProductExponent := by
  norm_num [mixedCanonicalProductExponent, mixedCanonicalAlpha,
    mixedCanonicalBeta, mixedCanonicalS, mixedSourceWeightBase,
    mixedOddWeightBase]

theorem mixedCanonicalRoughnessExponent_lt_zero :
    mixedCanonicalRoughnessExponent < 0 := by
  norm_num [mixedCanonicalRoughnessExponent, mixedCanonicalAlpha,
    mixedCanonicalBeta, mixedCanonicalS, mixedSourceWeightBase,
    mixedOddWeightBase]

theorem mixedCanonicalRegularityExponent_nonneg :
    0 ≤ mixedCanonicalRegularityExponent := by
  simpa [mixedCanonicalRegularityExponent] using
    mixedRegularityExponent_nonneg

theorem mixedCanonicalAlpha_add_beta_add_twoS_gt_one :
    1 < mixedCanonicalAlpha + mixedCanonicalBeta +
      2 * mixedCanonicalS := by
  norm_num [mixedCanonicalAlpha, mixedCanonicalBeta,
    mixedCanonicalS, mixedSourceWeightBase, mixedOddWeightBase]

theorem mixedCanonicalProduct_add_roughnessExponent :
    mixedCanonicalProductExponent +
        mixedCanonicalRoughnessExponent = -2 := by
  unfold mixedCanonicalProductExponent mixedCanonicalRoughnessExponent
  ring

theorem mixedCanonicalResidualExponent_lt_zero :
    mixedCanonicalResidualExponent < 0 := by
  unfold mixedCanonicalResidualExponent
  linarith [mixedCanonicalS_lt_one]

theorem mixedCanonicalResidualExponent_gt_neg_one :
    -1 < mixedCanonicalResidualExponent := by
  unfold mixedCanonicalResidualExponent
  linarith [mixedCanonicalS_pos]

/-- The two convolution powers add to the certified cross exponent. -/
theorem mixedCanonicalDyadic_add_residualExponent :
    mixedCanonicalDyadicExponent +
        mixedCanonicalResidualExponent =
      mixedCanonicalCrossExponent := by
  unfold mixedCanonicalDyadicExponent mixedCanonicalResidualExponent
    mixedCanonicalRegularityExponent mixedCanonicalProductExponent
    mixedCanonicalAlpha
    mixedCanonicalBeta mixedCanonicalS mixedCanonicalCrossExponent
  ring

theorem mixedCanonicalDyadicExponent_lt_zero :
    mixedCanonicalDyadicExponent < 0 := by
  have hsum := mixedCanonicalCrossExponent_lt_neg_one
  have hres := mixedCanonicalResidualExponent_gt_neg_one
  rw [← mixedCanonicalDyadic_add_residualExponent] at hsum
  linarith

/-- The dyadic endpoint exponent also lies above `-1`, so the terminal
two-ended power convolution is locally summable at that endpoint. -/
theorem mixedCanonicalDyadicExponent_gt_neg_one :
    -1 < mixedCanonicalDyadicExponent := by
  have hqb2 : (2 : ℝ) < mixedSourceWeightBase := by
    norm_num [mixedSourceWeightBase]
  have hlogqb :
      log (2 : ℝ) < log mixedSourceWeightBase :=
    Real.strictMonoOn_log
      (by norm_num)
      (by
        simpa only [Set.mem_Ioi] using
          (show (0 : ℝ) < mixedSourceWeightBase by linarith))
      hqb2
  have hslope : (1 : ℝ) < sourceAnatomySlope := by
    norm_num [sourceAnatomySlope]
  have hlogqb0 : 0 < log mixedSourceWeightBase :=
    log_pos mixedSourceWeightBase_gt_one
  have hsource :
      log (2 : ℝ) <
        sourceAnatomySlope * log mixedSourceWeightBase := by
    nlinarith
  have hodd :
      0 ≤ oddAnatomySlope * log mixedOddWeightBase :=
    mul_nonneg oddAnatomySlope_nonneg
      (log_pos mixedOddWeightBase_gt_one).le
  have hregularity :
      log (2 : ℝ) < mixedCanonicalRegularityExponent := by
    unfold mixedCanonicalRegularityExponent
    linarith
  have hreciprocal :
      (131 / 100 : ℝ) <
        mixedCanonicalAlpha + mixedCanonicalBeta +
          mixedCanonicalS := by
    norm_num [mixedCanonicalAlpha, mixedCanonicalBeta,
      mixedCanonicalS, mixedSourceWeightBase, mixedOddWeightBase]
  unfold mixedCanonicalDyadicExponent
    mixedCanonicalProductExponent
  nlinarith [Real.log_two_gt_d9]

theorem mixedCanonicalRegularityExponent_lt_two :
    mixedCanonicalRegularityExponent < 2 := by
  have hcross := mixedCanonicalCrossExponent_lt_neg_one
  have hsum := mixedCanonicalAlpha_add_beta_add_twoS_gt_one
  have hidentity :
      mixedCanonicalCrossExponent =
        mixedCanonicalRegularityExponent +
          mixedCanonicalAlpha + mixedCanonicalBeta +
          2 * mixedCanonicalS - 4 := by
    unfold mixedCanonicalCrossExponent
      mixedCanonicalRegularityExponent mixedCanonicalAlpha
      mixedCanonicalBeta mixedCanonicalS
    ring
  rw [hidentity] at hcross
  linarith

/-- The power of `log L` remaining outside the dyadic convolution. -/
def mixedCanonicalOuterExponent : ℝ :=
  -mixedCanonicalRegularityExponent +
    mixedCanonicalRoughnessExponent - mixedCanonicalS

/-- Outside power accompanying the summable finite-sieve error profile. -/
def mixedCanonicalErrorOuterExponent : ℝ :=
  -mixedCanonicalRegularityExponent - 1

/-- After summing the convolution, the total outside power is exactly
`-2`, explaining the shape used by `eventually_mixedBudget_main`. -/
theorem mixedCanonicalExponent_ledger :
    mixedCanonicalOuterExponent +
        (mixedCanonicalDyadicExponent +
          mixedCanonicalResidualExponent + 1) =
      -2 := by
  unfold mixedCanonicalOuterExponent mixedCanonicalDyadicExponent
    mixedCanonicalResidualExponent mixedCanonicalProductExponent
    mixedCanonicalRoughnessExponent
  ring

/-- Every summand in the exact residual fallback is at most one. -/
theorem mixedExactResidualMoment_le_length
    {L N X : ℕ} {qb qo : ℝ}
    (hqb : 1 < qb) (hqo : 1 < qo) :
    mixedExactResidualMoment L N X qb qo ≤
      (N / (X * X) : ℕ) := by
  have hqb0 : 0 < qb := zero_lt_one.trans hqb
  have hqo0 : 0 < qo := zero_lt_one.trans hqo
  have hprod0 : 0 < qb * qo := mul_pos hqb0 hqo0
  have hprodOne : 1 ≤ qb * qo := by
    nlinarith [mul_pos (sub_pos.mpr hqb) (sub_pos.mpr hqo)]
  have hs0 : 0 ≤ (1 / (qb * qo) : ℝ) := by positivity
  have hs1 : (1 / (qb * qo) : ℝ) ≤ 1 :=
    (div_le_one₀ hprod0).mpr hprodOne
  unfold mixedExactResidualMoment
  calc
    (∑ t ∈ Icc 1 (N / (X * X)),
        if Rough L t then
          (1 / (qb * qo)) ^ primeFactorCountBetween L X t
        else 0)
        ≤ ∑ _t ∈ Icc 1 (N / (X * X)), (1 : ℝ) := by
          apply sum_le_sum
          intro t ht
          split_ifs
          · exact pow_le_one₀ hs0 hs1
          · norm_num
    _ = (N / (X * X) : ℕ) := by simp

/-- Constant covering both cutoff orderings for the canonical mixed local
product. -/
def mixedCanonicalScheduledProductConstant : ℝ :=
  mixedLargeProductConstant
      mixedCanonicalAlpha mixedCanonicalBeta mixedCanonicalS +
    mixedSmallProductConstant *
      (5 : ℝ) ^ (-mixedCanonicalRoughnessExponent)

theorem mixedCanonicalScheduledProductConstant_pos :
    0 < mixedCanonicalScheduledProductConstant := by
  unfold mixedCanonicalScheduledProductConstant
  exact add_pos_of_pos_of_nonneg
    (mixedLargeProductConstant_pos _ _ _)
    (mul_nonneg mixedSmallProductConstant_pos.le
      (Real.rpow_nonneg (by norm_num) _))

/-- Uniform canonical mixed local-product bound on every dominant
scheduled block that can be nonempty.  It is valid in both orderings of
`L` and the scheduled prime cutoff. -/
theorem exp_mixedCanonicalAllCutoffEnvelope_le_scheduled
    {L j : ℕ} (hL : 3 ≤ L)
    (hdom : 32 * sieveRadius j ≤ j)
    (hnear : L ≤ 16 * dyadicScale j) :
    exp (mixedAllCutoffMertensEnvelope L (sieveCutoff j)
      mixedCanonicalAlpha mixedCanonicalBeta mixedCanonicalS) ≤
      mixedCanonicalScheduledProductConstant *
        log (dyadicScale j : ℝ) ^ mixedCanonicalProductExponent *
        log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
        scheduledLogLoss j ^ (2 : ℝ) := by
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
  have hH : 1 ≤ scheduledLogLoss j :=
    scheduledLogLoss_one_le j
  have hratio :
      log (dyadicScale j : ℝ) /
          log (sieveCutoff j : ℝ) ≤
        scheduledLogLoss j := by
    simpa [scheduledLogLoss] using
      log_dyadicScale_div_log_sieveCutoff_le hdom
  by_cases hLz : L ≤ sieveCutoff j
  · rw [mixedAllCutoffMertensEnvelope, if_pos hLz]
    have hbase :=
      exp_mixedMertensEnvelope_le_powers
        (alpha := mixedCanonicalAlpha)
        (beta := mixedCanonicalBeta) (s := mixedCanonicalS)
        (show 2 ≤ L by omega) hz
    have hcutRaw :=
      rpow_neg_le_ratio_rpow hlogX hlogz hH
        (by linarith [mixedCanonicalProductExponent_lt_zero] :
          0 ≤ -mixedCanonicalProductExponent)
        hratio
    have hcut :
        log (sieveCutoff j : ℝ) ^ mixedCanonicalProductExponent ≤
          scheduledLogLoss j ^ (-mixedCanonicalProductExponent) *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalProductExponent := by
      simpa using hcutRaw
    have hHpow :
        scheduledLogLoss j ^ (-mixedCanonicalProductExponent) ≤
          scheduledLogLoss j ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hH
        (by linarith [mixedCanonicalProductExponent_gt_neg_two])
    have hcut' :
        log (sieveCutoff j : ℝ) ^ mixedCanonicalProductExponent ≤
          scheduledLogLoss j ^ (2 : ℝ) *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalProductExponent :=
      hcut.trans
        (mul_le_mul_of_nonneg_right hHpow
          (Real.rpow_nonneg hlogX.le _))
    have hlarge :
        mixedLargeProductConstant
            mixedCanonicalAlpha mixedCanonicalBeta mixedCanonicalS ≤
          mixedCanonicalScheduledProductConstant := by
      unfold mixedCanonicalScheduledProductConstant
      exact le_add_of_nonneg_right
        (mul_nonneg mixedSmallProductConstant_pos.le
          (Real.rpow_nonneg (by norm_num) _))
    calc
      exp (mixedMertensEnvelope L (sieveCutoff j)
          mixedCanonicalAlpha mixedCanonicalBeta mixedCanonicalS)
          ≤
        mixedLargeProductConstant
            mixedCanonicalAlpha mixedCanonicalBeta mixedCanonicalS *
          log (sieveCutoff j : ℝ) ^
            mixedCanonicalProductExponent *
          log (L : ℝ) ^ mixedCanonicalRoughnessExponent := by
            simpa [mixedCanonicalProductExponent,
              mixedCanonicalRoughnessExponent] using hbase
      _ ≤
        mixedLargeProductConstant
            mixedCanonicalAlpha mixedCanonicalBeta mixedCanonicalS *
          (scheduledLogLoss j ^ (2 : ℝ) *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalProductExponent) *
          log (L : ℝ) ^ mixedCanonicalRoughnessExponent := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcut'
                (mixedLargeProductConstant_pos _ _ _).le)
              (Real.rpow_nonneg hlogL.le _)
      _ ≤
        mixedCanonicalScheduledProductConstant *
          log (dyadicScale j : ℝ) ^
            mixedCanonicalProductExponent *
          log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
          scheduledLogLoss j ^ (2 : ℝ) := by
            have hcommon :
                0 ≤ log (dyadicScale j : ℝ) ^
                    mixedCanonicalProductExponent *
                  log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
                  scheduledLogLoss j ^ (2 : ℝ) := by positivity
            calc
              mixedLargeProductConstant
                    mixedCanonicalAlpha mixedCanonicalBeta
                      mixedCanonicalS *
                  (scheduledLogLoss j ^ (2 : ℝ) *
                    log (dyadicScale j : ℝ) ^
                      mixedCanonicalProductExponent) *
                  log (L : ℝ) ^
                    mixedCanonicalRoughnessExponent =
                mixedLargeProductConstant
                    mixedCanonicalAlpha mixedCanonicalBeta
                      mixedCanonicalS *
                  (log (dyadicScale j : ℝ) ^
                      mixedCanonicalProductExponent *
                    log (L : ℝ) ^
                      mixedCanonicalRoughnessExponent *
                    scheduledLogLoss j ^ (2 : ℝ)) := by ring
              _ ≤ mixedCanonicalScheduledProductConstant *
                  (log (dyadicScale j : ℝ) ^
                      mixedCanonicalProductExponent *
                    log (L : ℝ) ^
                      mixedCanonicalRoughnessExponent *
                    scheduledLogLoss j ^ (2 : ℝ)) :=
                mul_le_mul_of_nonneg_right hlarge hcommon
              _ = _ := by ring
  · rw [mixedAllCutoffMertensEnvelope, if_neg hLz]
    have hbase :=
      exp_mixedSmallCutoffMertensEnvelope_le_power hz
    have hcut :=
      rpow_neg_le_ratio_rpow hlogX hlogz hH
        (by norm_num : (0 : ℝ) ≤ 2) hratio
    have hLratio :
        log (L : ℝ) / log (dyadicScale j : ℝ) ≤ 5 :=
      log_nat_div_log_nat_le_five_of_le_sixteen_mul hX hnear
    have hroughRaw :=
      rpow_neg_le_ratio_rpow hlogL hlogX
        (by norm_num : (1 : ℝ) ≤ 5)
        (by
          linarith [mixedCanonicalRoughnessExponent_lt_zero] :
          0 ≤ -mixedCanonicalRoughnessExponent)
        hLratio
    have hrough :
        log (dyadicScale j : ℝ) ^
            mixedCanonicalRoughnessExponent ≤
          (5 : ℝ) ^ (-mixedCanonicalRoughnessExponent) *
            log (L : ℝ) ^ mixedCanonicalRoughnessExponent := by
      simpa using hroughRaw
    have hsplit :
        log (dyadicScale j : ℝ) ^ (-2 : ℝ) =
          log (dyadicScale j : ℝ) ^
              mixedCanonicalProductExponent *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalRoughnessExponent := by
      rw [← Real.rpow_add hlogX]
      congr 1
      exact mixedCanonicalProduct_add_roughnessExponent.symm
    have htarget :
        log (sieveCutoff j : ℝ) ^ (-2 : ℝ) ≤
          scheduledLogLoss j ^ (2 : ℝ) *
            ((5 : ℝ) ^ (-mixedCanonicalRoughnessExponent) *
              log (dyadicScale j : ℝ) ^
                mixedCanonicalProductExponent *
              log (L : ℝ) ^
                mixedCanonicalRoughnessExponent) := by
      calc
        log (sieveCutoff j : ℝ) ^ (-2 : ℝ)
            ≤ scheduledLogLoss j ^ (2 : ℝ) *
                log (dyadicScale j : ℝ) ^ (-2 : ℝ) := hcut
        _ = scheduledLogLoss j ^ (2 : ℝ) *
              (log (dyadicScale j : ℝ) ^
                  mixedCanonicalProductExponent *
                log (dyadicScale j : ℝ) ^
                  mixedCanonicalRoughnessExponent) := by rw [hsplit]
        _ ≤ scheduledLogLoss j ^ (2 : ℝ) *
              (log (dyadicScale j : ℝ) ^
                  mixedCanonicalProductExponent *
                ((5 : ℝ) ^ (-mixedCanonicalRoughnessExponent) *
                  log (L : ℝ) ^
                    mixedCanonicalRoughnessExponent)) := by
              gcongr
        _ = _ := by ring
    calc
      exp (mixedSmallCutoffMertensEnvelope (sieveCutoff j))
          ≤ mixedSmallProductConstant *
              log (sieveCutoff j : ℝ) ^ (-2 : ℝ) := hbase
      _ ≤ mixedSmallProductConstant *
          (scheduledLogLoss j ^ (2 : ℝ) *
            ((5 : ℝ) ^ (-mixedCanonicalRoughnessExponent) *
              log (dyadicScale j : ℝ) ^
                mixedCanonicalProductExponent *
              log (L : ℝ) ^
                mixedCanonicalRoughnessExponent)) :=
        mul_le_mul_of_nonneg_left htarget
          mixedSmallProductConstant_pos.le
      _ ≤ mixedCanonicalScheduledProductConstant *
          log (dyadicScale j : ℝ) ^
            mixedCanonicalProductExponent *
          log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
          scheduledLogLoss j ^ (2 : ℝ) := by
        have hcoef :
            mixedSmallProductConstant *
                (5 : ℝ) ^ (-mixedCanonicalRoughnessExponent) ≤
              mixedCanonicalScheduledProductConstant := by
          unfold mixedCanonicalScheduledProductConstant
          exact le_add_of_nonneg_left
            (mixedLargeProductConstant_pos _ _ _).le
        have hcommon :
            0 ≤ log (dyadicScale j : ℝ) ^
                mixedCanonicalProductExponent *
              log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
              scheduledLogLoss j ^ (2 : ℝ) := by positivity
        calc
          mixedSmallProductConstant *
              (scheduledLogLoss j ^ (2 : ℝ) *
                ((5 : ℝ) ^ (-mixedCanonicalRoughnessExponent) *
                  log (dyadicScale j : ℝ) ^
                    mixedCanonicalProductExponent *
                  log (L : ℝ) ^
                    mixedCanonicalRoughnessExponent)) =
            (mixedSmallProductConstant *
                (5 : ℝ) ^ (-mixedCanonicalRoughnessExponent)) *
              (log (dyadicScale j : ℝ) ^
                  mixedCanonicalProductExponent *
                log (L : ℝ) ^
                  mixedCanonicalRoughnessExponent *
                scheduledLogLoss j ^ (2 : ℝ)) := by ring
          _ ≤ mixedCanonicalScheduledProductConstant *
              (log (dyadicScale j : ℝ) ^
                  mixedCanonicalProductExponent *
                log (L : ℝ) ^
                  mixedCanonicalRoughnessExponent *
                scheduledLogLoss j ^ (2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hcoef hcommon
          _ = _ := by ring

/-- Constant part of the canonical mixed regularity prefactor. -/
def mixedCanonicalPrefactorConstant (Kb Ko : ℝ) : ℝ :=
  mixedSourceWeightBase ^ Kb * mixedOddWeightBase ^ Ko *
    (5 : ℝ) ^ mixedCanonicalRegularityExponent

theorem mixedCanonicalPrefactorConstant_pos (Kb Ko : ℝ) :
    0 < mixedCanonicalPrefactorConstant Kb Ko := by
  unfold mixedCanonicalPrefactorConstant
  positivity [mixedSourceWeightBase_gt_one,
    mixedOddWeightBase_gt_one]

/-- Power form of the regularity prefactor on a nontrivial dyadic scale. -/
theorem mixedCanonicalBlockPrefactor_le_powers
    {L X : ℕ} {Kb Ko : ℝ} (hL : 3 ≤ L) (hX : 2 ≤ X) :
    mixedBlockPrefactor L X
        sourceAnatomySlope Kb oddAnatomySlope Ko
        mixedSourceWeightBase mixedOddWeightBase ≤
      mixedCanonicalPrefactorConstant Kb Ko *
        log (X : ℝ) ^ mixedCanonicalRegularityExponent *
        log (L : ℝ) ^ (-mixedCanonicalRegularityExponent) := by
  have hlogX : 0 < log (X : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogTwoX :
      log (2 : ℝ) ≤ log (X : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by norm_num)
      (by
        simpa only [Set.mem_Ioi] using
          (show (0 : ℝ) < (X : ℕ) by positivity))
      (by exact_mod_cast hX)
  have hlog16 :
      log (16 : ℝ) = 4 * log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hlog16X :
      log (16 * (X : ℝ)) ≤ 5 * log (X : ℝ) := by
    rw [log_mul (by norm_num : (16 : ℝ) ≠ 0)
      (by positivity : (X : ℝ) ≠ 0), hlog16]
    linarith
  have hratio :
      log (16 * (X : ℝ)) / log (L : ℝ) ≤
        (5 * log (X : ℝ)) / log (L : ℝ) :=
    div_le_div_of_nonneg_right hlog16X hlogL.le
  have hratio0 :
      0 ≤ log (16 * (X : ℝ)) / log (L : ℝ) := by
    positivity [Real.log_pos (by
      have : (1 : ℝ) < 16 * X := by
        exact_mod_cast (show 1 < 16 * X by omega)
      exact this)]
  have hpow :
      (log (16 * (X : ℝ)) / log (L : ℝ)) ^
          mixedCanonicalRegularityExponent ≤
        ((5 * log (X : ℝ)) / log (L : ℝ)) ^
          mixedCanonicalRegularityExponent :=
    Real.rpow_le_rpow hratio0 hratio
      mixedCanonicalRegularityExponent_nonneg
  have hnormalize :
      ((5 * log (X : ℝ)) / log (L : ℝ)) ^
          mixedCanonicalRegularityExponent =
        (5 : ℝ) ^ mixedCanonicalRegularityExponent *
          log (X : ℝ) ^ mixedCanonicalRegularityExponent *
          log (L : ℝ) ^ (-mixedCanonicalRegularityExponent) := by
    rw [Real.div_rpow (mul_nonneg (by norm_num) hlogX.le)
        hlogL.le,
      Real.mul_rpow (by norm_num) hlogX.le,
      Real.rpow_neg hlogL.le]
    ring
  unfold mixedBlockPrefactor
  change
    mixedSourceWeightBase ^ Kb * mixedOddWeightBase ^ Ko *
        (log (16 * (X : ℝ)) / log (L : ℝ)) ^
          mixedCanonicalRegularityExponent ≤ _
  calc
    mixedSourceWeightBase ^ Kb * mixedOddWeightBase ^ Ko *
          (log (16 * (X : ℝ)) / log (L : ℝ)) ^
            mixedCanonicalRegularityExponent
        ≤
      mixedSourceWeightBase ^ Kb * mixedOddWeightBase ^ Ko *
          (((5 * log (X : ℝ)) / log (L : ℝ)) ^
            mixedCanonicalRegularityExponent) :=
      mul_le_mul_of_nonneg_left hpow
        (mul_nonneg
          (Real.rpow_nonneg
            (by linarith [mixedSourceWeightBase_gt_one]) _)
          (Real.rpow_nonneg
            (by linarith [mixedOddWeightBase_gt_one]) _))
    _ = mixedCanonicalPrefactorConstant Kb Ko *
          log (X : ℝ) ^ mixedCanonicalRegularityExponent *
          log (L : ℝ) ^ (-mixedCanonicalRegularityExponent) := by
      rw [hnormalize]
      unfold mixedCanonicalPrefactorConstant
      ring

/-- The Euler-product part of the scheduled three-form box bound. -/
def mixedScheduledMertensMain
    (L : ℕ) (qb qo : ℝ) (j : ℕ) : ℝ :=
  8 * (dyadicScale j : ℝ) ^ 2 *
    exp (mixedAllCutoffMertensEnvelope L (sieveCutoff j)
      (1 / qb) (1 / qo) (1 / (qb * qo)))

/-- Scheduled main box at the certified bases in uniform power form. -/
theorem mixedCanonicalScheduledMertensMain_le_powers
    {L j : ℕ} (hL : 3 ≤ L)
    (hdom : 32 * sieveRadius j ≤ j)
    (hnear : L ≤ 16 * dyadicScale j) :
    mixedScheduledMertensMain L
        mixedSourceWeightBase mixedOddWeightBase j ≤
      8 * mixedCanonicalScheduledProductConstant *
        (dyadicScale j : ℝ) ^ 2 *
        log (dyadicScale j : ℝ) ^
          mixedCanonicalProductExponent *
        log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
        scheduledLogLoss j ^ (2 : ℝ) := by
  have hproduct :=
    exp_mixedCanonicalAllCutoffEnvelope_le_scheduled
      hL hdom hnear
  unfold mixedScheduledMertensMain
  rw [show (1 / mixedSourceWeightBase : ℝ) =
      mixedCanonicalAlpha by simp [mixedCanonicalAlpha, one_div],
    show (1 / mixedOddWeightBase : ℝ) =
      mixedCanonicalBeta by simp [mixedCanonicalBeta, one_div],
    show (1 / (mixedSourceWeightBase * mixedOddWeightBase) : ℝ) =
      mixedCanonicalS by simp [mixedCanonicalS, one_div]]
  calc
    8 * (dyadicScale j : ℝ) ^ 2 *
          exp (mixedAllCutoffMertensEnvelope L (sieveCutoff j)
            mixedCanonicalAlpha mixedCanonicalBeta mixedCanonicalS)
        ≤
      8 * (dyadicScale j : ℝ) ^ 2 *
        (mixedCanonicalScheduledProductConstant *
          log (dyadicScale j : ℝ) ^
            mixedCanonicalProductExponent *
          log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
          scheduledLogLoss j ^ (2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hproduct (by positivity)
    _ = _ := by ring

/-- A single summable envelope for both finite-sieve truncation errors. -/
def mixedScheduledSieveError (j : ℕ) : ℝ :=
  9 * (dyadicScale j : ℝ) ^ 2 /
    (((j + 1 : ℕ) : ℝ) ^ 8)

/-- Pointwise assembly of the two schedule-error estimates. -/
theorem mixedAllCutoffSharpBoxBound_le_main_add_error
    {L j : ℕ} {qb qo : ℝ}
    (htail :
      scheduledFactorialTail j ≤
        1 / (((j + 1 : ℕ) : ℝ) ^ 8))
    (hboundary :
      scheduledPolynomialBoundary j ≤
        (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8)) :
    mixedAllCutoffSharpBoxBound
        L (sieveCutoff j) (dyadicScale j) (sieveRadius j) qb qo ≤
      mixedScheduledMertensMain L qb qo j +
        mixedScheduledSieveError j := by
  have htailScaled :
      8 * (dyadicScale j : ℝ) ^ 2 * scheduledFactorialTail j ≤
        8 * (dyadicScale j : ℝ) ^ 2 *
          (1 / (((j + 1 : ℕ) : ℝ) ^ 8)) :=
    mul_le_mul_of_nonneg_left htail (by positivity)
  change
    mixedScheduledMertensMain L qb qo j +
        8 * (dyadicScale j : ℝ) ^ 2 * scheduledFactorialTail j +
        scheduledPolynomialBoundary j ≤
      mixedScheduledMertensMain L qb qo j +
        mixedScheduledSieveError j
  calc
    mixedScheduledMertensMain L qb qo j +
          8 * (dyadicScale j : ℝ) ^ 2 * scheduledFactorialTail j +
          scheduledPolynomialBoundary j
        ≤
      mixedScheduledMertensMain L qb qo j +
          (8 * (dyadicScale j : ℝ) ^ 2 *
            (1 / (((j + 1 : ℕ) : ℝ) ^ 8))) +
          ((dyadicScale j : ℝ) ^ 2 /
            (((j + 1 : ℕ) : ℝ) ^ 8)) :=
      add_le_add (add_le_add le_rfl htailScaled) hboundary
    _ =
      mixedScheduledMertensMain L qb qo j +
        mixedScheduledSieveError j := by
          unfold mixedScheduledSieveError
          ring

/-- The sharp scheduled box bound is eventually its Euler-product main term
plus a summable error, with all constants explicit. -/
theorem eventually_mixedAllCutoffSharpBoxBound_le_main_add_error
    (L : ℕ) (qb qo : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      mixedAllCutoffSharpBoxBound
          L (sieveCutoff j) (dyadicScale j) (sieveRadius j) qb qo ≤
        mixedScheduledMertensMain L qb qo j +
          mixedScheduledSieveError j := by
  filter_upwards
    [eventually_scheduledFactorialTail_le_inv_add_one_pow_eight,
      eventually_scheduledPolynomialBoundary_le] with j htail hboundary
  exact mixedAllCutoffSharpBoxBound_le_main_add_error htail hboundary

/-- Cutoff-independent constant in the canonical residual Mertens bound. -/
def mixedCanonicalResidualConstant : ℝ :=
  2 * (log 4 + 5) *
    exp (mixedCanonicalS * cutoffTailReserve +
      2 * reciprocalPrimeErrorReserve + 38)

theorem mixedCanonicalResidualConstant_pos :
    0 < mixedCanonicalResidualConstant := by
  unfold mixedCanonicalResidualConstant
  positivity [Real.log_pos (by norm_num : (1 : ℝ) < 4)]

/-- Power normalization of the fully explicit residual bound.  The
transition scale is `min X Y`, exactly as required in the later
two-range convolution. -/
theorem mixedCanonicalBlockResidualBound_le_powers
    {L N X : ℕ} (hL : 3 ≤ L) (hLX : L ≤ X)
    (hLY : L ≤ N / (X * X)) :
    mixedBlockResidualBound L N X
        mixedSourceWeightBase mixedOddWeightBase ≤
      mixedCanonicalResidualConstant *
        (N / (X * X) : ℕ) *
        log ((min X (N / (X * X)) : ℕ) : ℝ) ^
          mixedCanonicalResidualExponent *
        log (L : ℝ) ^ (-mixedCanonicalS) := by
  let Y : ℕ := N / (X * X)
  let T : ℕ := min X Y
  have hLT : L ≤ T := by
    dsimp [T, Y]
    exact le_min hLX hLY
  have hTY : T ≤ Y := by
    dsimp [T]
    exact min_le_right _ _
  have hT2 : 2 ≤ T := by omega
  have hY2 : 2 ≤ Y := hT2.trans hTY
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogT : 0 < log (T : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < T by omega))
  have hlogY : 0 < log (Y : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < Y by omega))
  have htail1 :=
    primeInvTailUpper_pred_le_scale_add_reserve hL hLT
  have htail1' :
      primeInvTailUpper (L - 1) T ≤
        log (log (T : ℝ)) - log (log (L : ℝ)) +
          cutoffTailReserve := by
    unfold cutoffLogScale at htail1
    rw [log_div hlogT.ne' hlogL.ne'] at htail1
    exact htail1
  have htail2 :=
    primeInvTailUpper_le_main_add_error hT2 hTY
  have hs0 : 0 ≤ mixedCanonicalS := mixedCanonicalS_pos.le
  have htail1Mul :=
    mul_le_mul_of_nonneg_left htail1' hs0
  have hexponent :
      mixedCanonicalS * primeInvTailUpper (L - 1) T +
          primeInvTailUpper T Y + 38 ≤
        log (log (Y : ℝ)) +
          mixedCanonicalResidualExponent * log (log (T : ℝ)) +
          (-mixedCanonicalS) * log (log (L : ℝ)) +
          (mixedCanonicalS * cutoffTailReserve +
            2 * reciprocalPrimeErrorReserve + 38) := by
    unfold mixedCanonicalResidualExponent
    linarith
  have hexp := exp_le_exp.mpr hexponent
  have hfront :
      0 ≤ 2 * ((log 4 + 5) * (Y : ℝ) / log Y) := by
    positivity [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
  have hexpEq :
      exp
          (log (log (Y : ℝ)) +
            mixedCanonicalResidualExponent * log (log (T : ℝ)) +
            (-mixedCanonicalS) * log (log (L : ℝ)) +
            (mixedCanonicalS * cutoffTailReserve +
              2 * reciprocalPrimeErrorReserve + 38)) =
        log (Y : ℝ) *
          exp (mixedCanonicalS * cutoffTailReserve +
            2 * reciprocalPrimeErrorReserve + 38) *
          exp (mixedCanonicalResidualExponent *
            log (log (T : ℝ))) *
          exp ((-mixedCanonicalS) *
            log (log (L : ℝ))) := by
    rw [show
      log (log (Y : ℝ)) +
          mixedCanonicalResidualExponent * log (log (T : ℝ)) +
          (-mixedCanonicalS) * log (log (L : ℝ)) +
          (mixedCanonicalS * cutoffTailReserve +
            2 * reciprocalPrimeErrorReserve + 38) =
        log (log (Y : ℝ)) +
          (mixedCanonicalS * cutoffTailReserve +
            2 * reciprocalPrimeErrorReserve + 38) +
          mixedCanonicalResidualExponent * log (log (T : ℝ)) +
          (-mixedCanonicalS) * log (log (L : ℝ)) by ring,
      exp_add, exp_add, exp_add, exp_log hlogY]
  unfold mixedBlockResidualBound
  dsimp only
  rw [show
    (1 / (mixedSourceWeightBase * mixedOddWeightBase) : ℝ) =
      mixedCanonicalS by
        simp [mixedCanonicalS, one_div]]
  change
    2 * ((log 4 + 5) * (Y : ℝ) / log Y) *
        exp
          (mixedCanonicalS * primeInvTailUpper (L - 1) T +
            primeInvTailUpper T Y + 38) ≤ _
  calc
    2 * ((log 4 + 5) * (Y : ℝ) / log Y) *
          exp
            (mixedCanonicalS * primeInvTailUpper (L - 1) T +
              primeInvTailUpper T Y + 38)
        ≤
      2 * ((log 4 + 5) * (Y : ℝ) / log Y) *
        exp
          (log (log (Y : ℝ)) +
            mixedCanonicalResidualExponent * log (log (T : ℝ)) +
            (-mixedCanonicalS) * log (log (L : ℝ)) +
            (mixedCanonicalS * cutoffTailReserve +
              2 * reciprocalPrimeErrorReserve + 38)) :=
      mul_le_mul_of_nonneg_left hexp hfront
    _ = mixedCanonicalResidualConstant * (Y : ℝ) *
          log (T : ℝ) ^ mixedCanonicalResidualExponent *
          log (L : ℝ) ^ (-mixedCanonicalS) := by
      rw [hexpEq]
      unfold mixedCanonicalResidualConstant
      rw [Real.rpow_def_of_pos hlogT,
        Real.rpow_def_of_pos hlogL]
      field_simp [hlogY.ne']

/-- The dyadic square cancels its residual quotient without loss. -/
theorem dyadic_sq_mul_mixedResidualCutoff_le
    (N j : ℕ) :
    (dyadicScale j * dyadicScale j) *
        (N / (dyadicScale j * dyadicScale j)) ≤ N := by
  simpa [Nat.mul_comm] using
    Nat.div_mul_le_self N (dyadicScale j * dyadicScale j)

/-- Fixed constant in the canonical mixed Euler main term, with the
moving odd intercept factored out. -/
def mixedCanonicalMainConstant (Kb : ℝ) : ℝ :=
  8 *
    (mixedSourceWeightBase ^ Kb *
      (5 : ℝ) ^ mixedCanonicalRegularityExponent) *
    mixedCanonicalScheduledProductConstant *
    mixedCanonicalResidualConstant

theorem mixedCanonicalMainConstant_pos (Kb : ℝ) :
    0 < mixedCanonicalMainConstant Kb := by
  unfold mixedCanonicalMainConstant
  positivity [mixedSourceWeightBase_gt_one,
    mixedCanonicalScheduledProductConstant_pos,
    mixedCanonicalResidualConstant_pos]

/-- Complete pointwise power normalization of the canonical Euler main
term on a good, nonempty scheduled block. -/
theorem mixedCanonicalGoodMainBlock_le_convolution
    {L N j : ℕ} {Kb Ko : ℝ}
    (hL : 3 ≤ L) (hdom : 32 * sieveRadius j ≤ j)
    (hnear : L ≤ 16 * dyadicScale j)
    (hgood : mixedScheduledGoodIndex L N j) :
    mixedBlockPrefactor L (dyadicScale j)
          sourceAnatomySlope Kb oddAnatomySlope Ko
          mixedSourceWeightBase mixedOddWeightBase *
        mixedScheduledMertensMain L
          mixedSourceWeightBase mixedOddWeightBase j *
        mixedBlockResidualBound L N (dyadicScale j)
          mixedSourceWeightBase mixedOddWeightBase ≤
      mixedCanonicalMainConstant Kb *
        mixedOddWeightBase ^ Ko * (N : ℝ) *
        log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent *
        log ((min (dyadicScale j)
          (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
            mixedCanonicalResidualExponent *
        log (L : ℝ) ^ mixedCanonicalOuterExponent *
        scheduledLogLoss j ^ (2 : ℝ) := by
  have hX2 : 2 ≤ dyadicScale j := by
    exact hgood.1.trans hgood.2.2.1
  have hLX : L ≤ dyadicScale j := hgood.2.1
  have hLY :
      L ≤ N / (dyadicScale j * dyadicScale j) :=
    hgood.2.2.2
  have hlogX : 0 < log (dyadicScale j : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < dyadicScale j by omega))
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hpref :=
    mixedCanonicalBlockPrefactor_le_powers
      (Kb := Kb) (Ko := Ko) hL hX2
  have hmain :=
    mixedCanonicalScheduledMertensMain_le_powers
      hL hdom hnear
  have hres :=
    mixedCanonicalBlockResidualBound_le_powers
      hL hLX hLY
  have hpref0 :
      0 ≤ mixedBlockPrefactor L (dyadicScale j)
        sourceAnatomySlope Kb oddAnatomySlope Ko
        mixedSourceWeightBase mixedOddWeightBase :=
    mixedBlockPrefactor_nonneg hL
      (by omega) mixedSourceWeightBase_gt_one
      mixedOddWeightBase_gt_one
  have hprefR0 :
      0 ≤ mixedCanonicalPrefactorConstant Kb Ko *
        log (dyadicScale j : ℝ) ^
          mixedCanonicalRegularityExponent *
        log (L : ℝ) ^ (-mixedCanonicalRegularityExponent) := by
    exact mul_nonneg
      (mul_nonneg (mixedCanonicalPrefactorConstant_pos Kb Ko).le
        (Real.rpow_nonneg hlogX.le _))
      (Real.rpow_nonneg hlogL.le _)
  have hmain0 :
      0 ≤ mixedScheduledMertensMain L
        mixedSourceWeightBase mixedOddWeightBase j := by
    unfold mixedScheduledMertensMain
    positivity
  have hmainR0 :
      0 ≤ 8 * mixedCanonicalScheduledProductConstant *
        (dyadicScale j : ℝ) ^ 2 *
        log (dyadicScale j : ℝ) ^
          mixedCanonicalProductExponent *
        log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
        scheduledLogLoss j ^ (2 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num)
              mixedCanonicalScheduledProductConstant_pos.le)
            (sq_nonneg (dyadicScale j : ℝ)))
          (Real.rpow_nonneg hlogX.le _))
        (Real.rpow_nonneg hlogL.le _))
      (Real.rpow_nonneg
        (by linarith [scheduledLogLoss_one_le j]) _)
  have hres0 :
      0 ≤ mixedBlockResidualBound L N (dyadicScale j)
        mixedSourceWeightBase mixedOddWeightBase := by
    have hY3 :
        3 ≤ N / (dyadicScale j * dyadicScale j) :=
      hL.trans hLY
    have hlogY :
        0 < log (N / (dyadicScale j * dyadicScale j) : ℕ) :=
      log_pos (by exact_mod_cast (show
        1 < N / (dyadicScale j * dyadicScale j) by omega))
    unfold mixedBlockResidualBound
    dsimp only
    positivity
  have hresR0 :
      0 ≤ mixedCanonicalResidualConstant *
        (N / (dyadicScale j * dyadicScale j) : ℕ) *
        log ((min (dyadicScale j)
          (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
            mixedCanonicalResidualExponent *
        log (L : ℝ) ^ (-mixedCanonicalS) := by
    positivity [mixedCanonicalResidualConstant_pos]
  have hscaled :
      mixedBlockPrefactor L (dyadicScale j)
            sourceAnatomySlope Kb oddAnatomySlope Ko
            mixedSourceWeightBase mixedOddWeightBase *
          mixedScheduledMertensMain L
            mixedSourceWeightBase mixedOddWeightBase j *
          mixedBlockResidualBound L N (dyadicScale j)
            mixedSourceWeightBase mixedOddWeightBase ≤
        (mixedCanonicalPrefactorConstant Kb Ko *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalRegularityExponent *
            log (L : ℝ) ^
              (-mixedCanonicalRegularityExponent)) *
          (8 * mixedCanonicalScheduledProductConstant *
            (dyadicScale j : ℝ) ^ 2 *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalProductExponent *
            log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
            scheduledLogLoss j ^ (2 : ℝ)) *
          (mixedCanonicalResidualConstant *
            (N / (dyadicScale j * dyadicScale j) : ℕ) *
            log ((min (dyadicScale j)
              (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
                mixedCanonicalResidualExponent *
            log (L : ℝ) ^ (-mixedCanonicalS)) := by
    calc
      _ ≤
        (mixedCanonicalPrefactorConstant Kb Ko *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalRegularityExponent *
            log (L : ℝ) ^
              (-mixedCanonicalRegularityExponent)) *
          mixedScheduledMertensMain L
            mixedSourceWeightBase mixedOddWeightBase j *
          mixedBlockResidualBound L N (dyadicScale j)
            mixedSourceWeightBase mixedOddWeightBase :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpref hmain0) hres0
      _ ≤
        (mixedCanonicalPrefactorConstant Kb Ko *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalRegularityExponent *
            log (L : ℝ) ^
              (-mixedCanonicalRegularityExponent)) *
          (8 * mixedCanonicalScheduledProductConstant *
            (dyadicScale j : ℝ) ^ 2 *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalProductExponent *
            log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
            scheduledLogLoss j ^ (2 : ℝ)) *
          mixedBlockResidualBound L N (dyadicScale j)
            mixedSourceWeightBase mixedOddWeightBase :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmain hprefR0) hres0
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left hres
          (mul_nonneg hprefR0 hmainR0)
  have hXYnat := dyadic_sq_mul_mixedResidualCutoff_le N j
  have hXY :
      (dyadicScale j : ℝ) ^ 2 *
          (N / (dyadicScale j * dyadicScale j) : ℕ) ≤
        (N : ℝ) := by
    have hcast :
        (((dyadicScale j * dyadicScale j) *
          (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ≤
            (N : ℝ) := by
      exact_mod_cast hXYnat
    simpa [pow_two] using hcast
  have hpowX :
      log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent =
        log (dyadicScale j : ℝ) ^
            mixedCanonicalRegularityExponent *
          log (dyadicScale j : ℝ) ^
            mixedCanonicalProductExponent := by
    unfold mixedCanonicalDyadicExponent
    exact Real.rpow_add hlogX _ _
  have hpowL :
      log (L : ℝ) ^ mixedCanonicalOuterExponent =
        log (L : ℝ) ^ (-mixedCanonicalRegularityExponent) *
          log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
          log (L : ℝ) ^ (-mixedCanonicalS) := by
    rw [show mixedCanonicalOuterExponent =
        (-mixedCanonicalRegularityExponent +
          mixedCanonicalRoughnessExponent) + (-mixedCanonicalS) by
      unfold mixedCanonicalOuterExponent
      ring,
      Real.rpow_add hlogL, Real.rpow_add hlogL]
  calc
    _ ≤
      (mixedCanonicalPrefactorConstant Kb Ko *
          log (dyadicScale j : ℝ) ^
            mixedCanonicalRegularityExponent *
          log (L : ℝ) ^
            (-mixedCanonicalRegularityExponent)) *
        (8 * mixedCanonicalScheduledProductConstant *
          (dyadicScale j : ℝ) ^ 2 *
          log (dyadicScale j : ℝ) ^
            mixedCanonicalProductExponent *
          log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
          scheduledLogLoss j ^ (2 : ℝ)) *
        (mixedCanonicalResidualConstant *
          (N / (dyadicScale j * dyadicScale j) : ℕ) *
          log ((min (dyadicScale j)
            (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent *
          log (L : ℝ) ^ (-mixedCanonicalS)) := hscaled
    _ =
      mixedCanonicalMainConstant Kb *
        mixedOddWeightBase ^ Ko *
        ((dyadicScale j : ℝ) ^ 2 *
          (N / (dyadicScale j * dyadicScale j) : ℕ)) *
        log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent *
        log ((min (dyadicScale j)
          (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
            mixedCanonicalResidualExponent *
        log (L : ℝ) ^ mixedCanonicalOuterExponent *
        scheduledLogLoss j ^ (2 : ℝ) := by
      rw [hpowX, hpowL]
      unfold mixedCanonicalPrefactorConstant mixedCanonicalMainConstant
      ring
    _ ≤
      mixedCanonicalMainConstant Kb *
        mixedOddWeightBase ^ Ko * (N : ℝ) *
        log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent *
        log ((min (dyadicScale j)
          (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
            mixedCanonicalResidualExponent *
        log (L : ℝ) ^ mixedCanonicalOuterExponent *
        scheduledLogLoss j ^ (2 : ℝ) := by
      gcongr
      · exact Real.rpow_nonneg
          (by linarith [scheduledLogLoss_one_le j]) _
      · exact mul_nonneg
          (mixedCanonicalMainConstant_pos Kb).le
          (Real.rpow_nonneg
            (by linarith [mixedOddWeightBase_gt_one]) _)

/-- Explicit constant converting the binary schedule loss to four powers
of the real logarithm of the index. -/
def mixedScheduleLogConstant : ℝ :=
  (4096 : ℝ) ^ 2 * (4 / log (2 : ℝ) ^ 2) ^ 2

theorem mixedScheduleLogConstant_pos :
    0 < mixedScheduleLogConstant := by
  unfold mixedScheduleLogConstant
  positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- The squared schedule loss costs at most four powers of `log (j+1)`. -/
theorem scheduledLogLoss_sq_le_log_four
    {j : ℕ} (hj : 1 ≤ j) :
    scheduledLogLoss j ^ (2 : ℝ) ≤
      mixedScheduleLogConstant *
        log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) := by
  have hheight := sieveHeight_cast_sq_le hj
  have hlog0 :
      0 ≤ log (((j + 1 : ℕ) : ℝ)) :=
    Real.log_natCast_nonneg _
  have hlog2 : 0 < log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hfactor0 : 0 ≤ 4 / log (2 : ℝ) ^ 2 := by positivity
  have hheight' :
      (sieveHeight j : ℝ) ^ 2 ≤
        (4 / log (2 : ℝ) ^ 2) *
          log (((j + 1 : ℕ) : ℝ)) ^ 2 := by
    calc
      (sieveHeight j : ℝ) ^ 2
          ≤ 4 * log (((j + 1 : ℕ) : ℝ)) ^ 2 /
              log (2 : ℝ) ^ 2 := hheight
      _ = (4 / log (2 : ℝ) ^ 2) *
            log (((j + 1 : ℕ) : ℝ)) ^ 2 := by ring
  have hsquare :=
    (sq_le_sq₀ (sq_nonneg (sieveHeight j : ℝ))
      (mul_nonneg hfactor0 (sq_nonneg
        (log (((j + 1 : ℕ) : ℝ)))))).2 hheight'
  rw [show scheduledLogLoss j ^ (2 : ℝ) =
      scheduledLogLoss j ^ (2 : ℕ) by
        norm_num [Real.rpow_natCast],
    show log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) =
      log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℕ) by
        norm_num [Real.rpow_natCast]]
  unfold scheduledLogLoss mixedScheduleLogConstant
  calc
    (4096 * (sieveHeight j : ℝ) ^ 2) ^ 2
        = (4096 : ℝ) ^ 2 *
            ((sieveHeight j : ℝ) ^ 2) ^ 2 := by ring
    _ ≤ (4096 : ℝ) ^ 2 *
          ((4 / log (2 : ℝ) ^ 2) *
            log (((j + 1 : ℕ) : ℝ)) ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (sq_nonneg (4096 : ℝ))
    _ = (4096 : ℝ) ^ 2 *
          (4 / log (2 : ℝ) ^ 2) ^ 2 *
          log (((j + 1 : ℕ) : ℝ)) ^ 4 := by
      push_cast
      ring

/-- Constant replacing the negative dyadic logarithmic power by the
corresponding power of `j+1`. -/
def mixedDyadicIndexConstant : ℝ :=
  (2 / log (2 : ℝ)) ^ (-mixedCanonicalCrossExponent)

theorem mixedDyadicIndexConstant_pos :
    0 < mixedDyadicIndexConstant := by
  unfold mixedDyadicIndexConstant
  positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem log_dyadicScale_rpow_cross_le_index
    {j : ℕ} (hj : 1 ≤ j) :
    log (dyadicScale j : ℝ) ^ mixedCanonicalCrossExponent ≤
      mixedDyadicIndexConstant *
        (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) := by
  have hlog2 : 0 < log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogX : 0 < log (dyadicScale j : ℝ) := by
    rw [log_dyadicScale]
    positivity
  have hH :
      (1 : ℝ) ≤ 2 / log (2 : ℝ) := by
    apply (le_div_iff₀ hlog2).2
    linarith [Real.log_two_lt_d9]
  have hratio :
      (((j + 1 : ℕ) : ℝ)) /
          log (dyadicScale j : ℝ) ≤
        2 / log (2 : ℝ) := by
    rw [div_le_div_iff₀ hlogX hlog2, log_dyadicScale]
    push_cast
    have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hraw :=
    rpow_neg_le_ratio_rpow
      (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))
      hlogX hH
      (by linarith [mixedCanonicalCrossExponent_lt_neg_one] :
        0 ≤ -mixedCanonicalCrossExponent)
      hratio
  unfold mixedDyadicIndexConstant
  simpa using hraw

/-- Complete fixed constant in the summable bulk schedule profile. -/
def mixedCanonicalBulkProfileConstant : ℝ :=
  mixedDyadicIndexConstant * mixedScheduleLogConstant

theorem mixedCanonicalBulkProfileConstant_pos :
    0 < mixedCanonicalBulkProfileConstant := by
  unfold mixedCanonicalBulkProfileConstant
  exact mul_pos mixedDyadicIndexConstant_pos mixedScheduleLogConstant_pos

/-- In the bulk range `X ≤ Y`, the two negative convolution powers merge
to the certified summable cross exponent. -/
theorem mixedCanonicalGoodBulkMainBlock_le_profile
    {L N j : ℕ} {Kb Ko : ℝ}
    (hL : 3 ≤ L) (hdom : 32 * sieveRadius j ≤ j)
    (hnear : L ≤ 16 * dyadicScale j)
    (hgood : mixedScheduledGoodIndex L N j)
    (hbulk :
      dyadicScale j ≤
        N / (dyadicScale j * dyadicScale j)) :
    mixedBlockPrefactor L (dyadicScale j)
          sourceAnatomySlope Kb oddAnatomySlope Ko
          mixedSourceWeightBase mixedOddWeightBase *
        mixedScheduledMertensMain L
          mixedSourceWeightBase mixedOddWeightBase j *
        mixedBlockResidualBound L N (dyadicScale j)
          mixedSourceWeightBase mixedOddWeightBase ≤
      mixedCanonicalMainConstant Kb *
        mixedOddWeightBase ^ Ko * (N : ℝ) *
        log (L : ℝ) ^ mixedCanonicalOuterExponent *
        mixedCanonicalBulkProfileConstant *
        ((((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
  have hbase :=
    mixedCanonicalGoodMainBlock_le_convolution
      (Kb := Kb) (Ko := Ko) hL hdom hnear hgood
  have hj : 1 ≤ j := by
    have hz := hgood.1
    by_contra hj0
    have : j = 0 := Nat.eq_zero_of_not_pos hj0
    subst j
    simp [sieveCutoff, sieveCutoffExponent, sieveRadius,
      sieveHeight] at hz
  have hindex := log_dyadicScale_rpow_cross_le_index hj
  have hloss := scheduledLogLoss_sq_le_log_four hj
  have hlogX :
      0 < log (dyadicScale j : ℝ) :=
    log_pos (by
      exact_mod_cast (show 1 < dyadicScale j by
        exact hgood.1.trans hgood.2.2.1))
  have hmerge :
      log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent *
          log ((min (dyadicScale j)
            (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent =
        log (dyadicScale j : ℝ) ^
          mixedCanonicalCrossExponent := by
    rw [min_eq_left hbulk, ← Real.rpow_add hlogX,
      mixedCanonicalDyadic_add_residualExponent]
  have hprofile :
      log (dyadicScale j : ℝ) ^ mixedCanonicalCrossExponent *
          scheduledLogLoss j ^ (2 : ℝ) ≤
        mixedCanonicalBulkProfileConstant *
          ((((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
    calc
      log (dyadicScale j : ℝ) ^ mixedCanonicalCrossExponent *
            scheduledLogLoss j ^ (2 : ℝ)
          ≤
        (mixedDyadicIndexConstant *
            (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent)) *
          (mixedScheduleLogConstant *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) :=
        mul_le_mul hindex hloss
          (Real.rpow_nonneg
            (by linarith [scheduledLogLoss_one_le j]) _)
          (mul_nonneg mixedDyadicIndexConstant_pos.le
            (Real.rpow_nonneg (by positivity) _))
      _ = _ := by
        unfold mixedCanonicalBulkProfileConstant
        ring
  have hcoef0 :
      0 ≤ mixedCanonicalMainConstant Kb *
          mixedOddWeightBase ^ Ko * (N : ℝ) *
          log (L : ℝ) ^ mixedCanonicalOuterExponent := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mixedCanonicalMainConstant_pos Kb).le
          (Real.rpow_nonneg
            (by linarith [mixedOddWeightBase_gt_one]) _))
        (Nat.cast_nonneg N))
      (Real.rpow_nonneg
        (log_pos (by exact_mod_cast (show 1 < L by omega))).le _)
  exact hbase.trans
    (by
      calc
        mixedCanonicalMainConstant Kb *
              mixedOddWeightBase ^ Ko * (N : ℝ) *
              log (dyadicScale j : ℝ) ^
                mixedCanonicalDyadicExponent *
              log ((min (dyadicScale j)
                (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
                  mixedCanonicalResidualExponent *
              log (L : ℝ) ^ mixedCanonicalOuterExponent *
              scheduledLogLoss j ^ (2 : ℝ)
            =
          (mixedCanonicalMainConstant Kb *
              mixedOddWeightBase ^ Ko * (N : ℝ) *
              log (L : ℝ) ^ mixedCanonicalOuterExponent) *
            ((log (dyadicScale j : ℝ) ^
                mixedCanonicalDyadicExponent *
              log ((min (dyadicScale j)
                (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
                  mixedCanonicalResidualExponent) *
              scheduledLogLoss j ^ (2 : ℝ)) := by ring
        _ =
          (mixedCanonicalMainConstant Kb *
              mixedOddWeightBase ^ Ko * (N : ℝ) *
              log (L : ℝ) ^ mixedCanonicalOuterExponent) *
            (log (dyadicScale j : ℝ) ^
                mixedCanonicalCrossExponent *
              scheduledLogLoss j ^ (2 : ℝ)) := by rw [hmerge]
        _ ≤
          (mixedCanonicalMainConstant Kb *
              mixedOddWeightBase ^ Ko * (N : ℝ) *
              log (L : ℝ) ^ mixedCanonicalOuterExponent) *
            (mixedCanonicalBulkProfileConstant *
              ((((j + 1 : ℕ) : ℝ) ^
                  mixedCanonicalCrossExponent) *
                log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hprofile hcoef0
        _ = _ := by ring)

/-- The canonical bulk profile is summable. -/
theorem summable_mixedCanonicalBulkProfile :
    Summable (fun j : ℕ ↦
      (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
        log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) :=
  summable_nat_add_one_rpow_mul_log_rpow
    mixedCanonicalCrossExponent_lt_neg_one (by norm_num)

/-- Euler-main contribution restricted to dominant, nonempty good blocks
in the bulk range `X ≤ Y`. -/
def mixedCanonicalBulkMainContribution
    (L N : ℕ) (Kb Ko : ℝ) (j : ℕ) : ℝ :=
  if 32 * sieveRadius j ≤ j ∧
      L ≤ 16 * dyadicScale j ∧
      mixedScheduledGoodIndex L N j ∧
      dyadicScale j ≤ N / (dyadicScale j * dyadicScale j) then
    mixedBlockPrefactor L (dyadicScale j)
        sourceAnatomySlope Kb oddAnatomySlope Ko
        mixedSourceWeightBase mixedOddWeightBase *
      mixedScheduledMertensMain L
        mixedSourceWeightBase mixedOddWeightBase j *
      mixedBlockResidualBound L N (dyadicScale j)
        mixedSourceWeightBase mixedOddWeightBase
  else 0

/-- Uniformly in `N`, the late bulk Euler-main terms consume an
arbitrarily small multiple of their explicit outside coefficient. -/
theorem exists_mixedCanonicalBulkMain_tail_le
    (Kb : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ J' ≥ J, ∀ L N M : ℕ, 3 ≤ L →
      (∑ j ∈ Ico J' M,
        mixedCanonicalBulkMainContribution
          L N Kb (oddBudget L) j) ≤
        ε *
          (mixedCanonicalMainConstant Kb *
            mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
            log (L : ℝ) ^ mixedCanonicalOuterExponent) := by
  have hbulkC : 0 < mixedCanonicalBulkProfileConstant :=
    mixedCanonicalBulkProfileConstant_pos
  obtain ⟨J, hJ⟩ :=
    exists_powerLogProfile_tail_lt
      mixedCanonicalCrossExponent_lt_neg_one
      (by norm_num : (0 : ℝ) ≤ 4)
      (div_pos hε hbulkC)
  refine ⟨J, ?_⟩
  intro J' hJJ L N M hL
  let C : ℝ :=
    mixedCanonicalMainConstant Kb *
      mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
      log (L : ℝ) ^ mixedCanonicalOuterExponent
  have hlogL :
      0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mixedCanonicalMainConstant_pos Kb).le
          (Real.rpow_nonneg
            (by linarith [mixedOddWeightBase_gt_one]) _))
        (Nat.cast_nonneg N))
      (Real.rpow_nonneg hlogL.le _)
  have hpoint :
      ∀ j : ℕ,
        mixedCanonicalBulkMainContribution
            L N Kb (oddBudget L) j ≤
          C * mixedCanonicalBulkProfileConstant *
            ((((j + 1 : ℕ) : ℝ) ^
                mixedCanonicalCrossExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
    intro j
    unfold mixedCanonicalBulkMainContribution
    split_ifs with hj
    · rcases hj with ⟨hdom, hnear, hgood, hbulk⟩
      simpa [C, mul_assoc] using
        (mixedCanonicalGoodBulkMainBlock_le_profile
          (Kb := Kb) (Ko := oddBudget L)
          hL hdom hnear hgood hbulk)
    · have hprofile0 :
          0 ≤ (((j + 1 : ℕ) : ℝ) ^
                mixedCanonicalCrossExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) :=
        mul_nonneg
          (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)
      exact mul_nonneg
        (mul_nonneg hC0 mixedCanonicalBulkProfileConstant_pos.le)
        hprofile0
  have hprofileTail :
      (∑ j ∈ Ico J' M,
        (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalCrossExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) ≤
        ε / mixedCanonicalBulkProfileConstant :=
    (hJ J' hJJ M).le
  calc
    (∑ j ∈ Ico J' M,
        mixedCanonicalBulkMainContribution
          L N Kb (oddBudget L) j)
        ≤
      ∑ j ∈ Ico J' M,
        C * mixedCanonicalBulkProfileConstant *
          ((((j + 1 : ℕ) : ℝ) ^
              mixedCanonicalCrossExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
          apply sum_le_sum
          intro j hj
          exact hpoint j
    _ =
      (C * mixedCanonicalBulkProfileConstant) *
        (∑ j ∈ Ico J' M,
          (((j + 1 : ℕ) : ℝ) ^
              mixedCanonicalCrossExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
          rw [mul_sum]
    _ ≤
      (C * mixedCanonicalBulkProfileConstant) *
        (ε / mixedCanonicalBulkProfileConstant) :=
      mul_le_mul_of_nonneg_left hprofileTail
        (mul_nonneg hC0 mixedCanonicalBulkProfileConstant_pos.le)
    _ = ε * C := by
      field_simp [mixedCanonicalBulkProfileConstant_pos.ne']
    _ = ε *
          (mixedCanonicalMainConstant Kb *
            mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
            log (L : ℝ) ^ mixedCanonicalOuterExponent) := by
      rfl

/-- Fixed constant in the finite-sieve error term, again with the moving
odd intercept factored out. -/
def mixedCanonicalErrorConstant (Kb : ℝ) : ℝ :=
  9 *
    (mixedSourceWeightBase ^ Kb *
      (5 : ℝ) ^ mixedCanonicalRegularityExponent) *
    mixedCanonicalResidualConstant

theorem mixedCanonicalErrorConstant_pos (Kb : ℝ) :
    0 < mixedCanonicalErrorConstant Kb := by
  unfold mixedCanonicalErrorConstant
  positivity [mixedSourceWeightBase_gt_one,
    mixedCanonicalResidualConstant_pos]

/-- The canonical regularity power of the dyadic logarithm is at most
the square of the scheduled index. -/
theorem log_dyadicScale_rpow_regularity_le_index_sq
    {j : ℕ} (hj : 1 ≤ j) :
    log (dyadicScale j : ℝ) ^
        mixedCanonicalRegularityExponent ≤
      (((j + 1 : ℕ) : ℝ) ^ 2) := by
  have hlogX : 0 < log (dyadicScale j : ℝ) := by
    rw [log_dyadicScale]
    positivity
  have hlogXIndex :
      log (dyadicScale j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    rw [log_dyadicScale]
    push_cast
    have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith [Real.log_two_lt_d9,
      Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hbase :=
    Real.rpow_le_rpow hlogX.le hlogXIndex
      mixedCanonicalRegularityExponent_nonneg
  have hone : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have hexponent :
      (((j + 1 : ℕ) : ℝ) ^
          mixedCanonicalRegularityExponent) ≤
        (((j + 1 : ℕ) : ℝ) ^ (2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hone
      mixedCanonicalRegularityExponent_lt_two.le
  exact hbase.trans
    (by simpa [Real.rpow_natCast] using hexponent)

/-- Pointwise summable envelope for the finite-sieve error on every good
block. -/
theorem mixedCanonicalGoodSieveErrorBlock_le_profile
    {L N j : ℕ} {Kb Ko : ℝ}
    (hL : 3 ≤ L) (hgood : mixedScheduledGoodIndex L N j) :
    mixedBlockPrefactor L (dyadicScale j)
          sourceAnatomySlope Kb oddAnatomySlope Ko
          mixedSourceWeightBase mixedOddWeightBase *
        mixedScheduledSieveError j *
        mixedBlockResidualBound L N (dyadicScale j)
          mixedSourceWeightBase mixedOddWeightBase ≤
      mixedCanonicalErrorConstant Kb *
        mixedOddWeightBase ^ Ko * (N : ℝ) *
        log (L : ℝ) ^ mixedCanonicalErrorOuterExponent *
        ((((j + 1 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)) := by
  have hX2 : 2 ≤ dyadicScale j :=
    hgood.1.trans hgood.2.2.1
  have hLX := hgood.2.1
  have hLY := hgood.2.2.2
  have hj : 1 ≤ j := by
    by_contra hj0
    have : j = 0 := Nat.eq_zero_of_not_pos hj0
    subst j
    have hz := hgood.1
    norm_num [sieveCutoff, sieveCutoffExponent, sieveRadius,
      sieveHeight] at hz
  have hpref :=
    mixedCanonicalBlockPrefactor_le_powers
      (Kb := Kb) (Ko := Ko) hL hX2
  have hres :=
    mixedCanonicalBlockResidualBound_le_powers hL hLX hLY
  have hindex :=
    log_dyadicScale_rpow_regularity_le_index_sq hj
  have hlogL :
      0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hT :
      L ≤ min (dyadicScale j)
        (N / (dyadicScale j * dyadicScale j)) :=
    le_min hLX hLY
  have hlogT :
      0 < log ((min (dyadicScale j)
        (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) :=
    log_pos (by exact_mod_cast (show
      1 < min (dyadicScale j)
        (N / (dyadicScale j * dyadicScale j)) by omega))
  have hlogLT :
      log (L : ℝ) ≤
        log ((min (dyadicScale j)
          (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using (show (0 : ℝ) < L by positivity))
      (by simpa only [Set.mem_Ioi] using
        (show (0 : ℝ) < min (dyadicScale j)
          (N / (dyadicScale j * dyadicScale j)) by
            exact_mod_cast (show 0 < min (dyadicScale j)
              (N / (dyadicScale j * dyadicScale j)) by omega)))
      (by exact_mod_cast hT)
  have htransition :
      log ((min (dyadicScale j)
          (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
            mixedCanonicalResidualExponent ≤
        log (L : ℝ) ^ mixedCanonicalResidualExponent :=
    Real.rpow_le_rpow_of_nonpos hlogL hlogLT
      mixedCanonicalResidualExponent_lt_zero.le
  have hprefR0 :
      0 ≤ mixedCanonicalPrefactorConstant Kb Ko *
        log (dyadicScale j : ℝ) ^
          mixedCanonicalRegularityExponent *
        log (L : ℝ) ^ (-mixedCanonicalRegularityExponent) := by
    exact mul_nonneg
      (mul_nonneg (mixedCanonicalPrefactorConstant_pos Kb Ko).le
        (Real.rpow_nonneg
          (log_pos (by exact_mod_cast (show
            1 < dyadicScale j by omega))).le _))
      (Real.rpow_nonneg hlogL.le _)
  have herror0 : 0 ≤ mixedScheduledSieveError j := by
    unfold mixedScheduledSieveError
    positivity
  have hres0 :
      0 ≤ mixedBlockResidualBound L N (dyadicScale j)
        mixedSourceWeightBase mixedOddWeightBase := by
    have hY3 :
        3 ≤ N / (dyadicScale j * dyadicScale j) :=
      hL.trans hLY
    have hlogY :
        0 < log (N / (dyadicScale j * dyadicScale j) : ℕ) :=
      log_pos (by exact_mod_cast (show
        1 < N / (dyadicScale j * dyadicScale j) by omega))
    unfold mixedBlockResidualBound
    dsimp only
    positivity
  have hscaled :
      mixedBlockPrefactor L (dyadicScale j)
            sourceAnatomySlope Kb oddAnatomySlope Ko
            mixedSourceWeightBase mixedOddWeightBase *
          mixedScheduledSieveError j *
          mixedBlockResidualBound L N (dyadicScale j)
            mixedSourceWeightBase mixedOddWeightBase ≤
        (mixedCanonicalPrefactorConstant Kb Ko *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalRegularityExponent *
            log (L : ℝ) ^
              (-mixedCanonicalRegularityExponent)) *
          mixedScheduledSieveError j *
          (mixedCanonicalResidualConstant *
            (N / (dyadicScale j * dyadicScale j) : ℕ) *
            log ((min (dyadicScale j)
              (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
                mixedCanonicalResidualExponent *
            log (L : ℝ) ^ (-mixedCanonicalS)) := by
    calc
      _ ≤
        (mixedCanonicalPrefactorConstant Kb Ko *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalRegularityExponent *
            log (L : ℝ) ^
              (-mixedCanonicalRegularityExponent)) *
          mixedScheduledSieveError j *
          mixedBlockResidualBound L N (dyadicScale j)
            mixedSourceWeightBase mixedOddWeightBase :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpref herror0) hres0
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left hres
          (mul_nonneg hprefR0 herror0)
  have hXYnat := dyadic_sq_mul_mixedResidualCutoff_le N j
  have hXY :
      (dyadicScale j : ℝ) ^ 2 *
          (N / (dyadicScale j * dyadicScale j) : ℕ) ≤
        (N : ℝ) := by
    have hcast :
        (((dyadicScale j * dyadicScale j) *
          (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ≤
            (N : ℝ) := by exact_mod_cast hXYnat
    simpa [pow_two] using hcast
  have hpowL :
      log (L : ℝ) ^ mixedCanonicalErrorOuterExponent =
        log (L : ℝ) ^ (-mixedCanonicalRegularityExponent) *
          log (L : ℝ) ^ (-mixedCanonicalS) *
          log (L : ℝ) ^ mixedCanonicalResidualExponent := by
    rw [show mixedCanonicalErrorOuterExponent =
        ((-mixedCanonicalRegularityExponent) + (-mixedCanonicalS)) +
          mixedCanonicalResidualExponent by
      unfold mixedCanonicalErrorOuterExponent
        mixedCanonicalResidualExponent
      ring,
      Real.rpow_add hlogL, Real.rpow_add hlogL]
  calc
    _ ≤
      (mixedCanonicalPrefactorConstant Kb Ko *
          log (dyadicScale j : ℝ) ^
            mixedCanonicalRegularityExponent *
          log (L : ℝ) ^
            (-mixedCanonicalRegularityExponent)) *
        mixedScheduledSieveError j *
        (mixedCanonicalResidualConstant *
          (N / (dyadicScale j * dyadicScale j) : ℕ) *
          log ((min (dyadicScale j)
            (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent *
          log (L : ℝ) ^ (-mixedCanonicalS)) := hscaled
    _ ≤
      mixedCanonicalErrorConstant Kb *
        mixedOddWeightBase ^ Ko * (N : ℝ) *
        log (L : ℝ) ^ mixedCanonicalErrorOuterExponent *
        ((((j + 1 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)) := by
      unfold mixedScheduledSieveError
      rw [hpowL]
      unfold mixedCanonicalPrefactorConstant
        mixedCanonicalErrorConstant
      let A : ℝ :=
        mixedSourceWeightBase ^ Kb *
          (5 : ℝ) ^ mixedCanonicalRegularityExponent
      let B : ℝ := mixedOddWeightBase ^ Ko
      let C : ℝ := mixedCanonicalResidualConstant
      let Q : ℝ :=
        log (L : ℝ) ^ (-mixedCanonicalRegularityExponent) *
          log (L : ℝ) ^ (-mixedCanonicalS)
      have hA0 : 0 ≤ A := by
        dsimp [A]
        exact mul_nonneg
          (Real.rpow_nonneg
            (by linarith [mixedSourceWeightBase_gt_one]) _)
          (Real.rpow_nonneg (by norm_num) _)
      have hB0 : 0 ≤ B := by
        dsimp [B]
        exact Real.rpow_nonneg
          (by linarith [mixedOddWeightBase_gt_one]) _
      have hC0 : 0 ≤ C := by
        exact mixedCanonicalResidualConstant_pos.le
      have hQ0 : 0 ≤ Q := by
        dsimp [Q]
        exact mul_nonneg
          (Real.rpow_nonneg hlogL.le _)
          (Real.rpow_nonneg hlogL.le _)
      have hden0 :
          0 ≤ (((j + 1 : ℕ) : ℝ) ^ 8) := by positivity
      have hlogX0 :
          0 ≤ log (dyadicScale j : ℝ) ^
            mixedCanonicalRegularityExponent :=
        Real.rpow_nonneg
          (log_pos (by exact_mod_cast (show
            1 < dyadicScale j by omega))).le _
      have hlogTpow0 :
          0 ≤ log ((min (dyadicScale j)
            (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent :=
        Real.rpow_nonneg hlogT.le _
      calc
        _ =
          (9 * A * B * C) *
            ((dyadicScale j : ℝ) ^ 2 *
              (N / (dyadicScale j * dyadicScale j) : ℕ)) *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalRegularityExponent *
            log ((min (dyadicScale j)
              (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
                mixedCanonicalResidualExponent *
            Q /
            (((j + 1 : ℕ) : ℝ) ^ 8) := by
              dsimp [Q]
              ring
        _ ≤
          (9 * A * B * C) * (N : ℝ) *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalRegularityExponent *
            log ((min (dyadicScale j)
              (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
                mixedCanonicalResidualExponent *
            Q /
            (((j + 1 : ℕ) : ℝ) ^ 8) := by
              gcongr
        _ ≤
          (9 * A * B * C) * (N : ℝ) *
            (((j + 1 : ℕ) : ℝ) ^ 2) *
            log ((min (dyadicScale j)
              (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ^
                mixedCanonicalResidualExponent *
            Q /
            (((j + 1 : ℕ) : ℝ) ^ 8) := by
              gcongr
        _ ≤
          (9 * A * B * C) * (N : ℝ) *
            (((j + 1 : ℕ) : ℝ) ^ 2) *
            log (L : ℝ) ^ mixedCanonicalResidualExponent *
            Q /
            (((j + 1 : ℕ) : ℝ) ^ 8) := by
              gcongr
        _ =
          (9 * A * C) * B * (N : ℝ) *
            (log (L : ℝ) ^ (-mixedCanonicalRegularityExponent) *
              log (L : ℝ) ^ (-mixedCanonicalS) *
              log (L : ℝ) ^ mixedCanonicalResidualExponent) *
            (((j + 1 : ℕ) : ℝ) ^ 2 /
              (((j + 1 : ℕ) : ℝ) ^ 8)) := by
              dsimp [Q]
              ring

/-- Algebraic identification of the error profile with a `p = -6`
power-log profile. -/
theorem mixedCanonicalErrorProfile_eq (j : ℕ) :
    (((j + 1 : ℕ) : ℝ) ^ (-6 : ℝ)) *
        log (((j + 1 : ℕ) : ℝ)) ^ (0 : ℝ) =
      (((j + 1 : ℕ) : ℝ) ^ 2) /
        (((j + 1 : ℕ) : ℝ) ^ 8) := by
  have hx : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  rw [Real.rpow_zero, mul_one, Real.rpow_neg hx.le]
  field_simp
  simp

/-- The normalized mixed sieve-error profile is summable. -/
theorem summable_mixedCanonicalErrorProfile :
    Summable (fun j : ℕ ↦
      (((j + 1 : ℕ) : ℝ) ^ 2) /
        (((j + 1 : ℕ) : ℝ) ^ 8)) := by
  have hsum :=
    summable_nat_add_one_rpow_mul_log_rpow
      (p := -6) (m := 0) (by norm_num) (by norm_num)
  exact hsum.congr mixedCanonicalErrorProfile_eq

/-- Late finite segments of the normalized error profile have arbitrarily
small mass. -/
theorem exists_mixedCanonicalErrorProfile_tail_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ J' ≥ J, ∀ M : ℕ,
      (∑ j ∈ Ico J' M,
        (((j + 1 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)) < ε := by
  obtain ⟨J, hJ⟩ :=
    exists_powerLogProfile_tail_lt
      (p := -6) (m := 0) (by norm_num) (by norm_num) hε
  refine ⟨J, ?_⟩
  intro J' hJJ M
  simpa only [mixedCanonicalErrorProfile_eq] using hJ J' hJJ M

/-- Finite-sieve error contribution restricted to good blocks. -/
def mixedCanonicalGoodSieveErrorContribution
    (L N : ℕ) (Kb Ko : ℝ) (j : ℕ) : ℝ :=
  if mixedScheduledGoodIndex L N j then
    mixedBlockPrefactor L (dyadicScale j)
        sourceAnatomySlope Kb oddAnatomySlope Ko
        mixedSourceWeightBase mixedOddWeightBase *
      mixedScheduledSieveError j *
      mixedBlockResidualBound L N (dyadicScale j)
        mixedSourceWeightBase mixedOddWeightBase
  else 0

/-- Uniformly in `N`, late good-block finite-sieve errors consume an
arbitrarily small multiple of their explicit outside coefficient. -/
theorem exists_mixedCanonicalGoodSieveError_tail_le
    (Kb : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ J' ≥ J, ∀ L N M : ℕ, 3 ≤ L →
      (∑ j ∈ Ico J' M,
        mixedCanonicalGoodSieveErrorContribution
          L N Kb (oddBudget L) j) ≤
        ε *
          (mixedCanonicalErrorConstant Kb *
            mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
            log (L : ℝ) ^ mixedCanonicalErrorOuterExponent) := by
  obtain ⟨J, hJ⟩ :=
    exists_mixedCanonicalErrorProfile_tail_lt hε
  refine ⟨J, ?_⟩
  intro J' hJJ L N M hL
  let C : ℝ :=
    mixedCanonicalErrorConstant Kb *
      mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
      log (L : ℝ) ^ mixedCanonicalErrorOuterExponent
  have hlogL :
      0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mixedCanonicalErrorConstant_pos Kb).le
          (Real.rpow_nonneg
            (by linarith [mixedOddWeightBase_gt_one]) _))
        (Nat.cast_nonneg N))
      (Real.rpow_nonneg hlogL.le _)
  have hpoint :
      ∀ j : ℕ,
        mixedCanonicalGoodSieveErrorContribution
            L N Kb (oddBudget L) j ≤
          C * ((((j + 1 : ℕ) : ℝ) ^ 2) /
            (((j + 1 : ℕ) : ℝ) ^ 8)) := by
    intro j
    unfold mixedCanonicalGoodSieveErrorContribution
    split_ifs with hgood
    · simpa [C, mul_assoc] using
        (mixedCanonicalGoodSieveErrorBlock_le_profile
          (Kb := Kb) (Ko := oddBudget L) hL hgood)
    · exact mul_nonneg hC0 (div_nonneg (by positivity) (by positivity))
  have htail :
      (∑ j ∈ Ico J' M,
        (((j + 1 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)) ≤ ε :=
    (hJ J' hJJ M).le
  calc
    (∑ j ∈ Ico J' M,
        mixedCanonicalGoodSieveErrorContribution
          L N Kb (oddBudget L) j)
        ≤
      ∑ j ∈ Ico J' M,
        C * ((((j + 1 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)) := by
            apply sum_le_sum
            intro j hj
            exact hpoint j
    _ =
      C * (∑ j ∈ Ico J' M,
        (((j + 1 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)) := by
            rw [mul_sum]
    _ ≤ C * ε := mul_le_mul_of_nonneg_left htail hC0
    _ = ε *
          (mixedCanonicalErrorConstant Kb *
            mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
            log (L : ℝ) ^ mixedCanonicalErrorOuterExponent) := by
      dsimp [C]
      ring

/-- The residual factor used in the good scheduled branch, and the trivial
interval-length bound used in the exact-residual fallback branch. -/
def mixedScheduledResidualEnvelope
    (L N : ℕ) (qb qo : ℝ) (j : ℕ) : ℝ :=
  if mixedScheduledGoodIndex L N j then
    mixedBlockResidualBound L N (dyadicScale j) qb qo
  else
    (N / (dyadicScale j * dyadicScale j) : ℕ)

theorem mixedScheduledMertensMain_add_error_nonneg
    (L j : ℕ) (qb qo : ℝ) :
    0 ≤ mixedScheduledMertensMain L qb qo j +
      mixedScheduledSieveError j := by
  unfold mixedScheduledMertensMain mixedScheduledSieveError
  positivity

theorem mixedBlockResidualBound_nonneg_of_good
    {L N j : ℕ} {qb qo : ℝ}
    (hL : 3 ≤ L) (hj : mixedScheduledGoodIndex L N j) :
    0 ≤ mixedBlockResidualBound L N (dyadicScale j) qb qo := by
  have hY3 :
      3 ≤ N / (dyadicScale j * dyadicScale j) :=
    hL.trans hj.2.2.2
  have hlogY :
      0 < log (N / (dyadicScale j * dyadicScale j) : ℕ) :=
    log_pos (by exact_mod_cast (show
      1 < N / (dyadicScale j * dyadicScale j) by omega))
  unfold mixedBlockResidualBound
  dsimp only
  positivity

theorem mixedScheduledResidualEnvelope_nonneg
    {L N j : ℕ} {qb qo : ℝ} (hL : 3 ≤ L) :
    0 ≤ mixedScheduledResidualEnvelope L N qb qo j := by
  unfold mixedScheduledResidualEnvelope
  split_ifs with hj
  · exact mixedBlockResidualBound_nonneg_of_good hL hj
  · positivity

/-- Once the scheduled cutoff is unclamped and available, the full
three-way block bound is controlled by one common analytic envelope. -/
theorem mixedScheduledBlockBound_le_analyticEnvelope
    {L N j : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hqb : 1 < qb) (hqo : 1 < qo)
    (hcutoff : 2 ≤ sieveCutoff j)
    (havailable : mixedScheduledResidualAvailable L j)
    (hbox :
      mixedAllCutoffSharpBoxBound
          L (sieveCutoff j) (dyadicScale j) (sieveRadius j) qb qo ≤
        mixedScheduledMertensMain L qb qo j +
          mixedScheduledSieveError j) :
    mixedScheduledBlockBound L N Ab Kb Ao Ko qb qo j ≤
      mixedBlockPrefactor L (dyadicScale j)
          Ab Kb Ao Ko qb qo *
        (mixedScheduledMertensMain L qb qo j +
          mixedScheduledSieveError j) *
        mixedScheduledResidualEnvelope L N qb qo j := by
  have hprefactor :
      0 ≤ mixedBlockPrefactor L (dyadicScale j)
        Ab Kb Ao Ko qb qo :=
    mixedBlockPrefactor_nonneg hL
      (by simpa [dyadicScale] using Nat.one_le_pow j 2 (by norm_num))
      hqb hqo
  have hmain :
      0 ≤ mixedScheduledMertensMain L qb qo j +
        mixedScheduledSieveError j :=
    mixedScheduledMertensMain_add_error_nonneg L j qb qo
  by_cases hgood : mixedScheduledGoodIndex L N j
  · rw [mixedScheduledBlockBound, if_pos hgood,
      mixedScheduledResidualEnvelope, if_pos hgood]
    unfold mixedScheduledExplicitBlockBound
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbox hprefactor)
      (mixedBlockResidualBound_nonneg_of_good hL hgood)
  · rw [mixedScheduledBlockBound, if_neg hgood,
      mixedScheduledFallbackBlockBound, if_pos havailable,
      mixedScheduledResidualEnvelope, if_neg hgood,
      mixedScheduledExactResidualBlockBound,
      mixedClampedSieveCutoff_eq hcutoff]
    have hexact0 :
        0 ≤ mixedExactResidualMoment L N (dyadicScale j) qb qo :=
      mixedExactResidualMoment_nonneg _ _ _
        (le_trans (by norm_num) hqb.le)
        (le_trans (by norm_num) hqo.le)
    calc
      mixedBlockPrefactor L (dyadicScale j) Ab Kb Ao Ko qb qo *
            mixedAllCutoffSharpBoxBound L (sieveCutoff j)
              (dyadicScale j) (sieveRadius j) qb qo *
            mixedExactResidualMoment L N (dyadicScale j) qb qo
          ≤
        mixedBlockPrefactor L (dyadicScale j) Ab Kb Ao Ko qb qo *
            (mixedScheduledMertensMain L qb qo j +
              mixedScheduledSieveError j) *
            mixedExactResidualMoment L N (dyadicScale j) qb qo :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbox hprefactor) hexact0
      _ ≤
        mixedBlockPrefactor L (dyadicScale j) Ab Kb Ao Ko qb qo *
            (mixedScheduledMertensMain L qb qo j +
              mixedScheduledSieveError j) *
            (N / (dyadicScale j * dyadicScale j) : ℕ) :=
        mul_le_mul_of_nonneg_left
          (mixedExactResidualMoment_le_length hqb hqo)
          (mul_nonneg hprefactor hmain)

/-- The empty-block refinement is bounded by the same common envelope. -/
theorem mixedRefinedScheduledBlockBound_le_analyticEnvelope
    {L N j : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hqb : 1 < qb) (hqo : 1 < qo)
    (hcutoff : 2 ≤ sieveCutoff j)
    (havailable : mixedScheduledResidualAvailable L j)
    (hbox :
      mixedAllCutoffSharpBoxBound
          L (sieveCutoff j) (dyadicScale j) (sieveRadius j) qb qo ≤
        mixedScheduledMertensMain L qb qo j +
          mixedScheduledSieveError j) :
    mixedRefinedScheduledBlockBound L N Ab Kb Ao Ko qb qo j ≤
      mixedBlockPrefactor L (dyadicScale j)
          Ab Kb Ao Ko qb qo *
        (mixedScheduledMertensMain L qb qo j +
          mixedScheduledSieveError j) *
        mixedScheduledResidualEnvelope L N qb qo j := by
  by_cases hempty : 16 * dyadicScale j < L
  · rw [mixedRefinedScheduledBlockBound, if_pos hempty]
    exact mul_nonneg
      (mul_nonneg
        (mixedBlockPrefactor_nonneg hL
          (by simpa [dyadicScale] using
            Nat.one_le_pow j 2 (by norm_num))
          hqb hqo)
        (mixedScheduledMertensMain_add_error_nonneg L j qb qo))
      (mixedScheduledResidualEnvelope_nonneg hL)
  · rw [mixedRefinedScheduledBlockBound, if_neg hempty]
    exact mixedScheduledBlockBound_le_analyticEnvelope
      hL hqb hqo hcutoff havailable hbox

/-- All branch conditions needed by the common mixed envelope hold
eventually, uniformly in `N` and in the regularity thresholds. -/
theorem eventually_mixedRefinedScheduledBlockBound_le_analyticEnvelope
    {L : ℕ} (hL : 3 ≤ L) (N : ℕ)
    (Ab Kb Ao Ko qb qo : ℝ)
    (hqb : 1 < qb) (hqo : 1 < qo) :
    ∀ᶠ j : ℕ in atTop,
      mixedRefinedScheduledBlockBound
          L N Ab Kb Ao Ko qb qo j ≤
        mixedBlockPrefactor L (dyadicScale j)
            Ab Kb Ao Ko qb qo *
          (mixedScheduledMertensMain L qb qo j +
            mixedScheduledSieveError j) *
          mixedScheduledResidualEnvelope L N qb qo j := by
  filter_upwards
    [eventually_sieveSchedule_dominates,
      eventually_mixedAllCutoffSharpBoxBound_le_main_add_error L qb qo,
      eventually_ge_atTop 1] with j hdom hbox hj
  exact mixedRefinedScheduledBlockBound_le_analyticEnvelope
    hL hqb hqo
    (two_le_sieveCutoff_of_dominance hdom)
    (mixedScheduledResidualAvailable_of_one_le_index hj)
    hbox

/-- A finite-index form of the eventual estimate, suitable for splitting
any scheduled sum into a fixed initial segment and an analytic tail. -/
theorem exists_mixedScheduledTail_start
    {L : ℕ} (hL : 3 ≤ L)
    (Ab Kb Ao Ko qb qo : ℝ)
    (hqb : 1 < qb) (hqo : 1 < qo) :
    ∃ J : ℕ, ∀ N M : ℕ,
      (∑ j ∈ Ico J M,
        mixedRefinedScheduledBlockBound
          L N Ab Kb Ao Ko qb qo j) ≤
      ∑ j ∈ Ico J M,
        mixedBlockPrefactor L (dyadicScale j)
            Ab Kb Ao Ko qb qo *
          (mixedScheduledMertensMain L qb qo j +
            mixedScheduledSieveError j) *
          mixedScheduledResidualEnvelope L N qb qo j := by
  have hevent :
      ∀ᶠ j : ℕ in atTop, ∀ N : ℕ,
        mixedRefinedScheduledBlockBound
            L N Ab Kb Ao Ko qb qo j ≤
          mixedBlockPrefactor L (dyadicScale j)
              Ab Kb Ao Ko qb qo *
            (mixedScheduledMertensMain L qb qo j +
              mixedScheduledSieveError j) *
            mixedScheduledResidualEnvelope L N qb qo j := by
    filter_upwards
      [eventually_sieveSchedule_dominates,
        eventually_mixedAllCutoffSharpBoxBound_le_main_add_error L qb qo,
        eventually_ge_atTop 1] with j hdom hbox hj
    intro N
    exact mixedRefinedScheduledBlockBound_le_analyticEnvelope
      hL hqb hqo
      (two_le_sieveCutoff_of_dominance hdom)
      (mixedScheduledResidualAvailable_of_one_le_index hj)
      hbox
  rw [eventually_atTop] at hevent
  rcases hevent with ⟨J, hJ⟩
  refine ⟨J, ?_⟩
  intro N M
  apply sum_le_sum
  intro j hj
  exact hJ j (mem_Ico.mp hj).1 N

/-- Canonical specialization of the analytic tail reduction.  This is the
tail of the mixed sum appearing verbatim in `ScheduledReduction`. -/
theorem exists_canonicalMixedScheduledTail_start
    {L : ℕ} (hL : 3 ≤ L) (Kb Ko : ℝ) :
    ∃ J : ℕ, ∀ N M : ℕ,
      (∑ j ∈ Ico J M,
        mixedRefinedScheduledBlockBound
          L N sourceAnatomySlope Kb oddAnatomySlope Ko
            mixedSourceWeightBase mixedOddWeightBase j) ≤
      ∑ j ∈ Ico J M,
        mixedBlockPrefactor L (dyadicScale j)
            sourceAnatomySlope Kb oddAnatomySlope Ko
            mixedSourceWeightBase mixedOddWeightBase *
          (mixedScheduledMertensMain L
              mixedSourceWeightBase mixedOddWeightBase j +
            mixedScheduledSieveError j) *
          mixedScheduledResidualEnvelope L N
            mixedSourceWeightBase mixedOddWeightBase j :=
  exists_mixedScheduledTail_start hL
    sourceAnatomySlope Kb oddAnatomySlope Ko
    mixedSourceWeightBase mixedOddWeightBase
    mixedSourceWeightBase_gt_one mixedOddWeightBase_gt_one

/-- The full canonical scheduled sum is therefore an exact finite initial
segment plus the common analytic tail. -/
theorem exists_canonicalMixedScheduledFullSum_split
    {L : ℕ} (hL : 3 ≤ L) (Kb Ko : ℝ) :
    ∃ J : ℕ, ∀ N M : ℕ, J ≤ M →
      (∑ j ∈ range M,
        mixedRefinedScheduledBlockBound
          L N sourceAnatomySlope Kb oddAnatomySlope Ko
            mixedSourceWeightBase mixedOddWeightBase j) ≤
      (∑ j ∈ range J,
        mixedRefinedScheduledBlockBound
          L N sourceAnatomySlope Kb oddAnatomySlope Ko
            mixedSourceWeightBase mixedOddWeightBase j) +
      ∑ j ∈ Ico J M,
        mixedBlockPrefactor L (dyadicScale j)
            sourceAnatomySlope Kb oddAnatomySlope Ko
            mixedSourceWeightBase mixedOddWeightBase *
          (mixedScheduledMertensMain L
              mixedSourceWeightBase mixedOddWeightBase j +
            mixedScheduledSieveError j) *
          mixedScheduledResidualEnvelope L N
            mixedSourceWeightBase mixedOddWeightBase j := by
  rcases exists_canonicalMixedScheduledTail_start hL Kb Ko with
    ⟨J, hJ⟩
  refine ⟨J, ?_⟩
  intro N M hJM
  rw [← sum_range_add_sum_Ico
    (fun j ↦ mixedRefinedScheduledBlockBound
      L N sourceAnatomySlope Kb oddAnatomySlope Ko
        mixedSourceWeightBase mixedOddWeightBase j) hJM]
  exact add_le_add le_rfl (hJ N M)

/-- Pointwise record that both finite-sieve errors satisfy their target
bounds. -/
def mixedCanonicalScheduleErrorsHold (j : ℕ) : Prop :=
  scheduledFactorialTail j ≤
      1 / (((j + 1 : ℕ) : ℝ) ^ 8) ∧
    scheduledPolynomialBoundary j ≤
      (dyadicScale j : ℝ) ^ 2 /
        (((j + 1 : ℕ) : ℝ) ^ 8)

instance mixedCanonicalScheduleErrorsHoldDecidable (j : ℕ) :
    Decidable (mixedCanonicalScheduleErrorsHold j) :=
  Classical.propDecidable _

/-- The unresolved canonical contribution: before the schedule is valid it
keeps the refined term literally; afterward it keeps only the terminal
Euler main term `X > Y`. -/
def mixedCanonicalUnresolvedBlock
    (L N : ℕ) (Kb Ko : ℝ) (j : ℕ) : ℝ :=
  if mixedCanonicalScheduleErrorsHold j ∧
      32 * sieveRadius j ≤ j ∧
      L ≤ 16 * dyadicScale j ∧
      mixedScheduledGoodIndex L N j then
    if dyadicScale j ≤
        N / (dyadicScale j * dyadicScale j) then
      0
    else
      mixedBlockPrefactor L (dyadicScale j)
          sourceAnatomySlope Kb oddAnatomySlope Ko
          mixedSourceWeightBase mixedOddWeightBase *
        mixedScheduledMertensMain L
          mixedSourceWeightBase mixedOddWeightBase j *
        mixedBlockResidualBound L N (dyadicScale j)
          mixedSourceWeightBase mixedOddWeightBase
  else
    mixedRefinedScheduledBlockBound
      L N sourceAnatomySlope Kb oddAnatomySlope Ko
        mixedSourceWeightBase mixedOddWeightBase j

theorem mixedCanonicalBulkMainContribution_nonneg
    {L N j : ℕ} {Kb Ko : ℝ} (hL : 3 ≤ L) :
    0 ≤ mixedCanonicalBulkMainContribution L N Kb Ko j := by
  unfold mixedCanonicalBulkMainContribution
  split_ifs with hj
  · rcases hj with ⟨_hdom, _hnear, hgood, _hbulk⟩
    exact mul_nonneg
      (mul_nonneg
        (mixedBlockPrefactor_nonneg hL
          (by simpa [dyadicScale] using
            Nat.one_le_pow j 2 (by norm_num))
          mixedSourceWeightBase_gt_one
          mixedOddWeightBase_gt_one)
        (by unfold mixedScheduledMertensMain; positivity))
      (mixedBlockResidualBound_nonneg_of_good hL hgood)
  · norm_num

theorem mixedCanonicalGoodSieveErrorContribution_nonneg
    {L N j : ℕ} {Kb Ko : ℝ} (hL : 3 ≤ L) :
    0 ≤ mixedCanonicalGoodSieveErrorContribution L N Kb Ko j := by
  unfold mixedCanonicalGoodSieveErrorContribution
  split_ifs with hgood
  · exact mul_nonneg
      (mul_nonneg
        (mixedBlockPrefactor_nonneg hL
          (by simpa [dyadicScale] using
            Nat.one_le_pow j 2 (by norm_num))
          mixedSourceWeightBase_gt_one
          mixedOddWeightBase_gt_one)
        (by unfold mixedScheduledSieveError; positivity))
      (mixedBlockResidualBound_nonneg_of_good hL hgood)
  · norm_num

/-- Exact pointwise decomposition into the two resolved good-block pieces
and an explicit transition/terminal remainder. -/
theorem mixedRefinedScheduledBlockBound_le_resolved_add_unresolved
    {L N j : ℕ} {Kb Ko : ℝ} (hL : 3 ≤ L) :
    mixedRefinedScheduledBlockBound
        L N sourceAnatomySlope Kb oddAnatomySlope Ko
          mixedSourceWeightBase mixedOddWeightBase j ≤
      mixedCanonicalBulkMainContribution L N Kb Ko j +
        mixedCanonicalGoodSieveErrorContribution L N Kb Ko j +
        mixedCanonicalUnresolvedBlock L N Kb Ko j := by
  have hbulk0 :=
    mixedCanonicalBulkMainContribution_nonneg
      (L := L) (N := N) (j := j) (Kb := Kb) (Ko := Ko) hL
  have herror0 :=
    mixedCanonicalGoodSieveErrorContribution_nonneg
      (L := L) (N := N) (j := j) (Kb := Kb) (Ko := Ko) hL
  by_cases hschedule :
      mixedCanonicalScheduleErrorsHold j ∧
        32 * sieveRadius j ≤ j ∧
        L ≤ 16 * dyadicScale j ∧
        mixedScheduledGoodIndex L N j
  · rcases hschedule with
      ⟨herrors, hdom, hnear, hgood⟩
    have hnotempty : ¬16 * dyadicScale j < L := by omega
    have hbox :
        mixedAllCutoffSharpBoxBound L (sieveCutoff j)
            (dyadicScale j) (sieveRadius j)
            mixedSourceWeightBase mixedOddWeightBase ≤
          mixedScheduledMertensMain L
              mixedSourceWeightBase mixedOddWeightBase j +
            mixedScheduledSieveError j :=
      mixedAllCutoffSharpBoxBound_le_main_add_error
        herrors.1 herrors.2
    have hpref0 :
        0 ≤ mixedBlockPrefactor L (dyadicScale j)
          sourceAnatomySlope Kb oddAnatomySlope Ko
          mixedSourceWeightBase mixedOddWeightBase :=
      mixedBlockPrefactor_nonneg hL
        (by simpa [dyadicScale] using
          Nat.one_le_pow j 2 (by norm_num))
        mixedSourceWeightBase_gt_one mixedOddWeightBase_gt_one
    have hres0 :
        0 ≤ mixedBlockResidualBound L N (dyadicScale j)
          mixedSourceWeightBase mixedOddWeightBase :=
      mixedBlockResidualBound_nonneg_of_good hL hgood
    have hrefined :
        mixedRefinedScheduledBlockBound
            L N sourceAnatomySlope Kb oddAnatomySlope Ko
              mixedSourceWeightBase mixedOddWeightBase j ≤
          mixedBlockPrefactor L (dyadicScale j)
              sourceAnatomySlope Kb oddAnatomySlope Ko
              mixedSourceWeightBase mixedOddWeightBase *
            mixedScheduledMertensMain L
              mixedSourceWeightBase mixedOddWeightBase j *
            mixedBlockResidualBound L N (dyadicScale j)
              mixedSourceWeightBase mixedOddWeightBase +
          mixedBlockPrefactor L (dyadicScale j)
              sourceAnatomySlope Kb oddAnatomySlope Ko
              mixedSourceWeightBase mixedOddWeightBase *
            mixedScheduledSieveError j *
            mixedBlockResidualBound L N (dyadicScale j)
              mixedSourceWeightBase mixedOddWeightBase := by
      rw [mixedRefinedScheduledBlockBound, if_neg hnotempty,
        mixedScheduledBlockBound, if_pos hgood]
      unfold mixedScheduledExplicitBlockBound
      calc
        _ ≤
          mixedBlockPrefactor L (dyadicScale j)
              sourceAnatomySlope Kb oddAnatomySlope Ko
              mixedSourceWeightBase mixedOddWeightBase *
            (mixedScheduledMertensMain L
                mixedSourceWeightBase mixedOddWeightBase j +
              mixedScheduledSieveError j) *
            mixedBlockResidualBound L N (dyadicScale j)
              mixedSourceWeightBase mixedOddWeightBase :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hbox hpref0) hres0
        _ = _ := by ring
    by_cases hbulk :
        dyadicScale j ≤
          N / (dyadicScale j * dyadicScale j)
    · unfold mixedCanonicalBulkMainContribution
        mixedCanonicalGoodSieveErrorContribution
        mixedCanonicalUnresolvedBlock
      rw [if_pos ⟨hdom, hnear, hgood, hbulk⟩,
        if_pos hgood, if_pos
          ⟨herrors, hdom, hnear, hgood⟩, if_pos hbulk]
      linarith
    · unfold mixedCanonicalBulkMainContribution
        mixedCanonicalGoodSieveErrorContribution
        mixedCanonicalUnresolvedBlock
      rw [if_neg (by
          intro h
          exact hbulk h.2.2.2),
        if_pos hgood, if_pos
          ⟨herrors, hdom, hnear, hgood⟩, if_neg hbulk]
      linarith
  · unfold mixedCanonicalUnresolvedBlock
    rw [if_neg hschedule]
    linarith

/-- Finite-sum version of the resolved/unresolved decomposition. -/
theorem sum_mixedRefinedScheduledBlockBound_le_resolved_add_unresolved
    {L N M : ℕ} {Kb Ko : ℝ} (hL : 3 ≤ L) :
    (∑ j ∈ range M,
      mixedRefinedScheduledBlockBound
        L N sourceAnatomySlope Kb oddAnatomySlope Ko
          mixedSourceWeightBase mixedOddWeightBase j) ≤
      (∑ j ∈ range M,
        mixedCanonicalBulkMainContribution L N Kb Ko j) +
      (∑ j ∈ range M,
        mixedCanonicalGoodSieveErrorContribution L N Kb Ko j) +
      ∑ j ∈ range M,
        mixedCanonicalUnresolvedBlock L N Kb Ko j := by
  calc
    _ ≤ ∑ j ∈ range M,
        (mixedCanonicalBulkMainContribution L N Kb Ko j +
          mixedCanonicalGoodSieveErrorContribution L N Kb Ko j +
          mixedCanonicalUnresolvedBlock L N Kb Ko j) := by
      apply sum_le_sum
      intro j hj
      exact mixedRefinedScheduledBlockBound_le_resolved_add_unresolved hL
    _ = _ := by
      rw [sum_add_distrib, sum_add_distrib]

/-- Every fixed unresolved prefix vanishes exactly once `L` is large,
uniformly in `N` and with the moving choice `Ko = oddBudget L`. -/
theorem eventually_mixedCanonicalUnresolved_prefix_eq_zero
    (J : ℕ) (Kb : ℝ) :
    ∀ᶠ L : ℕ in atTop, ∀ N : ℕ,
      (∑ j ∈ range J,
        mixedCanonicalUnresolvedBlock
          L N Kb (oddBudget L) j) = 0 := by
  filter_upwards
    [eventually_gt_atTop (16 * dyadicScale J)] with L hfar
  intro N
  apply sum_eq_zero
  intro j hj
  have hjJ : j ≤ J :=
    Nat.le_of_lt (mem_range.mp hj)
  have hscale :
      16 * dyadicScale j < L :=
    (Nat.mul_le_mul_left 16 (dyadicScale_mono hjJ)).trans_lt hfar
  have hnear : ¬L ≤ 16 * dyadicScale j := by omega
  unfold mixedCanonicalUnresolvedBlock
  rw [if_neg (by
      intro h
      exact hnear h.2.2.1)]
  rw [mixedRefinedScheduledBlockBound, if_pos hscale]

/-- The certified exponent decomposes into the regularity prefactor, the
three-form Euler product, and the residual Euler product. -/
theorem mixedCanonicalCrossExponent_decomposition :
    mixedCanonicalCrossExponent =
      (sourceAnatomySlope * log mixedSourceWeightBase +
        oddAnatomySlope * log mixedOddWeightBase) +
      (mixedSourceWeightBase⁻¹ + mixedOddWeightBase⁻¹ +
        (mixedSourceWeightBase * mixedOddWeightBase)⁻¹ - 3) +
      ((mixedSourceWeightBase * mixedOddWeightBase)⁻¹ - 1) := by
  unfold mixedCanonicalCrossExponent
  ring

end

end Erdos327.Analytic
