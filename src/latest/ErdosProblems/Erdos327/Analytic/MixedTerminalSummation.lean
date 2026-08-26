import ErdosProblems.Erdos327.Analytic.MixedMainSummation
import ErdosProblems.Erdos327.Analytic.DyadicTerminalArithmetic
import ErdosProblems.Erdos327.Analytic.PowerConvolution

/-!
# Terminal summation for the mixed canonical estimate

This module treats the good Euler-main blocks in the terminal range
`Y = N / X² < X`.  The dyadic and residual logarithmic powers remain
separate there.  Both powers belong to `(-1, 0)`, while their sum is
strictly less than `-1`; the residual-index map therefore gives a
uniformly decaying finite convolution.
-/

namespace Erdos327.Analytic

open Filter Finset Real Topology

open scoped BigOperators

noncomputable section

/-- Good Euler-main contribution restricted to the terminal range
`N / X² < X`. -/
def mixedCanonicalTerminalMainContribution
    (L N : ℕ) (Kb Ko : ℝ) (j : ℕ) : ℝ :=
  if 32 * sieveRadius j ≤ j ∧
      L ≤ 16 * dyadicScale j ∧
      mixedScheduledGoodIndex L N j ∧
      N / (dyadicScale j * dyadicScale j) < dyadicScale j then
    mixedBlockPrefactor L (dyadicScale j)
        sourceAnatomySlope Kb oddAnatomySlope Ko
        mixedSourceWeightBase mixedOddWeightBase *
      mixedScheduledMertensMain L
        mixedSourceWeightBase mixedOddWeightBase j *
      mixedBlockResidualBound L N (dyadicScale j)
        mixedSourceWeightBase mixedOddWeightBase
  else 0

theorem mixedCanonicalTerminalMainContribution_nonneg
    {L N j : ℕ} {Kb Ko : ℝ} (hL : 3 ≤ L) :
    0 ≤ mixedCanonicalTerminalMainContribution L N Kb Ko j := by
  unfold mixedCanonicalTerminalMainContribution
  split_ifs with hj
  · exact mul_nonneg
      (mul_nonneg
        (mixedBlockPrefactor_nonneg hL
          (by
            simpa [dyadicScale] using
              Nat.one_le_pow j 2 (by norm_num))
          mixedSourceWeightBase_gt_one mixedOddWeightBase_gt_one)
        (by
          unfold mixedScheduledMertensMain
          positivity))
      (mixedBlockResidualBound_nonneg_of_good hL hj.2.2.1)
  · norm_num

/-- Constant converting the terminal dyadic logarithmic power into the
corresponding power of `j+1`. -/
def mixedTerminalDyadicIndexConstant : ℝ :=
  (2 / log (2 : ℝ)) ^ (-mixedCanonicalDyadicExponent)

theorem mixedTerminalDyadicIndexConstant_pos :
    0 < mixedTerminalDyadicIndexConstant := by
  unfold mixedTerminalDyadicIndexConstant
  positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem log_dyadicScale_rpow_terminal_le_index
    {j : ℕ} (hj : 1 ≤ j) :
    log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent ≤
      mixedTerminalDyadicIndexConstant *
        (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) := by
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogX : 0 < log (dyadicScale j : ℝ) := by
    rw [log_dyadicScale]
    positivity
  have hH : (1 : ℝ) ≤ 2 / log (2 : ℝ) := by
    apply (le_div_iff₀ hlog2).2
    linarith [Real.log_two_lt_d9]
  have hratio :
      (((j + 1 : ℕ) : ℝ)) / log (dyadicScale j : ℝ) ≤
        2 / log (2 : ℝ) := by
    rw [div_le_div_iff₀ hlogX hlog2, log_dyadicScale]
    push_cast
    have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hraw :=
    rpow_neg_le_ratio_rpow
      (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))
      hlogX hH
      (by
        linarith [mixedCanonicalDyadicExponent_lt_zero] :
          0 ≤ -mixedCanonicalDyadicExponent)
      hratio
  unfold mixedTerminalDyadicIndexConstant
  simpa using hraw

/-- Constant converting the logarithm of an exact residual quotient into
the power of its positive dyadic residual index. -/
def mixedTerminalResidualIndexConstant : ℝ :=
  (1 / 2 : ℝ) ^ mixedCanonicalResidualExponent *
    log (2 : ℝ) ^ mixedCanonicalResidualExponent

theorem mixedTerminalResidualIndexConstant_pos :
    0 < mixedTerminalResidualIndexConstant := by
  unfold mixedTerminalResidualIndexConstant
  exact mul_pos
    (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)) _)

theorem log_residual_rpow_le_residualIndex
    {Q j : ℕ}
    (hY : 2 ≤ Q / dyadicScale j ^ 2) :
    log (Q / dyadicScale j ^ 2 : ℕ) ^
          mixedCanonicalResidualExponent ≤
      mixedTerminalResidualIndexConstant *
        (((dyadicResidualIndex Q j + 1 : ℕ) : ℝ) ^
          mixedCanonicalResidualExponent) := by
  let k : ℕ := dyadicResidualIndex Q j
  have hk : 1 ≤ k := by
    dsimp [k]
    exact dyadicResidualIndex_pos hY
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hreslog :
      (k : ℝ) * log 2 ≤ log (Q / dyadicScale j ^ 2 : ℕ) := by
    simpa [k] using residualIndex_mul_log_two_le_log_residual hY
  have hanti :
      log (Q / dyadicScale j ^ 2 : ℕ) ^
          mixedCanonicalResidualExponent ≤
        ((k : ℝ) * log 2) ^ mixedCanonicalResidualExponent :=
    Real.rpow_le_rpow_of_nonpos
      (mul_pos hkpos hlog2) hreslog
      mixedCanonicalResidualExponent_lt_zero.le
  have hkhalf :
      (((k + 1 : ℕ) : ℝ) / 2) ≤ (k : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact_mod_cast (show k + 1 ≤ k * 2 by omega)
  have hkpow :
      (k : ℝ) ^ mixedCanonicalResidualExponent ≤
        (((k + 1 : ℕ) : ℝ) / 2) ^
          mixedCanonicalResidualExponent :=
    Real.rpow_le_rpow_of_nonpos
      (by positivity) hkhalf mixedCanonicalResidualExponent_lt_zero.le
  calc
    log (Q / dyadicScale j ^ 2 : ℕ) ^
          mixedCanonicalResidualExponent
        ≤ ((k : ℝ) * log 2) ^
            mixedCanonicalResidualExponent := hanti
    _ =
        log 2 ^ mixedCanonicalResidualExponent *
          (k : ℝ) ^ mixedCanonicalResidualExponent := by
      rw [Real.mul_rpow hkpos.le hlog2.le]
      ring
    _ ≤
        log 2 ^ mixedCanonicalResidualExponent *
          ((((k + 1 : ℕ) : ℝ) / 2) ^
            mixedCanonicalResidualExponent) :=
      mul_le_mul_of_nonneg_left hkpow
        (Real.rpow_nonneg hlog2.le _)
    _ =
        mixedTerminalResidualIndexConstant *
          (((k + 1 : ℕ) : ℝ) ^
            mixedCanonicalResidualExponent) := by
      unfold mixedTerminalResidualIndexConstant
      rw [show (((k + 1 : ℕ) : ℝ) / 2) =
          (1 / 2 : ℝ) * (((k + 1 : ℕ) : ℝ)) by ring,
        Real.mul_rpow (by norm_num) (by positivity)]
      ring

/-- Complete fixed constant in the terminal dyadic-residual profile. -/
def mixedCanonicalTerminalProfileConstant : ℝ :=
  mixedTerminalDyadicIndexConstant *
    mixedTerminalResidualIndexConstant *
    mixedScheduleLogConstant

theorem mixedCanonicalTerminalProfileConstant_pos :
    0 < mixedCanonicalTerminalProfileConstant := by
  unfold mixedCanonicalTerminalProfileConstant
  positivity [mixedTerminalDyadicIndexConstant_pos,
    mixedTerminalResidualIndexConstant_pos,
    mixedScheduleLogConstant_pos]

/-- Pointwise terminal estimate in terms of the two exact dyadic endpoint
indices. -/
theorem mixedCanonicalTerminalMainContribution_le_profile
    {L N j : ℕ} {Kb Ko : ℝ} (hL : 3 ≤ L) :
    mixedCanonicalTerminalMainContribution L N Kb Ko j ≤
      mixedCanonicalMainConstant Kb *
        mixedOddWeightBase ^ Ko * (N : ℝ) *
        log (L : ℝ) ^ mixedCanonicalOuterExponent *
        mixedCanonicalTerminalProfileConstant *
        ((((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
          (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
            mixedCanonicalResidualExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
  unfold mixedCanonicalTerminalMainContribution
  split_ifs with hj
  · rcases hj with ⟨hdom, hnear, hgood, hterminal⟩
    have hbase :=
      mixedCanonicalGoodMainBlock_le_convolution
        (Kb := Kb) (Ko := Ko) hL hdom hnear hgood
    have hj1 : 1 ≤ j := by
      have hz := hgood.1
      by_contra hj0
      have : j = 0 := Nat.eq_zero_of_not_pos hj0
      subst j
      simp [sieveCutoff, sieveCutoffExponent, sieveRadius,
        sieveHeight] at hz
    have hY2 :
        2 ≤ N / dyadicScale j ^ 2 := by
      have := hgood.2.2.2
      simpa [pow_two] using (show
        2 ≤ N / (dyadicScale j * dyadicScale j) by omega)
    have hY2mul :
        2 ≤ N / (dyadicScale j * dyadicScale j) := by
      simpa [pow_two] using hY2
    have hmin :
        min (dyadicScale j)
            (N / (dyadicScale j * dyadicScale j)) =
          N / (dyadicScale j * dyadicScale j) :=
      min_eq_right hterminal.le
    have hdyadic := log_dyadicScale_rpow_terminal_le_index hj1
    have hresidual :=
      log_residual_rpow_le_residualIndex
        (Q := N) (j := j) hY2
    have hloss := scheduledLogLoss_sq_le_log_four hj1
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
    rw [hmin] at hbase
    have hresidual' :
        log (N / (dyadicScale j * dyadicScale j) : ℕ) ^
              mixedCanonicalResidualExponent ≤
          mixedTerminalResidualIndexConstant *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) := by
      simpa [pow_two] using hresidual
    have hprofile :
        log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent *
            log (N / (dyadicScale j * dyadicScale j) : ℕ) ^
              mixedCanonicalResidualExponent *
            scheduledLogLoss j ^ (2 : ℝ) ≤
          mixedCanonicalTerminalProfileConstant *
            ((((j + 1 : ℕ) : ℝ) ^
                mixedCanonicalDyadicExponent) *
              (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
                mixedCanonicalResidualExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
      calc
        _ ≤
            (mixedTerminalDyadicIndexConstant *
                (((j + 1 : ℕ) : ℝ) ^
                  mixedCanonicalDyadicExponent)) *
              (mixedTerminalResidualIndexConstant *
                (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
                  mixedCanonicalResidualExponent)) *
              (mixedScheduleLogConstant *
                log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
          have hlogY :
              0 < log
                  (N / (dyadicScale j * dyadicScale j) : ℕ) :=
            log_pos (by
              exact_mod_cast
                (show 1 < N /
                    (dyadicScale j * dyadicScale j) by
                  exact lt_of_lt_of_le (by norm_num) hY2mul))
          have hAB :=
            mul_le_mul hdyadic hresidual'
              (Real.rpow_nonneg hlogY.le _)
              (mul_nonneg
                mixedTerminalDyadicIndexConstant_pos.le
                (Real.rpow_nonneg (by positivity) _))
          exact mul_le_mul hAB hloss
            (Real.rpow_nonneg
              (zero_le_one.trans (scheduledLogLoss_one_le j)) _)
            (mul_nonneg
              (mul_nonneg
                mixedTerminalDyadicIndexConstant_pos.le
                (Real.rpow_nonneg (by positivity) _))
              (mul_nonneg
                mixedTerminalResidualIndexConstant_pos.le
                (Real.rpow_nonneg (by positivity) _)))
      _ = _ := by
        unfold mixedCanonicalTerminalProfileConstant
        ring
    exact hbase.trans
      (by
        calc
          _ =
              (mixedCanonicalMainConstant Kb *
                  mixedOddWeightBase ^ Ko * (N : ℝ) *
                  log (L : ℝ) ^ mixedCanonicalOuterExponent) *
                (log (dyadicScale j : ℝ) ^
                    mixedCanonicalDyadicExponent *
                  log (N /
                    (dyadicScale j * dyadicScale j) : ℕ) ^
                      mixedCanonicalResidualExponent *
                  scheduledLogLoss j ^ (2 : ℝ)) := by ring
          _ ≤
              (mixedCanonicalMainConstant Kb *
                  mixedOddWeightBase ^ Ko * (N : ℝ) *
                  log (L : ℝ) ^ mixedCanonicalOuterExponent) *
                (mixedCanonicalTerminalProfileConstant *
                  ((((j + 1 : ℕ) : ℝ) ^
                      mixedCanonicalDyadicExponent) *
                    (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
                      mixedCanonicalResidualExponent) *
                    log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ))) :=
            mul_le_mul_of_nonneg_left hprofile hcoef0
          _ = _ := by ring)
  · have hcoef0 :
        0 ≤ mixedCanonicalMainConstant Kb *
            mixedOddWeightBase ^ Ko * (N : ℝ) *
            log (L : ℝ) ^ mixedCanonicalOuterExponent *
            mixedCanonicalTerminalProfileConstant := by
      have hlogL :
          0 < log (L : ℝ) :=
        log_pos (by exact_mod_cast (show 1 < L by omega))
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (mixedCanonicalMainConstant_pos Kb).le
              (Real.rpow_nonneg
                (by linarith [mixedOddWeightBase_gt_one]) _))
            (Nat.cast_nonneg N))
          (Real.rpow_nonneg hlogL.le _))
        mixedCanonicalTerminalProfileConstant_pos.le
    exact mul_nonneg hcoef0
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (Real.log_natCast_nonneg _) _))

/-! ## Finite terminal convolution -/

/-- A small positive power absorbing the four logarithms in the
terminal schedule profile. -/
def mixedTerminalLogAbsorption : ℝ :=
  -(mixedCanonicalCrossExponent + 1) / 2

theorem mixedTerminalLogAbsorption_pos :
    0 < mixedTerminalLogAbsorption := by
  unfold mixedTerminalLogAbsorption
  linarith [mixedCanonicalCrossExponent_lt_neg_one]

/-- Dyadic exponent after absorbing the scheduled logarithms. -/
def mixedTerminalAbsorbedDyadicExponent : ℝ :=
  mixedCanonicalDyadicExponent + mixedTerminalLogAbsorption

theorem mixedTerminalAbsorbedDyadicExponent_gt_neg_one :
    -1 < mixedTerminalAbsorbedDyadicExponent := by
  unfold mixedTerminalAbsorbedDyadicExponent
  linarith [mixedCanonicalDyadicExponent_gt_neg_one,
    mixedTerminalLogAbsorption_pos]

theorem mixedTerminalAbsorbedDyadicExponent_lt_zero :
    mixedTerminalAbsorbedDyadicExponent < 0 := by
  have hresOne :
      0 < mixedCanonicalResidualExponent + 1 := by
    linarith [mixedCanonicalResidualExponent_gt_neg_one]
  have hdyadic0 := mixedCanonicalDyadicExponent_lt_zero
  have hsum :
      mixedCanonicalDyadicExponent +
          mixedCanonicalResidualExponent =
        mixedCanonicalCrossExponent :=
    mixedCanonicalDyadic_add_residualExponent
  unfold mixedTerminalAbsorbedDyadicExponent
    mixedTerminalLogAbsorption
  rw [← hsum]
  linarith

theorem mixedTerminalAbsorbedConvolutionExponent_lt_zero :
    mixedTerminalAbsorbedDyadicExponent +
        mixedCanonicalResidualExponent + 1 < 0 := by
  unfold mixedTerminalAbsorbedDyadicExponent
    mixedTerminalLogAbsorption
  have hsum := mixedCanonicalDyadic_add_residualExponent
  linarith [mixedCanonicalCrossExponent_lt_neg_one]

/-- The active terminal index set at a finite dyadic endpoint. -/
def mixedCanonicalTerminalIndexSet
    (L N M : ℕ) : Finset ℕ :=
  (range M).filter (fun j ↦
    32 * sieveRadius j ≤ j ∧
      L ≤ 16 * dyadicScale j ∧
      mixedScheduledGoodIndex L N j ∧
      N / (dyadicScale j * dyadicScale j) < dyadicScale j)

/-- Past a fixed index, the four schedule logarithms are absorbed into
the strict terminal convolution margin. -/
theorem eventually_mixedTerminalProfile_absorbed :
    ∀ᶠ j : ℕ in atTop,
      (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) ≤
        (((j + 1 : ℕ) : ℝ) ^
          mixedTerminalAbsorbedDyadicExponent) := by
  filter_upwards
    [eventually_log_add_one_rpow_le_rpow
      (4 : ℝ) mixedTerminalLogAbsorption_pos] with j hj
  have hx : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  calc
    (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)
        ≤
      (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
        (((j + 1 : ℕ) : ℝ) ^ mixedTerminalLogAbsorption) :=
      mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg hx.le _)
    _ =
      (((j + 1 : ℕ) : ℝ) ^
        mixedTerminalAbsorbedDyadicExponent) := by
      rw [← Real.rpow_add hx]
      rfl

/-- Explicit constant in the terminal finite-convolution bound. -/
def mixedTerminalConvolutionConstant : ℝ :=
  (1 / 3 : ℝ) ^ mixedTerminalAbsorbedDyadicExponent *
    partialRpowConstant mixedCanonicalResidualExponent

theorem mixedTerminalConvolutionConstant_pos :
    0 < mixedTerminalConvolutionConstant := by
  unfold mixedTerminalConvolutionConstant
  exact mul_pos
    (Real.rpow_pos_of_pos (by norm_num) _)
    (partialRpowConstant_pos
      mixedCanonicalResidualExponent_gt_neg_one)

/-- Uniform finite sum of the absorbed terminal dyadic-residual
profile. -/
theorem sum_mixedTerminalIndexSet_profile_le
    {L N M H : ℕ}
    (hL : 3 ≤ L)
    (hstart : H ≤ mixedBulkMovingStart L)
    (habsorb : ∀ j ≥ H,
      (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) ≤
        (((j + 1 : ℕ) : ℝ) ^
          mixedTerminalAbsorbedDyadicExponent)) :
    (∑ j ∈ mixedCanonicalTerminalIndexSet L N M,
        (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
          (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
            mixedCanonicalResidualExponent) *
          log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) ≤
      mixedTerminalConvolutionConstant *
        (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
          (mixedTerminalAbsorbedDyadicExponent +
            mixedCanonicalResidualExponent + 1)) := by
  let s : Finset ℕ := mixedCanonicalTerminalIndexSet L N M
  let n : ℕ := Nat.log 2 N
  have hsResidual :
      ∀ j ∈ s, 2 * j ≤ Nat.log 2 N := by
    intro j hj
    have hj' := (mem_filter.mp hj).2
    have hY2 :
        2 ≤ N / dyadicScale j ^ 2 := by
      have hLY := hj'.2.2.1.2.2.2
      simpa [pow_two] using
        (show 2 ≤ N / (dyadicScale j * dyadicScale j) by omega)
    exact (two_mul_index_lt_log_of_two_le_residual hY2).le
  have hqsum :=
    sum_dyadicResidualIndex_rpow_le
      hsResidual mixedCanonicalResidualExponent_gt_neg_one
      mixedCanonicalResidualExponent_lt_zero.le
  have hpoint :
      ∀ j ∈ s,
        (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) ≤
          (1 / 3 : ℝ) ^ mixedTerminalAbsorbedDyadicExponent *
            (((n + 1 : ℕ) : ℝ) ^
              mixedTerminalAbsorbedDyadicExponent) *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) := by
    intro j hj
    have hj' := (mem_filter.mp hj).2
    rcases hj' with ⟨_hdom, hnear, hgood, hterminal⟩
    have hJ : H ≤ j :=
      hstart.trans (mixedBulkMovingStart_le_of_near hnear)
    have habs := habsorb j hJ
    have hYpos :
        1 ≤ N / dyadicScale j ^ 2 := by
      have hLY := hgood.2.2.2
      simpa [pow_two] using
        (show 1 ≤ N / (dyadicScale j * dyadicScale j) by omega)
    have hnlt :
        n < 3 * j := by
      dsimp [n]
      exact log_lt_three_mul_index_of_residual_lt_scale
        hYpos (by simpa [pow_two] using hterminal)
    have hthird :
        (((n + 1 : ℕ) : ℝ) / 3) ≤
          ((j + 1 : ℕ) : ℝ) := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).2
      exact_mod_cast (show n + 1 ≤ (j + 1) * 3 by omega)
    have hjpow :
        (((j + 1 : ℕ) : ℝ) ^
            mixedTerminalAbsorbedDyadicExponent) ≤
          (1 / 3 : ℝ) ^ mixedTerminalAbsorbedDyadicExponent *
            (((n + 1 : ℕ) : ℝ) ^
              mixedTerminalAbsorbedDyadicExponent) := by
      calc
        _ ≤
            ((((n + 1 : ℕ) : ℝ) / 3) ^
              mixedTerminalAbsorbedDyadicExponent) :=
          Real.rpow_le_rpow_of_nonpos
            (by positivity) hthird
            mixedTerminalAbsorbedDyadicExponent_lt_zero.le
        _ = _ := by
          rw [show (((n + 1 : ℕ) : ℝ) / 3) =
              (1 / 3 : ℝ) * (((n + 1 : ℕ) : ℝ)) by ring,
            Real.mul_rpow (by norm_num) (by positivity)]
    have hk0 :
        0 ≤ (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
          mixedCanonicalResidualExponent) :=
      Real.rpow_nonneg (by positivity) _
    calc
      _ =
          ((((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) := by ring
      _ ≤
          (((j + 1 : ℕ) : ℝ) ^
              mixedTerminalAbsorbedDyadicExponent) *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) :=
        mul_le_mul_of_nonneg_right habs hk0
      _ ≤ _ := mul_le_mul_of_nonneg_right hjpow hk0
  have hsumPoint :
      (∑ j ∈ s,
          (((j + 1 : ℕ) : ℝ) ^ mixedCanonicalDyadicExponent) *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) ≤
        ((1 / 3 : ℝ) ^ mixedTerminalAbsorbedDyadicExponent *
          (((n + 1 : ℕ) : ℝ) ^
            mixedTerminalAbsorbedDyadicExponent)) *
          (∑ j ∈ s,
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent)) := by
    calc
      _ ≤ ∑ j ∈ s,
          (1 / 3 : ℝ) ^ mixedTerminalAbsorbedDyadicExponent *
            (((n + 1 : ℕ) : ℝ) ^
              mixedTerminalAbsorbedDyadicExponent) *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) := by
        apply sum_le_sum
        intro j hj
        exact hpoint j hj
      _ = _ := by rw [mul_sum]
  have hfront0 :
      0 ≤ (1 / 3 : ℝ) ^ mixedTerminalAbsorbedDyadicExponent *
        (((n + 1 : ℕ) : ℝ) ^
          mixedTerminalAbsorbedDyadicExponent) := by positivity
  calc
    _ ≤
        ((1 / 3 : ℝ) ^ mixedTerminalAbsorbedDyadicExponent *
          (((n + 1 : ℕ) : ℝ) ^
            mixedTerminalAbsorbedDyadicExponent)) *
          (∑ j ∈ s,
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent)) := hsumPoint
    _ ≤
        ((1 / 3 : ℝ) ^ mixedTerminalAbsorbedDyadicExponent *
          (((n + 1 : ℕ) : ℝ) ^
            mixedTerminalAbsorbedDyadicExponent)) *
          (partialRpowConstant mixedCanonicalResidualExponent *
            (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
              (mixedCanonicalResidualExponent + 1))) :=
      mul_le_mul_of_nonneg_left hqsum hfront0
    _ =
      mixedTerminalConvolutionConstant *
        (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
          (mixedTerminalAbsorbedDyadicExponent +
            mixedCanonicalResidualExponent + 1)) := by
      dsimp [n]
      unfold mixedTerminalConvolutionConstant
      have hx : (0 : ℝ) < ((Nat.log 2 N + 1 : ℕ) : ℝ) := by
        positivity
      have hpow :
          (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
              mixedTerminalAbsorbedDyadicExponent) *
            (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
              (mixedCanonicalResidualExponent + 1)) =
            (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
              (mixedTerminalAbsorbedDyadicExponent +
                (mixedCanonicalResidualExponent + 1))) := by
        rw [← Real.rpow_add hx]
      calc
        _ =
            ((1 / 3 : ℝ) ^
                mixedTerminalAbsorbedDyadicExponent *
              partialRpowConstant mixedCanonicalResidualExponent) *
              ((((Nat.log 2 N + 1 : ℕ) : ℝ) ^
                  mixedTerminalAbsorbedDyadicExponent) *
                (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
                  (mixedCanonicalResidualExponent + 1))) := by ring
        _ = _ := by rw [hpow]; ring_nf

/-- The binary logarithmic index, cast to the reals and shifted by one,
tends to infinity. -/
theorem tendsto_natLogTwo_add_one_atTop :
    Tendsto (fun N : ℕ ↦
      ((Nat.log 2 N + 1 : ℕ) : ℝ)) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨m : ℕ, hm : b ≤ m⟩ := exists_nat_ge b
  filter_upwards [eventually_ge_atTop (2 ^ m)] with N hN
  have hlog :
      m ≤ Nat.log 2 N := by
    have :=
      Nat.log_mono_right (b := 2) hN
    simpa [Nat.log_pow (by norm_num : 1 < 2)] using this
  exact hm.trans (by
    exact_mod_cast (show m ≤ Nat.log 2 N + 1 by omega))

theorem tendsto_mixedTerminalConvolutionPower_zero :
    Tendsto
      (fun N : ℕ ↦
        (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
          (mixedTerminalAbsorbedDyadicExponent +
            mixedCanonicalResidualExponent + 1)))
      atTop (𝓝 0) := by
  let a : ℝ :=
    -(mixedTerminalAbsorbedDyadicExponent +
      mixedCanonicalResidualExponent + 1)
  have ha : 0 < a := by
    dsimp [a]
    linarith [mixedTerminalAbsorbedConvolutionExponent_lt_zero]
  have h :=
    (tendsto_rpow_neg_atTop ha).comp
      tendsto_natLogTwo_add_one_atTop
  change Tendsto
    (fun N : ℕ ↦
      (((Nat.log 2 N + 1 : ℕ) : ℝ) ^ (-a)))
    atTop (𝓝 0) at h
  simpa [a] using h

/-- Final rough-density allocation for every good terminal Euler-main
block.  The roughness cutoff is selected first; the ambient cutoff may
then be taken sufficiently large, uniformly in the finite dyadic
endpoint. -/
theorem eventually_sum_mixedCanonicalTerminalMain_le_roughDensity
    (Kb : ℝ) :
    ∀ᶠ L : ℕ in atTop, ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
      (∑ j ∈ range M,
        mixedCanonicalTerminalMainContribution
          L N Kb (oddBudget L) j) ≤
        (N : ℝ) * Erdos327.roughDensity L / 64 := by
  rcases eventually_atTop.1
      eventually_mixedTerminalProfile_absorbed with ⟨H, hH⟩
  filter_upwards
    [eventually_ge_atTop 3,
      eventually_fixed_le_mixedBulkMovingStart H] with L hL hstart
  let D : ℝ :=
    mixedCanonicalMainConstant Kb *
      mixedOddWeightBase ^ oddBudget L *
      log (L : ℝ) ^ mixedCanonicalOuterExponent *
      mixedCanonicalTerminalProfileConstant *
      mixedTerminalConvolutionConstant
  have hpower := tendsto_mixedTerminalConvolutionPower_zero
  have hscaled :
      Tendsto
        (fun N : ℕ ↦
          D * (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
            (mixedTerminalAbsorbedDyadicExponent +
              mixedCanonicalResidualExponent + 1)))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpower)
  have htarget :
      0 < Erdos327.roughDensity L / 64 := by
    exact div_pos (Erdos327.roughDensity_pos hL) (by norm_num)
  filter_upwards
    [(tendsto_order.1 hscaled).2
      (Erdos327.roughDensity L / 64) htarget] with N hN
  intro M
  let C : ℝ :=
    mixedCanonicalMainConstant Kb *
      mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
      log (L : ℝ) ^ mixedCanonicalOuterExponent *
      mixedCanonicalTerminalProfileConstant
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have hlogL :
        0 < log (L : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < L by omega))
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mixedCanonicalMainConstant_pos Kb).le
            (Real.rpow_nonneg
              (by linarith [mixedOddWeightBase_gt_one]) _))
          (Nat.cast_nonneg N))
        (Real.rpow_nonneg hlogL.le _))
      mixedCanonicalTerminalProfileConstant_pos.le
  have hsumEq :
      (∑ j ∈ range M,
          mixedCanonicalTerminalMainContribution
            L N Kb (oddBudget L) j) =
        ∑ j ∈ mixedCanonicalTerminalIndexSet L N M,
          mixedCanonicalTerminalMainContribution
            L N Kb (oddBudget L) j := by
    unfold mixedCanonicalTerminalIndexSet
      mixedCanonicalTerminalMainContribution
    rw [sum_filter]
    apply sum_congr rfl
    intro j hj
    by_cases hp :
        32 * sieveRadius j ≤ j ∧
          L ≤ 16 * dyadicScale j ∧
          mixedScheduledGoodIndex L N j ∧
          N / (dyadicScale j * dyadicScale j) < dyadicScale j
    · rw [if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp]
  have hpoint :
      ∀ j : ℕ,
        mixedCanonicalTerminalMainContribution
            L N Kb (oddBudget L) j ≤
          C *
            ((((j + 1 : ℕ) : ℝ) ^
                mixedCanonicalDyadicExponent) *
              (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
                mixedCanonicalResidualExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
    intro j
    simpa [C, mul_assoc] using
      (mixedCanonicalTerminalMainContribution_le_profile
        (L := L) (N := N) (j := j)
        (Kb := Kb) (Ko := oddBudget L) hL)
  have hprofile :=
    sum_mixedTerminalIndexSet_profile_le
      (L := L) (N := N) (M := M) hL hstart hH
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  calc
    (∑ j ∈ range M,
        mixedCanonicalTerminalMainContribution
          L N Kb (oddBudget L) j) =
      ∑ j ∈ mixedCanonicalTerminalIndexSet L N M,
        mixedCanonicalTerminalMainContribution
          L N Kb (oddBudget L) j := hsumEq
    _ ≤
      ∑ j ∈ mixedCanonicalTerminalIndexSet L N M,
        C *
          ((((j + 1 : ℕ) : ℝ) ^
              mixedCanonicalDyadicExponent) *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
      apply sum_le_sum
      intro j hj
      exact hpoint j
    _ =
      C *
        (∑ j ∈ mixedCanonicalTerminalIndexSet L N M,
          (((j + 1 : ℕ) : ℝ) ^
              mixedCanonicalDyadicExponent) *
            (((dyadicResidualIndex N j + 1 : ℕ) : ℝ) ^
              mixedCanonicalResidualExponent) *
            log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by
      rw [mul_sum]
    _ ≤
      C * (mixedTerminalConvolutionConstant *
        (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
          (mixedTerminalAbsorbedDyadicExponent +
            mixedCanonicalResidualExponent + 1))) :=
      mul_le_mul_of_nonneg_left hprofile hC0
    _ =
      (N : ℝ) *
        (D * (((Nat.log 2 N + 1 : ℕ) : ℝ) ^
          (mixedTerminalAbsorbedDyadicExponent +
            mixedCanonicalResidualExponent + 1))) := by
      dsimp [C, D]
      ring
    _ ≤
      (N : ℝ) * (Erdos327.roughDensity L / 64) :=
      mul_le_mul_of_nonneg_left hN.le hN0
    _ = (N : ℝ) * Erdos327.roughDensity L / 64 := by
      ring

/-! ## Exact isolation of the remaining boundary ranges -/

/-- The only non-good ranges left after the schedule dominates: either
the roughness cutoff lies in the short transition above `X`, or it lies
above the exact residual quotient `Y`. -/
theorem mixedScheduled_not_good_boundary
    {L N j : ℕ}
    (hdom : 32 * sieveRadius j ≤ j)
    (hnotgood : ¬mixedScheduledGoodIndex L N j) :
    dyadicScale j < L ∨
      N / (dyadicScale j * dyadicScale j) < L := by
  have hz : 2 ≤ sieveCutoff j :=
    two_le_sieveCutoff_of_dominance hdom
  have hX : 2 ≤ dyadicScale j :=
    hz.trans (sieveCutoff_le_dyadicScale j)
  by_contra hboundary
  push_neg at hboundary
  apply hnotgood
  exact ⟨hz, hboundary.1,
    sieveCutoff_le_dyadicScale j, hboundary.2⟩

/-- Literal refined contribution on precisely the two boundary ranges
not covered by the good Euler-main estimates. -/
def mixedCanonicalBoundaryBlock
    (L N : ℕ) (Kb Ko : ℝ) (j : ℕ) : ℝ :=
  if L ≤ 16 * dyadicScale j ∧
      (dyadicScale j < L ∨
        N / (dyadicScale j * dyadicScale j) < L) then
    mixedRefinedScheduledBlockBound
      L N sourceAnatomySlope Kb oddAnatomySlope Ko
        mixedSourceWeightBase mixedOddWeightBase j
  else 0

/-- Eventually the unresolved block is exactly the sum of the terminal
good Euler-main term and the literal transition/fallback boundary term.
This is an equality, uniform in `L`, `N`, and the intercepts. -/
theorem exists_mixedCanonicalUnresolved_eq_terminal_add_boundary :
    ∃ J : ℕ, ∀ L N j : ℕ, J ≤ j → ∀ Kb Ko : ℝ,
      mixedCanonicalUnresolvedBlock L N Kb Ko j =
        mixedCanonicalTerminalMainContribution L N Kb Ko j +
          mixedCanonicalBoundaryBlock L N Kb Ko j := by
  have hschedule :
      ∀ᶠ j : ℕ in atTop,
        mixedCanonicalScheduleErrorsHold j := by
    filter_upwards
      [eventually_scheduledFactorialTail_le_inv_add_one_pow_eight,
        eventually_scheduledPolynomialBoundary_le] with j ht hp
    exact ⟨ht, hp⟩
  have hall :
      ∀ᶠ j : ℕ in atTop,
        mixedCanonicalScheduleErrorsHold j ∧
          32 * sieveRadius j ≤ j := hschedule.and
            eventually_sieveSchedule_dominates
  rcases eventually_atTop.1 hall with ⟨J, hJ⟩
  refine ⟨J, ?_⟩
  intro L N j hj Kb Ko
  rcases hJ j hj with ⟨herrors, hdom⟩
  by_cases hnear : L ≤ 16 * dyadicScale j
  · by_cases hgood : mixedScheduledGoodIndex L N j
    · by_cases hterminal :
          N / (dyadicScale j * dyadicScale j) < dyadicScale j
      · have hnotbulk :
            ¬dyadicScale j ≤
              N / (dyadicScale j * dyadicScale j) := by omega
        have hnoboundary :
            ¬(L ≤ 16 * dyadicScale j ∧
              (dyadicScale j < L ∨
                N / (dyadicScale j * dyadicScale j) < L)) := by
          intro hb
          rcases hb.2 with hbX | hbY
          · exact (Nat.not_lt_of_ge hgood.2.1) hbX
          · exact (Nat.not_lt_of_ge hgood.2.2.2) hbY
        unfold mixedCanonicalUnresolvedBlock
          mixedCanonicalTerminalMainContribution
          mixedCanonicalBoundaryBlock
        rw [if_pos ⟨herrors, hdom, hnear, hgood⟩,
          if_neg hnotbulk,
          if_pos ⟨hdom, hnear, hgood, hterminal⟩,
          if_neg hnoboundary]
        simp
      · have hbulk :
            dyadicScale j ≤
              N / (dyadicScale j * dyadicScale j) := by omega
        have hnoboundary :
            ¬(L ≤ 16 * dyadicScale j ∧
              (dyadicScale j < L ∨
                N / (dyadicScale j * dyadicScale j) < L)) := by
          intro hb
          rcases hb.2 with hbX | hbY
          · exact (Nat.not_lt_of_ge hgood.2.1) hbX
          · exact (Nat.not_lt_of_ge hgood.2.2.2) hbY
        unfold mixedCanonicalUnresolvedBlock
          mixedCanonicalTerminalMainContribution
          mixedCanonicalBoundaryBlock
        rw [if_pos ⟨herrors, hdom, hnear, hgood⟩,
          if_pos hbulk,
          if_neg (by
            intro ht
            exact hterminal ht.2.2.2),
          if_neg hnoboundary]
        simp
    · have hboundary :=
        mixedScheduled_not_good_boundary hdom hgood
      unfold mixedCanonicalUnresolvedBlock
        mixedCanonicalTerminalMainContribution
        mixedCanonicalBoundaryBlock
      rw [if_neg (by
          intro h
          exact hgood h.2.2.2),
        if_neg (by
          intro h
          exact hgood h.2.2.1),
        if_pos ⟨hnear, hboundary⟩]
      simp
  · have hempty : 16 * dyadicScale j < L := by omega
    unfold mixedCanonicalUnresolvedBlock
      mixedCanonicalTerminalMainContribution
      mixedCanonicalBoundaryBlock
    rw [if_neg (by
        intro h
        exact hnear h.2.2.1),
      if_neg (by
        intro h
        exact hnear h.2.1),
      if_neg (by
        intro h
        exact hnear h.1),
      mixedRefinedScheduledBlockBound, if_pos hempty]
    simp

/-- Finite-tail form of the exact terminal/boundary decomposition. -/
theorem exists_sum_mixedCanonicalUnresolved_eq_terminal_add_boundary :
    ∃ J : ℕ, ∀ J' ≥ J, ∀ L N M : ℕ, ∀ Kb Ko : ℝ,
      (∑ j ∈ Ico J' M,
        mixedCanonicalUnresolvedBlock L N Kb Ko j) =
        (∑ j ∈ Ico J' M,
          mixedCanonicalTerminalMainContribution L N Kb Ko j) +
        ∑ j ∈ Ico J' M,
          mixedCanonicalBoundaryBlock L N Kb Ko j := by
  rcases exists_mixedCanonicalUnresolved_eq_terminal_add_boundary with
    ⟨J, hJ⟩
  refine ⟨J, ?_⟩
  intro J' hJJ L N M Kb Ko
  calc
    _ = ∑ j ∈ Ico J' M,
        (mixedCanonicalTerminalMainContribution L N Kb Ko j +
          mixedCanonicalBoundaryBlock L N Kb Ko j) := by
      apply sum_congr rfl
      intro j hj
      exact hJ L N j (hJJ.trans (mem_Ico.mp hj).1) Kb Ko
    _ = _ := by rw [sum_add_distrib]

end

end Erdos327.Analytic
