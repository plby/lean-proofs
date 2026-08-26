import ErdosProblems.Erdos327.Analytic.SourceSmallBlocks
import ErdosProblems.Erdos327.Analytic.SieveScheduleErrors
import ErdosProblems.Erdos327.Analytic.ScheduledProductBounds
import ErdosProblems.Erdos327.Analytic.ResidualEnvelopePowers
import ErdosProblems.Erdos327.Analytic.ScheduledInitialVanishing
import ErdosProblems.Erdos327.Analytic.TailInstantiation
import ErdosProblems.Erdos327.Parameters

/-!
# Quantitative summation of the scheduled source blocks

This file sharpens the global source majorant by retaining the exact
residual moment on every nonempty block.  It then isolates the Euler main
term from the factorial-tail and polynomial-boundary errors and proves the
scheduled error estimates needed for the final summation.
-/

namespace Erdos327.Analytic

open Finset Filter Real

noncomputable section

/-- A sharper global summand than `sourceRefinedScheduledBlockBound`:
all nonempty blocks retain the exact residual moment. -/
def sourceExactRefinedScheduledBlockBound
    (L N : ℕ) (A K : ℝ) (j : ℕ) : ℝ :=
  if 8 * dyadicScale j < L then 0
  else sourceScheduledFallbackBlockBound L N A K j

/-- Every exact-residual block in a fixed prefix vanishes once the
largest reference scale in that prefix lies below `L/8`. -/
theorem sourceExactRefinedScheduledBlockBound_eq_zero_of_le
    {L N i j : ℕ} {A K : ℝ}
    (hij : i ≤ j) (hfar : 8 * dyadicScale j < L) :
    sourceExactRefinedScheduledBlockBound L N A K i = 0 := by
  rw [sourceExactRefinedScheduledBlockBound, if_pos]
  exact
    (Nat.mul_le_mul_left 8 (dyadicScale_mono hij)).trans_lt hfar

/-- Exact disappearance of a fixed prefix of the sharper source
majorant. -/
theorem sum_sourceExactRefinedScheduledBlockBound_range_eq_zero
    {L N J : ℕ} {A K : ℝ}
    (hfar : 8 * dyadicScale J < L) :
    (∑ j ∈ range J,
      sourceExactRefinedScheduledBlockBound L N A K j) = 0 := by
  apply sum_eq_zero
  intro j hj
  exact sourceExactRefinedScheduledBlockBound_eq_zero_of_le
    (Nat.le_of_lt (mem_range.mp hj)) hfar

/-- Pointwise validity of the exact-residual refined summand. -/
theorem card_sourceDyadic_le_exactRefinedScheduledBlock
    {L N j : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hA : 0 ≤ A) :
    ((sourceDyadicCoordinateSet
      L N A K (dyadicScale j)).card : ℝ) ≤
      sourceExactRefinedScheduledBlockBound L N A K j := by
  by_cases hfar : 8 * dyadicScale j < L
  · rw [sourceExactRefinedScheduledBlockBound, if_pos hfar,
      sourceDyadicCoordinateSet_eq_empty_of_eight_mul_lt hfar]
    simp
  · rw [sourceExactRefinedScheduledBlockBound, if_neg hfar]
    exact card_sourceDyadic_le_scheduledFallback hL hA

/-- The exact-residual scheduled sum bounds the full source coordinate
set. -/
theorem card_sourceCoordinateSet_le_exactRefinedScheduled_sum
    {L N : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hA : 0 ≤ A) :
    ((sourceCoordinateSet L N A K).card : ℝ) ≤
      ∑ j ∈ range (Nat.log 2 N + 1),
        sourceExactRefinedScheduledBlockBound L N A K j := by
  refine (card_sourceCoordinateSet_le_sum_dyadic L N A K).trans ?_
  apply sum_le_sum
  intro j hj
  simpa [dyadicScale] using
    (card_sourceDyadic_le_exactRefinedScheduledBlock
      (L := L) (N := N) (j := j) (A := A) (K := K) hL hA)

/-- Canonical bad-source count bounded by the sharper exact-residual sum. -/
theorem card_rankBad_le_exactRefinedScheduled_sum
    {L N : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N) (hA : 0 ≤ A) :
    ((Erdos327.rankBad (Erdos327.upto N)
      (regularSource L A K N)
      ArithmeticFunction.cardFactors).card : ℝ) ≤
      ∑ j ∈ range (Nat.log 2 N + 1),
        sourceExactRefinedScheduledBlockBound L N A K j := by
  have hcoordinate :
      ((Erdos327.rankBad (Erdos327.upto N)
        (regularSource L A K N)
        ArithmeticFunction.cardFactors).card : ℝ) ≤
        ((sourceCoordinateSet L N A K).card : ℝ) := by
    exact_mod_cast card_rankBad_le_sourceCoordinateSet hL hN
  exact hcoordinate.trans
    (card_sourceCoordinateSet_le_exactRefinedScheduled_sum hL hA)

/-- The exact residual moment is at most the length of its interval. -/
theorem sourceDyadicResidualMoment_le
    (L X Y : ℕ) :
    sourceDyadicResidualMoment L X Y ≤ (Y : ℝ) := by
  unfold sourceDyadicResidualMoment
  calc
    (∑ d ∈ Icc 1 Y,
        if OddRough L d then
          (1 / 4 : ℝ) ^ primeFactorCountBetween L X d
        else 0) ≤
      ∑ _d ∈ Icc 1 Y, (1 : ℝ) := by
        apply sum_le_sum
        intro d hd
        split_ifs
        · exact pow_le_one₀ (by norm_num) (by norm_num)
        · norm_num
    _ = (Y : ℝ) := by
      simp [Nat.card_Icc]

/-- The dyadic square times its residual cutoff is at most `2N`. -/
theorem dyadic_sq_mul_residualCutoff_le
    (N j : ℕ) :
    dyadicScale j ^ 2 *
        (2 * N / dyadicScale j ^ 2) ≤
      2 * N := by
  have hpos : 0 < dyadicScale j ^ 2 := by
    positivity [dyadicScale_pos j]
  simpa [Nat.mul_comm] using
    Nat.div_mul_le_self (2 * N) (dyadicScale j ^ 2)

/-- Euler-product main term of the scheduled source sieve. -/
def sourceScheduledEulerSieveMain (L j : ℕ) : ℝ :=
  8 * (dyadicScale j : ℝ) ^ 2 *
    exp (sourceAllCutoffMertensEnvelope L (sieveCutoff j))

/-- Exact-residual block contribution of the Euler-product main term. -/
def sourceScheduledEulerBlockMain
    (L N : ℕ) (A K : ℝ) (j : ℕ) : ℝ :=
  sourceDyadicBudget L (dyadicScale j) A K *
    sourceScheduledEulerSieveMain L j *
    sourceDyadicResidualMoment
      L (dyadicScale j) (2 * N / dyadicScale j ^ 2)

/-- Uniformly in the roughness cutoff, the full scheduled sieve factor is
eventually its Euler main term plus at most `9 X²/(j+1)^8`. -/
theorem eventually_forall_sourceScheduledSieve_le_main_add_error :
    ∀ᶠ j : ℕ in atTop,
      ∀ L : ℕ,
      sourceAllCutoffSharpSieveBound
          L (sieveCutoff j) (dyadicScale j) (sieveRadius j) ≤
        sourceScheduledEulerSieveMain L j +
          9 * (dyadicScale j : ℝ) ^ 2 /
            (((j + 1 : ℕ) : ℝ) ^ 8) := by
  filter_upwards
    [eventually_scheduledFactorialTail_le_inv_add_one_pow_eight,
      eventually_scheduledPolynomialBoundary_le] with j htail hboundary
  intro L
  have htailScaled :
      8 * (dyadicScale j : ℝ) ^ 2 *
          scheduledFactorialTail j ≤
        8 * (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) := by
    calc
      8 * (dyadicScale j : ℝ) ^ 2 *
            scheduledFactorialTail j ≤
          8 * (dyadicScale j : ℝ) ^ 2 *
            (1 / (((j + 1 : ℕ) : ℝ) ^ 8)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring
  have htailScaled' :
      8 * (dyadicScale j : ℝ) ^ 2 *
          ((3 * primeInvSum (sieveCutoff j)) ^
              (2 * sieveRadius j + 1) /
            ((2 * sieveRadius j + 1).factorial : ℝ)) ≤
        8 * (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) := by
    change
      8 * (dyadicScale j : ℝ) ^ 2 *
          ((3 * primeInvSum (sieveCutoff j)) ^
              (2 * sieveRadius j + 1) /
            ((2 * sieveRadius j + 1).factorial : ℝ)) ≤
        8 * (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) at htailScaled
    exact htailScaled
  have hboundary' :
      ((2 * sieveRadius j + 1 : ℕ) : ℝ) *
          (sieveCutoff j : ℝ) ^ (2 * sieveRadius j) *
          (3 : ℝ) ^ (2 * sieveRadius j) *
          (9 * (dyadicScale j : ℝ) +
            (sieveCutoff j : ℝ) ^ (2 * sieveRadius j)) ≤
        (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) := by
    change
      ((2 * sieveRadius j + 1 : ℕ) : ℝ) *
          (sieveCutoff j : ℝ) ^ (2 * sieveRadius j) *
          (3 : ℝ) ^ (2 * sieveRadius j) *
          (9 * (dyadicScale j : ℝ) +
            (sieveCutoff j : ℝ) ^ (2 * sieveRadius j)) ≤
        (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) at hboundary
    exact hboundary
  unfold sourceAllCutoffSharpSieveBound
    sourceScheduledEulerSieveMain
  calc
    8 * (dyadicScale j : ℝ) ^ 2 *
          exp (sourceAllCutoffMertensEnvelope L (sieveCutoff j)) +
        8 * (dyadicScale j : ℝ) ^ 2 *
          ((3 * primeInvSum (sieveCutoff j)) ^
              (2 * sieveRadius j + 1) /
            ((2 * sieveRadius j + 1).factorial : ℝ)) +
        ((2 * sieveRadius j + 1 : ℕ) : ℝ) *
          (sieveCutoff j : ℝ) ^ (2 * sieveRadius j) *
          (3 : ℝ) ^ (2 * sieveRadius j) *
          (9 * (dyadicScale j : ℝ) +
            (sieveCutoff j : ℝ) ^ (2 * sieveRadius j))
        ≤
      8 * (dyadicScale j : ℝ) ^ 2 *
          exp (sourceAllCutoffMertensEnvelope L (sieveCutoff j)) +
        (8 * (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8)) +
        (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) :=
      add_le_add (add_le_add le_rfl htailScaled') hboundary'
    _ = 8 * (dyadicScale j : ℝ) ^ 2 *
          exp (sourceAllCutoffMertensEnvelope L (sieveCutoff j)) +
        9 * (dyadicScale j : ℝ) ^ 2 /
          (((j + 1 : ℕ) : ℝ) ^ 8) := by ring

/-- Fixed-cutoff projection of the uniform scheduled sieve estimate. -/
theorem eventually_sourceScheduledSieve_le_main_add_error
    (L : ℕ) :
    ∀ᶠ j : ℕ in atTop,
      sourceAllCutoffSharpSieveBound
          L (sieveCutoff j) (dyadicScale j) (sieveRadius j) ≤
        sourceScheduledEulerSieveMain L j +
          9 * (dyadicScale j : ℝ) ^ 2 /
            (((j + 1 : ℕ) : ℝ) ^ 8) := by
  filter_upwards
    [eventually_forall_sourceScheduledSieve_le_main_add_error] with j hj
  exact hj L

/-- Constant part of the source regularity budget. -/
def sourceBudgetConstant (K : ℝ) : ℝ :=
  exp (log 4 * (K + 2))

/-- The actual polynomial exponent in the canonical source regularity
budget.  Keeping this exponent, rather than rounding it up to two, is
needed when it is combined with the `-7/4` source Euler-product power. -/
def sourceCanonicalBudgetExponent : ℝ :=
  sourceAnatomySlope * log 4

/-- The canonical budget exponent is strictly below `3/2`. -/
theorem sourceCanonicalBudgetExponent_lt_three_halves :
    sourceCanonicalBudgetExponent < 3 / 2 := by
  simpa [sourceCanonicalBudgetExponent, sourceAnatomySlope] using
    Erdos327.source_exponent_lt_three_halves

/-- On a potentially nonempty block, retain the exact real power of the
dyadic index in the source regularity budget. -/
theorem sourceScheduledBudget_le_rpow
    {L j : ℕ} {K : ℝ}
    (hL : 3 ≤ L) (hnear : L ≤ 8 * dyadicScale j) :
    sourceDyadicBudget L (dyadicScale j)
        sourceAnatomySlope K ≤
      sourceBudgetConstant K *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) := by
  have hlogL :
      0 < log (L : ℝ) :=
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
  have hratioPos :
      0 < log (8 * (dyadicScale j : ℝ)) / log L := by
    apply div_pos _ hlogL
    rw [hlogScale]
    positivity
  have hratioUpper :
      log (8 * (dyadicScale j : ℝ)) / log L ≤
        ((j + 3 : ℕ) : ℝ) := by
    rw [hlogScale]
    apply (div_le_iff₀ hlogL).2
    have hlogTwoL :
        log (2 : ℝ) ≤ log (L : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (by norm_num)
        (by
          simpa only [Set.mem_Ioi] using
            (show (0 : ℝ) < L by positivity))
        (by exact_mod_cast (show 2 ≤ L by omega))
    exact mul_le_mul_of_nonneg_left hlogTwoL (by positivity)
  have hjPos : (0 : ℝ) < (j + 3 : ℕ) := by positivity
  have hlogRatioUpper :
      log (log (8 * (dyadicScale j : ℝ)) / log L) ≤
        log (((j + 3 : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn hratioPos hjPos hratioUpper
  have hcoef :
      0 ≤ sourceCanonicalBudgetExponent := by
    unfold sourceCanonicalBudgetExponent
    positivity [sourceAnatomySlope_nonneg]
  unfold sourceDyadicBudget sourceBudgetConstant
  have hexponent :
      log 4 *
          (sourceAnatomySlope *
              log
                (log (8 * (dyadicScale j : ℝ)) / log L) +
            K + 2) ≤
        log 4 * (K + 2) +
          sourceCanonicalBudgetExponent *
            log (((j + 3 : ℕ) : ℝ)) := by
    unfold sourceCanonicalBudgetExponent at hcoef ⊢
    nlinarith [log_pos (show (1 : ℝ) < 4 by norm_num)]
  calc
    exp (log 4 *
          (sourceAnatomySlope *
              log
                (log (8 * (dyadicScale j : ℝ)) / log L) +
            K + 2)) ≤
        exp (log 4 * (K + 2) +
          sourceCanonicalBudgetExponent *
            log (((j + 3 : ℕ) : ℝ))) :=
      exp_le_exp.mpr hexponent
    _ = exp (log 4 * (K + 2)) *
          (((j + 3 : ℕ) : ℝ) ^
            sourceCanonicalBudgetExponent) := by
      rw [exp_add, Real.rpow_def_of_pos hjPos]
      ring_nf

/-- On every potentially nonempty scheduled block, the source regularity
budget grows at most quadratically in the dyadic index. -/
theorem sourceScheduledBudget_le_quadratic
    {L j : ℕ} {K : ℝ}
    (hL : 3 ≤ L) (hnear : L ≤ 8 * dyadicScale j) :
    sourceDyadicBudget L (dyadicScale j)
        sourceAnatomySlope K ≤
      sourceBudgetConstant K * (((j + 3 : ℕ) : ℝ) ^ 2) := by
  have hlogL :
      0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogTwo :
      0 < log (2 : ℝ) :=
    log_pos (by norm_num)
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
  have hlogTwoL :
      log (2 : ℝ) ≤ log (L : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by norm_num)
      (by
        simpa only [Set.mem_Ioi] using
          (show (0 : ℝ) < L by positivity))
      (by exact_mod_cast (show 2 ≤ L by omega))
  have hratioPos :
      0 < log (8 * (dyadicScale j : ℝ)) / log L := by
    apply div_pos _ hlogL
    rw [hlogScale]
    positivity
  have hratioOne :
      1 ≤ log (8 * (dyadicScale j : ℝ)) / log L := by
    apply (le_div_iff₀ hlogL).2
    have hnearReal :
        (L : ℝ) ≤ 8 * (dyadicScale j : ℝ) := by
      exact_mod_cast hnear
    simpa using
      (Real.strictMonoOn_log.monotoneOn
        (by
          simpa only [Set.mem_Ioi] using
            (show (0 : ℝ) < L by positivity))
        (by
          have hscalePos :
              (0 : ℝ) < (dyadicScale j : ℝ) := by
            exact_mod_cast dyadicScale_pos j
          simpa only [Set.mem_Ioi] using
            (mul_pos (by norm_num : (0 : ℝ) < 8) hscalePos))
        hnearReal)
  have hratioUpper :
      log (8 * (dyadicScale j : ℝ)) / log L ≤
        ((j + 3 : ℕ) : ℝ) := by
    rw [hlogScale]
    apply (div_le_iff₀ hlogL).2
    exact mul_le_mul_of_nonneg_left hlogTwoL (by positivity)
  have hjPos : (0 : ℝ) < (j + 3 : ℕ) := by positivity
  have hlogRatio0 :
      0 ≤ log
        (log (8 * (dyadicScale j : ℝ)) / log L) :=
    log_nonneg hratioOne
  have hlogRatioUpper :
      log (log (8 * (dyadicScale j : ℝ)) / log L) ≤
        log (((j + 3 : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn hratioPos hjPos hratioUpper
  have hM0 :
      0 ≤ sourceAnatomySlope * log 4 :=
    mul_nonneg sourceAnatomySlope_nonneg
      (log_pos (by norm_num)).le
  have hM2 :
      sourceAnatomySlope * log 4 ≤ 2 := by
    unfold sourceAnatomySlope
    linarith [Erdos327.source_exponent_lt_three_halves]
  unfold sourceDyadicBudget sourceBudgetConstant
  have hexponent :
      log 4 *
          (sourceAnatomySlope *
              log
                (log (8 * (dyadicScale j : ℝ)) / log L) +
            K + 2) ≤
        log 4 * (K + 2) +
          2 * log (((j + 3 : ℕ) : ℝ)) := by
    nlinarith
  calc
    exp (log 4 *
          (sourceAnatomySlope *
              log
                (log (8 * (dyadicScale j : ℝ)) / log L) +
            K + 2)) ≤
        exp (log 4 * (K + 2) +
          2 * log (((j + 3 : ℕ) : ℝ))) :=
      exp_le_exp.mpr hexponent
    _ = exp (log 4 * (K + 2)) *
          (((j + 3 : ℕ) : ℝ) ^ 2) := by
      rw [exp_add]
      congr 1
      rw [show
        2 * log (((j + 3 : ℕ) : ℝ)) =
          log ((((j + 3 : ℕ) : ℝ) ^ 2)) by
            rw [Real.log_pow]
            norm_num,
        exp_log (by positivity)]

/-- Scheduled source Euler main term with both cutoff orderings absorbed
into one explicit logarithmic-power envelope. -/
theorem sourceScheduledEulerSieveMain_le_product
    {L j : ℕ} (hL : 3 ≤ L)
    (hdom : 32 * sieveRadius j ≤ j)
    (hnear : L ≤ 8 * dyadicScale j) :
    sourceScheduledEulerSieveMain L j ≤
      8 * (dyadicScale j : ℝ) ^ 2 *
        (sourceScheduledProductConstant *
          log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
          log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ)) := by
  unfold sourceScheduledEulerSieveMain
  exact mul_le_mul_of_nonneg_left
    (exp_sourceAllCutoffMertensEnvelope_le_scheduled
      hL hdom hnear) (by positivity)

/-- Pointwise canonical Euler block bound retaining the exact residual
moment and the true source budget exponent. -/
theorem sourceScheduledEulerBlockMain_le_product
    {L N j : ℕ} {K : ℝ}
    (hL : 3 ≤ L)
    (hdom : 32 * sieveRadius j ≤ j)
    (hnear : L ≤ 8 * dyadicScale j) :
    sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j ≤
      (sourceBudgetConstant K *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
      (8 * (dyadicScale j : ℝ) ^ 2 *
        (sourceScheduledProductConstant *
          log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
          log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
          scheduledLogLoss j ^ (5 / 2 : ℝ))) *
      sourceDyadicResidualMoment
        L (dyadicScale j) (2 * N / dyadicScale j ^ 2) := by
  have hbudget :=
    sourceScheduledBudget_le_rpow (K := K) hL hnear
  have hsieve :=
    sourceScheduledEulerSieveMain_le_product hL hdom hnear
  have hresidual0 :
      0 ≤ sourceDyadicResidualMoment
        L (dyadicScale j) (2 * N / dyadicScale j ^ 2) := by
    unfold sourceDyadicResidualMoment
    positivity
  have hsieve0 :
      0 ≤ sourceScheduledEulerSieveMain L j := by
    unfold sourceScheduledEulerSieveMain
    positivity
  have hbudgetRhs0 :
      0 ≤ sourceBudgetConstant K *
        (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) := by
    unfold sourceBudgetConstant
    positivity
  unfold sourceScheduledEulerBlockMain
  exact
    (mul_le_mul_of_nonneg_right
      (mul_le_mul hbudget hsieve
        hsieve0
        hbudgetRhs0)
      hresidual0)

/-- The canonical exact source residual moment in its normalized
logarithmic-power form. -/
theorem sourceDyadicResidualMoment_le_normalized
    {L X Y : ℕ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hLY : L ≤ Y)
    (hY : 2 ≤ Y) :
    sourceDyadicResidualMoment L X Y ≤
      residualMomentConstant (1 / 4 : ℝ) *
        ((Y : ℝ) / log L) *
        (log ((min X Y : ℕ) : ℝ) / log (L : ℝ)) ^
          (-(3 / 4 : ℝ)) := by
  have h :=
    residualMoment_le_normalized_rpow
      hL hLX hLY hY
      (q := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  unfold sourceDyadicResidualMoment
  convert h using 1 <;> norm_num

/-- Fully normalized envelope for a source Euler block in the main
residual regime `L ≤ min(X,Y)`. -/
def sourceScheduledNormalizedBlockMain
    (L N : ℕ) (K : ℝ) (j : ℕ) : ℝ :=
  let X : ℕ := dyadicScale j
  let Y : ℕ := 2 * N / X ^ 2
  (sourceBudgetConstant K *
      (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
    (8 * (X : ℝ) ^ 2 *
      (sourceScheduledProductConstant *
        log (X : ℝ) ^ (-(7 / 4 : ℝ)) *
        log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
        scheduledLogLoss j ^ (5 / 2 : ℝ))) *
    (residualMomentConstant (1 / 4 : ℝ) *
      ((Y : ℝ) / log L) *
      (log ((min X Y : ℕ) : ℝ) / log (L : ℝ)) ^
        (-(3 / 4 : ℝ)))

/-- The canonical Euler block is bounded by the fully normalized product
envelope whenever both the dyadic and residual scales exceed `L`. -/
theorem sourceScheduledEulerBlockMain_le_normalized
    {L N j : ℕ} {K : ℝ}
    (hL : 3 ≤ L)
    (hdom : 32 * sieveRadius j ≤ j)
    (hLX : L ≤ dyadicScale j)
    (hLY : L ≤ 2 * N / dyadicScale j ^ 2)
    (hY : 2 ≤ 2 * N / dyadicScale j ^ 2) :
    sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j ≤
      sourceScheduledNormalizedBlockMain L N K j := by
  have hnear : L ≤ 8 * dyadicScale j := by
    have hXpos := dyadicScale_pos j
    omega
  have hbase :=
    sourceScheduledEulerBlockMain_le_product
      (N := N) (K := K) hL hdom hnear
  have hresidual :=
    sourceDyadicResidualMoment_le_normalized
      hL hLX hLY hY
  have hprefactor0 :
      0 ≤
        (sourceBudgetConstant K *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent)) *
        (8 * (dyadicScale j : ℝ) ^ 2 *
          (sourceScheduledProductConstant *
            log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
            log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
            scheduledLogLoss j ^ (5 / 2 : ℝ))) := by
    have hlogX :
        0 < log (dyadicScale j : ℝ) :=
      log_pos (by
        exact_mod_cast
          (show 1 < dyadicScale j by
            exact lt_of_lt_of_le (by omega : 1 < L) hLX))
    have hlogL :
        0 < log (L : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < L by omega))
    have hbudget0 :
        0 ≤ sourceBudgetConstant K *
          (((j + 3 : ℕ) : ℝ) ^ sourceCanonicalBudgetExponent) := by
      unfold sourceBudgetConstant
      exact mul_nonneg (exp_pos _).le
        (Real.rpow_nonneg (by positivity) _)
    have hproduct0 :
        0 ≤
          8 * (dyadicScale j : ℝ) ^ 2 *
            (sourceScheduledProductConstant *
              log (dyadicScale j : ℝ) ^ (-(7 / 4 : ℝ)) *
              log (L : ℝ) ^ (-(3 / 4 : ℝ)) *
              scheduledLogLoss j ^ (5 / 2 : ℝ)) := by
      exact mul_nonneg (by positivity)
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg sourceScheduledProductConstant_pos.le
              (Real.rpow_nonneg hlogX.le _))
            (Real.rpow_nonneg hlogL.le _))
          (Real.rpow_nonneg
            (zero_le_one.trans (scheduledLogLoss_one_le j)) _))
    exact mul_nonneg hbudget0 hproduct0
  exact hbase.trans
    (by
      unfold sourceScheduledNormalizedBlockMain
      dsimp only
      exact mul_le_mul_of_nonneg_left hresidual hprefactor0)

/-- Explicit summable majorant for the two scheduled sieve errors after
multiplying by the exact residual moment. -/
def sourceScheduledErrorBlockBound
    (N : ℕ) (K : ℝ) (j : ℕ) : ℝ :=
  18 * (N : ℝ) * sourceBudgetConstant K *
    (((j + 3 : ℕ) : ℝ) ^ 2) /
    (((j + 1 : ℕ) : ℝ) ^ 8)

/-- After a single schedule threshold independent of `L`, `K`, and `N`,
every exact scheduled block is bounded by its Euler main term plus the
explicit summable error majorant. -/
theorem eventually_forall_sourceExactRefinedBlock_le_main_add_error :
    ∀ᶠ j : ℕ in atTop,
      ∀ L : ℕ, ∀ K : ℝ, 3 ≤ L → ∀ N : ℕ,
        sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j ≤
          sourceScheduledEulerBlockMain
            L N sourceAnatomySlope K j +
          sourceScheduledErrorBlockBound N K j := by
  filter_upwards
    [eventually_forall_sourceScheduledSieve_le_main_add_error,
      eventually_sieveSchedule_dominates] with j hsieve hdom
  intro L K hL N
  specialize hsieve L
  have hz : 2 ≤ sieveCutoff j :=
    two_le_sieveCutoff_of_dominance hdom
  have hclamp :
      sourceClampedSieveCutoff j = sieveCutoff j :=
    sourceClampedSieveCutoff_eq hz
  by_cases hfar : 8 * dyadicScale j < L
  · rw [sourceExactRefinedScheduledBlockBound, if_pos hfar]
    have hmain0 :
        0 ≤ sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j := by
      unfold sourceScheduledEulerBlockMain
        sourceScheduledEulerSieveMain sourceDyadicBudget
        sourceDyadicResidualMoment
      positivity
    have herror0 :
        0 ≤ sourceScheduledErrorBlockBound N K j := by
      unfold sourceScheduledErrorBlockBound sourceBudgetConstant
      positivity
    linarith
  · have hnear : L ≤ 8 * dyadicScale j :=
      Nat.le_of_not_gt hfar
    have hbudget :=
      sourceScheduledBudget_le_quadratic
        (K := K) hL hnear
    have hresidual :=
      sourceDyadicResidualMoment_le
        L (dyadicScale j) (2 * N / dyadicScale j ^ 2)
    have hresidual0 :
        0 ≤ sourceDyadicResidualMoment
          L (dyadicScale j) (2 * N / dyadicScale j ^ 2) := by
      unfold sourceDyadicResidualMoment
      positivity
    have hsqResidualNat :=
      dyadic_sq_mul_residualCutoff_le N j
    have hsqResidual :
        (dyadicScale j : ℝ) ^ 2 *
            sourceDyadicResidualMoment
              L (dyadicScale j)
                (2 * N / dyadicScale j ^ 2) ≤
          2 * (N : ℝ) := by
      calc
        (dyadicScale j : ℝ) ^ 2 *
              sourceDyadicResidualMoment
                L (dyadicScale j)
                  (2 * N / dyadicScale j ^ 2) ≤
            (dyadicScale j : ℝ) ^ 2 *
              (2 * N / dyadicScale j ^ 2 : ℕ) :=
          mul_le_mul_of_nonneg_left hresidual (by positivity)
        _ ≤ 2 * (N : ℝ) := by
          exact_mod_cast hsqResidualNat
    have hdenom :
        0 ≤ 9 / (((j + 1 : ℕ) : ℝ) ^ 8) := by positivity
    have hcombined :
        sourceDyadicBudget L (dyadicScale j)
              sourceAnatomySlope K *
            ((dyadicScale j : ℝ) ^ 2 *
              sourceDyadicResidualMoment
                L (dyadicScale j)
                  (2 * N / dyadicScale j ^ 2)) ≤
          (sourceBudgetConstant K *
              (((j + 3 : ℕ) : ℝ) ^ 2)) *
            (2 * (N : ℝ)) := by
      exact mul_le_mul hbudget hsqResidual
        (mul_nonneg (by positivity) hresidual0)
        (by
          unfold sourceBudgetConstant
          positivity)
    have herror :
        sourceDyadicBudget L (dyadicScale j)
              sourceAnatomySlope K *
            (9 * (dyadicScale j : ℝ) ^ 2 /
              (((j + 1 : ℕ) : ℝ) ^ 8)) *
            sourceDyadicResidualMoment
              L (dyadicScale j)
                (2 * N / dyadicScale j ^ 2) ≤
          sourceScheduledErrorBlockBound N K j := by
      calc
        sourceDyadicBudget L (dyadicScale j)
              sourceAnatomySlope K *
            (9 * (dyadicScale j : ℝ) ^ 2 /
              (((j + 1 : ℕ) : ℝ) ^ 8)) *
            sourceDyadicResidualMoment
              L (dyadicScale j)
                (2 * N / dyadicScale j ^ 2) =
          (9 / (((j + 1 : ℕ) : ℝ) ^ 8)) *
            (sourceDyadicBudget L (dyadicScale j)
                sourceAnatomySlope K *
              ((dyadicScale j : ℝ) ^ 2 *
                sourceDyadicResidualMoment
                  L (dyadicScale j)
                    (2 * N / dyadicScale j ^ 2))) := by ring
        _ ≤ (9 / (((j + 1 : ℕ) : ℝ) ^ 8)) *
            ((sourceBudgetConstant K *
                (((j + 3 : ℕ) : ℝ) ^ 2)) *
              (2 * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hcombined hdenom
        _ = sourceScheduledErrorBlockBound N K j := by
          unfold sourceScheduledErrorBlockBound
          ring
    rw [sourceExactRefinedScheduledBlockBound, if_neg hfar,
      sourceScheduledFallbackBlockBound, hclamp]
    have hbudget0 :
        0 ≤ sourceDyadicBudget L (dyadicScale j)
          sourceAnatomySlope K := by
      unfold sourceDyadicBudget
      positivity
    have hscaled :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsieve hbudget0) hresidual0
    refine hscaled.trans ?_
    unfold sourceScheduledEulerBlockMain
    linarith

/-- Fixed-parameter projection of the uniform exact-block estimate. -/
theorem eventually_sourceExactRefinedBlock_le_main_add_error
    (L : ℕ) (K : ℝ) (hL : 3 ≤ L) :
    ∀ᶠ j : ℕ in atTop,
      ∀ N : ℕ,
        sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j ≤
          sourceScheduledEulerBlockMain
            L N sourceAnatomySlope K j +
          sourceScheduledErrorBlockBound N K j := by
  filter_upwards
    [eventually_forall_sourceExactRefinedBlock_le_main_add_error]
      with j hj
  exact hj L K hL

/-- The normalized scheduled error profile is summable. -/
theorem summable_sourceScheduledErrorProfile :
    Summable (fun j : ℕ ↦
      (((j + 3 : ℕ) : ℝ) ^ 2) /
        (((j + 1 : ℕ) : ℝ) ^ 8)) := by
  have hseries :
      Summable (fun j : ℕ ↦
        9 * (1 / |(j : ℝ) + 1| ^ (6 : ℝ))) :=
    ((Real.summable_one_div_nat_add_rpow 1 6).2
      (by norm_num)).mul_left 9
  apply hseries.of_nonneg_of_le
  · intro j
    positivity
  · intro j
    have hj1 : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    have hnum :
        (((j + 3 : ℕ) : ℝ) ^ 2) ≤
          9 * (((j + 1 : ℕ) : ℝ) ^ 2) := by
      have hlinear :
          ((j + 3 : ℕ) : ℝ) ≤ 3 * ((j + 1 : ℕ) : ℝ) := by
        push_cast
        nlinarith
      nlinarith [sq_nonneg
        (((j + 3 : ℕ) : ℝ) - 3 * ((j + 1 : ℕ) : ℝ))]
    have hdenPos :
        0 < (((j + 1 : ℕ) : ℝ) ^ 8) := pow_pos hj1 8
    calc
      (((j + 3 : ℕ) : ℝ) ^ 2) /
            (((j + 1 : ℕ) : ℝ) ^ 8) ≤
          (9 * (((j + 1 : ℕ) : ℝ) ^ 2)) /
            (((j + 1 : ℕ) : ℝ) ^ 8) :=
        div_le_div_of_nonneg_right hnum hdenPos.le
      _ = 9 * (1 / |(j : ℝ) + 1| ^ (6 : ℝ)) := by
        rw [abs_of_pos (by positivity : (0 : ℝ) < (j : ℝ) + 1)]
        norm_num [Real.rpow_natCast]
        field_simp

/-- For fixed `N,K`, the complete scheduled sieve-error sequence is
summable. -/
theorem summable_sourceScheduledErrorBlockBound
    (N : ℕ) (K : ℝ) :
    Summable (sourceScheduledErrorBlockBound N K) := by
  have h :=
    summable_sourceScheduledErrorProfile.mul_left
      (18 * (N : ℝ) * sourceBudgetConstant K)
  apply h.congr
  intro j
  unfold sourceScheduledErrorBlockBound
  ring

/-- Every sufficiently late finite segment of the normalized error profile
has arbitrarily small mass. -/
theorem exists_sourceScheduledErrorProfile_tail_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ J' ≥ J, ∀ M : ℕ,
      (∑ j ∈ Ico J' M,
        (((j + 3 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)) < ε := by
  let f : ℕ → ℝ := fun j ↦
    (((j + 3 : ℕ) : ℝ) ^ 2) /
      (((j + 1 : ℕ) : ℝ) ^ 8)
  have hf : Summable f := by
    exact summable_sourceScheduledErrorProfile
  have htail :
      ∀ᶠ J : ℕ in atTop, (∑' k : ℕ, f (k + J)) < ε :=
    (tendsto_order.1 (tendsto_sum_nat_add f)).2 ε hε
  rcases (eventually_atTop.1 htail) with ⟨J, hJ⟩
  refine ⟨J, fun J' hJJ M ↦ ?_⟩
  have hshift : Summable (fun k : ℕ ↦ f (k + J')) :=
    (summable_nat_add_iff J').2 hf
  have hfinite :
      (∑ k ∈ range (M - J'), f (k + J')) ≤
        ∑' k : ℕ, f (k + J') := by
    exact hshift.sum_le_tsum (range (M - J'))
      (fun k hk ↦ by
        dsimp [f]
        positivity)
  calc
    (∑ j ∈ Ico J' M,
        (((j + 3 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)) =
        ∑ k ∈ range (M - J'), f (k + J') := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply sum_congr rfl
      intro k hk
      dsimp [f]
      have hthree : J' + k + 3 = k + J' + 3 := by omega
      have hone : J' + k + 1 = k + J' + 1 := by omega
      rw [hthree, hone]
    _ ≤ ∑' k : ℕ, f (k + J') := hfinite
    _ < ε := hJ J' hJJ

/-- Uniformly in `N`, the late scheduled sieve errors consume an
arbitrarily small multiple of `N`. -/
theorem exists_sourceScheduledError_tail_le
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ J' ≥ J, ∀ N M : ℕ,
      (∑ j ∈ Ico J' M,
        sourceScheduledErrorBlockBound N K j) ≤
        ε * (N : ℝ) := by
  have hC :
      0 < 18 * sourceBudgetConstant K := by
    unfold sourceBudgetConstant
    positivity
  have hC0 : sourceBudgetConstant K ≠ 0 := by
    unfold sourceBudgetConstant
    exact (exp_pos _).ne'
  obtain ⟨J, hJ⟩ :=
    exists_sourceScheduledErrorProfile_tail_lt
      (ε := ε / (18 * sourceBudgetConstant K))
      (div_pos hε hC)
  refine ⟨J, fun J' hJJ N M ↦ ?_⟩
  have hprofile :
      (∑ j ∈ Ico J' M,
        (((j + 3 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)) ≤
        ε / (18 * sourceBudgetConstant K) :=
    (hJ J' hJJ M).le
  calc
    (∑ j ∈ Ico J' M,
        sourceScheduledErrorBlockBound N K j) =
      (18 * (N : ℝ) * sourceBudgetConstant K) *
        (∑ j ∈ Ico J' M,
          (((j + 3 : ℕ) : ℝ) ^ 2) /
            (((j + 1 : ℕ) : ℝ) ^ 8)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      unfold sourceScheduledErrorBlockBound
      ring
    _ ≤ (18 * (N : ℝ) * sourceBudgetConstant K) *
        (ε / (18 * sourceBudgetConstant K)) :=
      mul_le_mul_of_nonneg_left hprofile
        (mul_nonneg
          (mul_nonneg (by norm_num) (Nat.cast_nonneg N))
          (exp_pos _).le)
    _ = ε * (N : ℝ) := by
      field_simp [hC0]

/-- With a threshold independent of `L`, the complete exact-residual
scheduled sum is reduced to:

* finitely many initial blocks;
* the Euler-product main terms;
* an arbitrarily small multiple of `N`.
-/
theorem exists_forall_sourceExactScheduled_sum_le_initial_add_main_add_error
    (K : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ L : ℕ, 3 ≤ L → ∀ N M : ℕ, J ≤ M →
      (∑ j ∈ range M,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) ≤
        (∑ j ∈ range J,
          sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j) +
        (∑ j ∈ Ico J M,
          sourceScheduledEulerBlockMain
            L N sourceAnatomySlope K j) +
        ε * (N : ℝ) := by
  rcases (eventually_atTop.1
    eventually_forall_sourceExactRefinedBlock_le_main_add_error) with
      ⟨Js, hJs⟩
  obtain ⟨Je, hJe⟩ :=
    exists_sourceScheduledError_tail_le K hε
  let J := max Js Je
  refine ⟨J, fun L hL N M hJM ↦ ?_⟩
  have hlate :
      (∑ j ∈ Ico J M,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) ≤
        ∑ j ∈ Ico J M,
          (sourceScheduledEulerBlockMain
              L N sourceAnatomySlope K j +
            sourceScheduledErrorBlockBound N K j) := by
    apply sum_le_sum
    intro j hj
    exact hJs j
      (le_trans (le_max_left Js Je) (mem_Ico.mp hj).1)
      L K hL N
  have herror :
      (∑ j ∈ Ico J M,
        sourceScheduledErrorBlockBound N K j) ≤
        ε * (N : ℝ) :=
    hJe J (le_max_right Js Je) N M
  calc
    (∑ j ∈ range M,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) =
      (∑ j ∈ range J,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) +
      ∑ j ∈ Ico J M,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j :=
      (Finset.sum_range_add_sum_Ico
        (fun j ↦ sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) hJM).symm
    _ ≤
      (∑ j ∈ range J,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) +
      ∑ j ∈ Ico J M,
        (sourceScheduledEulerBlockMain
            L N sourceAnatomySlope K j +
          sourceScheduledErrorBlockBound N K j) :=
      add_le_add_right hlate _
    _ =
      (∑ j ∈ range J,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) +
      (∑ j ∈ Ico J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j) +
      ∑ j ∈ Ico J M,
        sourceScheduledErrorBlockBound N K j := by
      rw [sum_add_distrib]
      ring
    _ ≤
      (∑ j ∈ range J,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) +
      (∑ j ∈ Ico J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j) +
      ε * (N : ℝ) := by
      exact add_le_add_right herror _

/-- Fixed-cutoff projection of the uniform scheduled-sum reduction. -/
theorem exists_sourceExactScheduled_sum_le_initial_add_main_add_error
    (L : ℕ) (K : ℝ) (hL : 3 ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ N M : ℕ, J ≤ M →
      (∑ j ∈ range M,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) ≤
        (∑ j ∈ range J,
          sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j) +
        (∑ j ∈ Ico J M,
          sourceScheduledEulerBlockMain
            L N sourceAnatomySlope K j) +
        ε * (N : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_forall_sourceExactScheduled_sum_le_initial_add_main_add_error
      K hε
  exact ⟨J, hJ L hL⟩

/-- Uniform source-density reduction after choosing `L` large enough to
kill the schedule prefix.  Only the Euler main convolution remains,
besides an arbitrarily small `εN` error. -/
theorem exists_forall_card_rankBad_le_main_add_error
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ L : ℕ, 3 ≤ L →
      8 * dyadicScale J < L →
      ∀ N : ℕ, 2 ≤ N →
        J ≤ Nat.log 2 N + 1 →
        ((Erdos327.rankBad (Erdos327.upto N)
          (regularSource L sourceAnatomySlope K N)
          ArithmeticFunction.cardFactors).card : ℝ) ≤
          (∑ j ∈ Ico J (Nat.log 2 N + 1),
            sourceScheduledEulerBlockMain
              L N sourceAnatomySlope K j) +
          ε * (N : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_forall_sourceExactScheduled_sum_le_initial_add_main_add_error
      K hε
  refine ⟨J, fun L hL hfar N hN hJlog ↦ ?_⟩
  have hprefix :
      (∑ j ∈ range J,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) = 0 :=
    sum_sourceExactRefinedScheduledBlockBound_range_eq_zero hfar
  have hglobal :=
    card_rankBad_le_exactRefinedScheduled_sum
      (L := L) (N := N)
      (A := sourceAnatomySlope) (K := K)
      hL hN sourceAnatomySlope_nonneg
  exact hglobal.trans
    (by
      simpa [hprefix] using
        hJ L hL N (Nat.log 2 N + 1) hJlog)

/-- Corresponding quantitative reduction for the canonical bad-source
count. -/
theorem exists_card_rankBad_le_initial_add_main_add_error
    (L : ℕ) (K : ℝ) (hL : 3 ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ N : ℕ, 2 ≤ N →
      J ≤ Nat.log 2 N + 1 →
      ((Erdos327.rankBad (Erdos327.upto N)
        (regularSource L sourceAnatomySlope K N)
        ArithmeticFunction.cardFactors).card : ℝ) ≤
        (∑ j ∈ range J,
          sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j) +
        (∑ j ∈ Ico J (Nat.log 2 N + 1),
          sourceScheduledEulerBlockMain
            L N sourceAnatomySlope K j) +
        ε * (N : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_sourceExactScheduled_sum_le_initial_add_main_add_error
      L K hL hε
  refine ⟨J, fun N hN hJlog ↦ ?_⟩
  exact
    (card_rankBad_le_exactRefinedScheduled_sum
      (L := L) (N := N)
      (A := sourceAnatomySlope) (K := K)
      hL hN sourceAnatomySlope_nonneg).trans
        (hJ N (Nat.log 2 N + 1) hJlog)

end

end Erdos327.Analytic
