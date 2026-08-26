import ErdosProblems.Erdos327.Analytic.MixedTerminalSummation
import ErdosProblems.Erdos327.Analytic.ScheduledSupport

/-!
# Boundary summation for the mixed canonical estimate

The literal boundary block left by `MixedTerminalSummation` has two
parts.  The transition part satisfies `X < L ≤ 16X`, hence contains at
most four dyadic indices.  In the residual part the positive quotient
`N / X²` is less than `L`; those quotients are distinct and the
corresponding indices escape every fixed prefix as `N → ∞`.
-/

namespace Erdos327.Analytic

open Filter Finset Real Topology

open scoped BigOperators

noncomputable section

/-- Constant in the exact-length Euler-main boundary estimate. -/
def mixedBoundaryMainConstant (Kb Ko : ℝ) : ℝ :=
  8 * mixedCanonicalPrefactorConstant Kb Ko *
    mixedCanonicalScheduledProductConstant

theorem mixedBoundaryMainConstant_pos (Kb Ko : ℝ) :
    0 < mixedBoundaryMainConstant Kb Ko := by
  unfold mixedBoundaryMainConstant
  exact mul_pos
    (mul_pos (by norm_num)
      (mixedCanonicalPrefactorConstant_pos Kb Ko))
    mixedCanonicalScheduledProductConstant_pos

/-- Constant in the exact-length finite-sieve-error boundary estimate. -/
def mixedBoundaryErrorConstant (Kb Ko : ℝ) : ℝ :=
  9 * mixedCanonicalPrefactorConstant Kb Ko

theorem mixedBoundaryErrorConstant_pos (Kb Ko : ℝ) :
    0 < mixedBoundaryErrorConstant Kb Ko := by
  unfold mixedBoundaryErrorConstant
  exact mul_pos (by norm_num)
    (mixedCanonicalPrefactorConstant_pos Kb Ko)

/-- Every canonical refined scheduled block is nonnegative. -/
theorem mixedCanonicalRefinedScheduledBlockBound_nonneg
    {L N j : ℕ} {Kb Ko : ℝ} (hL : 3 ≤ L) :
    0 ≤ mixedRefinedScheduledBlockBound
      L N sourceAnatomySlope Kb oddAnatomySlope Ko
        mixedSourceWeightBase mixedOddWeightBase j := by
  have hcard :=
    card_mixedCoordinateBoxBlock_le_refinedScheduledBlock
      (L := L) (N := N) (j := j)
      (Ab := sourceAnatomySlope) (Kb := Kb)
      (Ao := oddAnatomySlope) (Ko := Ko)
      (qb := mixedSourceWeightBase) (qo := mixedOddWeightBase)
      hL mixedSourceWeightBase_gt_one mixedOddWeightBase_gt_one
      mixedRegularityExponent_nonneg
  exact (Nat.cast_nonneg
    ((mixedCoordinateBoxBlock L N sourceAnatomySlope Kb
      oddAnatomySlope Ko (dyadicScale j)).card)).trans hcard

/-- The canonical literal boundary block is nonnegative. -/
theorem mixedCanonicalBoundaryBlock_nonneg
    {L N j : ℕ} {Kb Ko : ℝ} (hL : 3 ≤ L) :
    0 ≤ mixedCanonicalBoundaryBlock L N Kb Ko j := by
  unfold mixedCanonicalBoundaryBlock
  split_ifs
  · exact mixedCanonicalRefinedScheduledBlockBound_nonneg hL
  · norm_num

/-- On an active boundary block the common residual envelope is its
exact interval length. -/
theorem mixedScheduledResidualEnvelope_eq_length_of_boundary
    {L N j : ℕ}
    (hboundary :
      dyadicScale j < L ∨
        N / (dyadicScale j * dyadicScale j) < L) :
    mixedScheduledResidualEnvelope L N
        mixedSourceWeightBase mixedOddWeightBase j =
      (N / (dyadicScale j * dyadicScale j) : ℕ) := by
  unfold mixedScheduledResidualEnvelope
  rw [if_neg]
  intro hgood
  rcases hboundary with hX | hY
  · exact (Nat.not_lt_of_ge hgood.2.1) hX
  · exact (Nat.not_lt_of_ge hgood.2.2.2) hY

/-- Pointwise exact-length bound for an active late boundary block.
The two terms are kept separate because the Euler main and finite-sieve
error have different dyadic profiles. -/
theorem mixedCanonicalBoundaryBlock_le_raw
    {L N j : ℕ} {Kb Ko : ℝ}
    (hL : 3 ≤ L) (hj : 1 ≤ j)
    (hdom : 32 * sieveRadius j ≤ j)
    (herrors : mixedCanonicalScheduleErrorsHold j) :
    mixedCanonicalBoundaryBlock L N Kb Ko j ≤
      mixedBoundaryMainConstant Kb Ko * (N : ℝ) *
          log (L : ℝ) ^
            (-mixedCanonicalRegularityExponent +
              mixedCanonicalRoughnessExponent) *
          log (dyadicScale j : ℝ) ^
            mixedCanonicalDyadicExponent *
          scheduledLogLoss j ^ (2 : ℝ) +
        mixedBoundaryErrorConstant Kb Ko * (N : ℝ) *
          log (L : ℝ) ^
            (-mixedCanonicalRegularityExponent) *
          ((((j + 1 : ℕ) : ℝ) ^ 2) /
            (((j + 1 : ℕ) : ℝ) ^ 8)) := by
  unfold mixedCanonicalBoundaryBlock
  split_ifs with hb
  · rcases hb with ⟨hnear, hboundary⟩
    have hX2 : 2 ≤ dyadicScale j := by
      simpa [dyadicScale] using
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hj
    have hpref :=
      mixedCanonicalBlockPrefactor_le_powers
        (Kb := Kb) (Ko := Ko) hL hX2
    have hmain :=
      mixedCanonicalScheduledMertensMain_le_powers
        hL hdom hnear
    have hbox :
        mixedAllCutoffSharpBoxBound L (sieveCutoff j)
            (dyadicScale j) (sieveRadius j)
            mixedSourceWeightBase mixedOddWeightBase ≤
          mixedScheduledMertensMain L
              mixedSourceWeightBase mixedOddWeightBase j +
            mixedScheduledSieveError j :=
      mixedAllCutoffSharpBoxBound_le_main_add_error
        herrors.1 herrors.2
    have henvelope :=
      mixedRefinedScheduledBlockBound_le_analyticEnvelope
        (L := L) (N := N) (j := j)
        (Ab := sourceAnatomySlope) (Kb := Kb)
        (Ao := oddAnatomySlope) (Ko := Ko)
        (qb := mixedSourceWeightBase) (qo := mixedOddWeightBase)
        hL mixedSourceWeightBase_gt_one mixedOddWeightBase_gt_one
        (two_le_sieveCutoff_of_dominance hdom)
        (mixedScheduledResidualAvailable_of_one_le_index hj)
        hbox
    rw [mixedScheduledResidualEnvelope_eq_length_of_boundary hboundary]
      at henvelope
    have hpref0 :
        0 ≤ mixedBlockPrefactor L (dyadicScale j)
          sourceAnatomySlope Kb oddAnatomySlope Ko
          mixedSourceWeightBase mixedOddWeightBase :=
      mixedBlockPrefactor_nonneg hL
        (by simpa [dyadicScale] using Nat.one_le_pow j 2 (by norm_num))
        mixedSourceWeightBase_gt_one mixedOddWeightBase_gt_one
    have hprefR0 :
        0 ≤ mixedCanonicalPrefactorConstant Kb Ko *
          log (dyadicScale j : ℝ) ^
            mixedCanonicalRegularityExponent *
          log (L : ℝ) ^
            (-mixedCanonicalRegularityExponent) := by
      exact mul_nonneg
        (mul_nonneg (mixedCanonicalPrefactorConstant_pos Kb Ko).le
          (Real.rpow_nonneg
            (log_pos (by exact_mod_cast
              (show 1 < dyadicScale j by omega))).le _))
        (Real.rpow_nonneg
          (log_pos (by exact_mod_cast (show 1 < L by omega))).le _)
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
            (Real.rpow_nonneg
              (log_pos (by exact_mod_cast
                (show 1 < dyadicScale j by omega))).le _))
          (Real.rpow_nonneg
            (log_pos (by exact_mod_cast (show 1 < L by omega))).le _))
        (Real.rpow_nonneg
          (zero_le_one.trans (scheduledLogLoss_one_le j)) _)
    have herror0 : 0 ≤ mixedScheduledSieveError j := by
      unfold mixedScheduledSieveError
      positivity
    have hY0 :
        (0 : ℝ) ≤
          (N / (dyadicScale j * dyadicScale j) : ℕ) :=
      Nat.cast_nonneg _
    have hXYnat := dyadic_sq_mul_mixedResidualCutoff_le N j
    have hXY :
        (dyadicScale j : ℝ) ^ 2 *
            (N / (dyadicScale j * dyadicScale j) : ℕ) ≤
          (N : ℝ) := by
      simpa [pow_two] using
        (show
          ((dyadicScale j * dyadicScale j *
            (N / (dyadicScale j * dyadicScale j)) : ℕ) : ℝ) ≤
              (N : ℝ) by exact_mod_cast hXYnat)
    have hindex :=
      log_dyadicScale_rpow_regularity_le_index_sq hj
    have hmainScaled :
        mixedBlockPrefactor L (dyadicScale j)
              sourceAnatomySlope Kb oddAnatomySlope Ko
              mixedSourceWeightBase mixedOddWeightBase *
            mixedScheduledMertensMain L
              mixedSourceWeightBase mixedOddWeightBase j *
            (N / (dyadicScale j * dyadicScale j) : ℕ) ≤
          mixedBoundaryMainConstant Kb Ko * (N : ℝ) *
            log (L : ℝ) ^
              (-mixedCanonicalRegularityExponent +
                mixedCanonicalRoughnessExponent) *
            log (dyadicScale j : ℝ) ^
              mixedCanonicalDyadicExponent *
            scheduledLogLoss j ^ (2 : ℝ) := by
      have hscaled :
          mixedBlockPrefactor L (dyadicScale j)
                sourceAnatomySlope Kb oddAnatomySlope Ko
                mixedSourceWeightBase mixedOddWeightBase *
              mixedScheduledMertensMain L
                mixedSourceWeightBase mixedOddWeightBase j ≤
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
                scheduledLogLoss j ^ (2 : ℝ)) := by
        calc
          _ ≤
              (mixedCanonicalPrefactorConstant Kb Ko *
                  log (dyadicScale j : ℝ) ^
                    mixedCanonicalRegularityExponent *
                  log (L : ℝ) ^
                    (-mixedCanonicalRegularityExponent)) *
                mixedScheduledMertensMain L
                  mixedSourceWeightBase mixedOddWeightBase j :=
            mul_le_mul_of_nonneg_right hpref hmain0
          _ ≤ _ := mul_le_mul_of_nonneg_left hmain hprefR0
      have hcoef0 :
          0 ≤ 8 * mixedCanonicalPrefactorConstant Kb Ko *
            mixedCanonicalScheduledProductConstant *
            log (dyadicScale j : ℝ) ^
              (mixedCanonicalRegularityExponent +
                mixedCanonicalProductExponent) *
            log (L : ℝ) ^
              (-mixedCanonicalRegularityExponent +
                mixedCanonicalRoughnessExponent) *
            scheduledLogLoss j ^ (2 : ℝ) := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by norm_num)
                  (mixedCanonicalPrefactorConstant_pos Kb Ko).le)
                mixedCanonicalScheduledProductConstant_pos.le)
              (Real.rpow_nonneg
                (log_pos (by exact_mod_cast
                  (show 1 < dyadicScale j by omega))).le _))
            (Real.rpow_nonneg
              (log_pos (by exact_mod_cast
                (show 1 < L by omega))).le _))
          (Real.rpow_nonneg
            (zero_le_one.trans (scheduledLogLoss_one_le j)) _)
      calc
        _ ≤
            ((mixedCanonicalPrefactorConstant Kb Ko *
                log (dyadicScale j : ℝ) ^
                  mixedCanonicalRegularityExponent *
                log (L : ℝ) ^
                  (-mixedCanonicalRegularityExponent)) *
              (8 * mixedCanonicalScheduledProductConstant *
                (dyadicScale j : ℝ) ^ 2 *
                log (dyadicScale j : ℝ) ^
                  mixedCanonicalProductExponent *
                log (L : ℝ) ^ mixedCanonicalRoughnessExponent *
                scheduledLogLoss j ^ (2 : ℝ))) *
              (N / (dyadicScale j * dyadicScale j) : ℕ) :=
          mul_le_mul_of_nonneg_right hscaled hY0
        _ =
            (8 * mixedCanonicalPrefactorConstant Kb Ko *
              mixedCanonicalScheduledProductConstant *
              log (dyadicScale j : ℝ) ^
                (mixedCanonicalRegularityExponent +
                  mixedCanonicalProductExponent) *
              log (L : ℝ) ^
                (-mixedCanonicalRegularityExponent +
                  mixedCanonicalRoughnessExponent) *
              scheduledLogLoss j ^ (2 : ℝ)) *
              ((dyadicScale j : ℝ) ^ 2 *
                (N / (dyadicScale j * dyadicScale j) : ℕ)) := by
          rw [Real.rpow_add
            (log_pos (by exact_mod_cast
              (show 1 < dyadicScale j by omega)))]
          rw [Real.rpow_add
            (log_pos (by exact_mod_cast
              (show 1 < L by omega)))]
          ring
        _ ≤
            (8 * mixedCanonicalPrefactorConstant Kb Ko *
              mixedCanonicalScheduledProductConstant *
              log (dyadicScale j : ℝ) ^
                (mixedCanonicalRegularityExponent +
                  mixedCanonicalProductExponent) *
              log (L : ℝ) ^
                (-mixedCanonicalRegularityExponent +
                  mixedCanonicalRoughnessExponent) *
              scheduledLogLoss j ^ (2 : ℝ)) * (N : ℝ) :=
          mul_le_mul_of_nonneg_left hXY hcoef0
        _ = _ := by
          unfold mixedBoundaryMainConstant mixedCanonicalDyadicExponent
          ring
    have herrorScaled :
        mixedBlockPrefactor L (dyadicScale j)
              sourceAnatomySlope Kb oddAnatomySlope Ko
              mixedSourceWeightBase mixedOddWeightBase *
            mixedScheduledSieveError j *
            (N / (dyadicScale j * dyadicScale j) : ℕ) ≤
          mixedBoundaryErrorConstant Kb Ko * (N : ℝ) *
            log (L : ℝ) ^
              (-mixedCanonicalRegularityExponent) *
            ((((j + 1 : ℕ) : ℝ) ^ 2) /
              (((j + 1 : ℕ) : ℝ) ^ 8)) := by
      have hscaled :
          mixedBlockPrefactor L (dyadicScale j)
                sourceAnatomySlope Kb oddAnatomySlope Ko
                mixedSourceWeightBase mixedOddWeightBase *
              mixedScheduledSieveError j ≤
            (mixedCanonicalPrefactorConstant Kb Ko *
                log (dyadicScale j : ℝ) ^
                  mixedCanonicalRegularityExponent *
                log (L : ℝ) ^
                  (-mixedCanonicalRegularityExponent)) *
              mixedScheduledSieveError j :=
        mul_le_mul_of_nonneg_right hpref herror0
      calc
        _ ≤
            ((mixedCanonicalPrefactorConstant Kb Ko *
                log (dyadicScale j : ℝ) ^
                  mixedCanonicalRegularityExponent *
                log (L : ℝ) ^
                  (-mixedCanonicalRegularityExponent)) *
              mixedScheduledSieveError j) *
              (N / (dyadicScale j * dyadicScale j) : ℕ) :=
          mul_le_mul_of_nonneg_right hscaled hY0
        _ =
            (9 * mixedCanonicalPrefactorConstant Kb Ko *
              log (L : ℝ) ^
                (-mixedCanonicalRegularityExponent) *
              log (dyadicScale j : ℝ) ^
                mixedCanonicalRegularityExponent /
              (((j + 1 : ℕ) : ℝ) ^ 8)) *
              ((dyadicScale j : ℝ) ^ 2 *
                (N / (dyadicScale j * dyadicScale j) : ℕ)) := by
          unfold mixedScheduledSieveError
          ring
        _ ≤
            (9 * mixedCanonicalPrefactorConstant Kb Ko *
              log (L : ℝ) ^
                (-mixedCanonicalRegularityExponent) *
              log (dyadicScale j : ℝ) ^
                mixedCanonicalRegularityExponent /
              (((j + 1 : ℕ) : ℝ) ^ 8)) * (N : ℝ) := by
          apply mul_le_mul_of_nonneg_left hXY
          exact div_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by norm_num)
                  (mixedCanonicalPrefactorConstant_pos Kb Ko).le)
                (Real.rpow_nonneg
                  (log_pos (by exact_mod_cast
                    (show 1 < L by omega))).le _))
              (Real.rpow_nonneg
                (log_pos (by exact_mod_cast
                  (show 1 < dyadicScale j by omega))).le _))
            (by positivity)
        _ ≤
            (9 * mixedCanonicalPrefactorConstant Kb Ko *
              log (L : ℝ) ^
                (-mixedCanonicalRegularityExponent) *
              (((j + 1 : ℕ) : ℝ) ^ 2 /
                (((j + 1 : ℕ) : ℝ) ^ 8))) * (N : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
          let A : ℝ :=
            9 * mixedCanonicalPrefactorConstant Kb Ko *
              log (L : ℝ) ^ (-mixedCanonicalRegularityExponent)
          have hA0 : 0 ≤ A := by
            dsimp [A]
            exact mul_nonneg
              (mul_nonneg (by norm_num)
                (mixedCanonicalPrefactorConstant_pos Kb Ko).le)
              (Real.rpow_nonneg
                (log_pos (by exact_mod_cast
                  (show 1 < L by omega))).le _)
          have hdiv :=
            div_le_div_of_nonneg_right hindex
              (by positivity :
                (0 : ℝ) ≤ (((j + 1 : ℕ) : ℝ) ^ 8))
          calc
            _ = A *
                (log (dyadicScale j : ℝ) ^
                  mixedCanonicalRegularityExponent /
                  (((j + 1 : ℕ) : ℝ) ^ 8)) := by
              dsimp [A]
              ring
            _ ≤ A *
                ((((j + 1 : ℕ) : ℝ) ^ 2) /
                  (((j + 1 : ℕ) : ℝ) ^ 8)) :=
              mul_le_mul_of_nonneg_left hdiv hA0
            _ = _ := by
              dsimp [A]
        _ = _ := by
          unfold mixedBoundaryErrorConstant
          ring
    calc
      _ ≤
          mixedBlockPrefactor L (dyadicScale j)
              sourceAnatomySlope Kb oddAnatomySlope Ko
              mixedSourceWeightBase mixedOddWeightBase *
            (mixedScheduledMertensMain L
                mixedSourceWeightBase mixedOddWeightBase j +
              mixedScheduledSieveError j) *
            (N / (dyadicScale j * dyadicScale j) : ℕ) := henvelope
      _ =
          mixedBlockPrefactor L (dyadicScale j)
              sourceAnatomySlope Kb oddAnatomySlope Ko
              mixedSourceWeightBase mixedOddWeightBase *
            mixedScheduledMertensMain L
              mixedSourceWeightBase mixedOddWeightBase j *
            (N / (dyadicScale j * dyadicScale j) : ℕ) +
          mixedBlockPrefactor L (dyadicScale j)
              sourceAnatomySlope Kb oddAnatomySlope Ko
              mixedSourceWeightBase mixedOddWeightBase *
            mixedScheduledSieveError j *
            (N / (dyadicScale j * dyadicScale j) : ℕ) := by ring
      _ ≤ _ := add_le_add hmainScaled herrorScaled
  · have hmainR0 :
        0 ≤ mixedBoundaryMainConstant Kb Ko * (N : ℝ) *
          log (L : ℝ) ^
            (-mixedCanonicalRegularityExponent +
              mixedCanonicalRoughnessExponent) *
          log (dyadicScale j : ℝ) ^
            mixedCanonicalDyadicExponent *
          scheduledLogLoss j ^ (2 : ℝ) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (mixedBoundaryMainConstant_pos Kb Ko).le
              (Nat.cast_nonneg N))
            (Real.rpow_nonneg
              (log_nonneg (by exact_mod_cast
                (show 1 ≤ L by omega))) _))
          (Real.rpow_nonneg
            (Real.log_natCast_nonneg _) _))
        (Real.rpow_nonneg
          (zero_le_one.trans (scheduledLogLoss_one_le j)) _)
    have herrorR0 :
        0 ≤ mixedBoundaryErrorConstant Kb Ko * (N : ℝ) *
          log (L : ℝ) ^
            (-mixedCanonicalRegularityExponent) *
          ((((j + 1 : ℕ) : ℝ) ^ 2) /
            (((j + 1 : ℕ) : ℝ) ^ 8)) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (mixedBoundaryErrorConstant_pos Kb Ko).le
            (Nat.cast_nonneg N))
          (Real.rpow_nonneg
            (log_nonneg (by exact_mod_cast
              (show 1 ≤ L by omega))) _))
        (div_nonneg (by positivity) (by positivity))
    linarith

/-! ## Boundary index sets -/

/-- The short transition window `X < L ≤ 16X`. -/
def mixedTransitionBoundaryIndexSet (L M : ℕ) : Finset ℕ :=
  (range M).filter fun j ↦
    dyadicScale j < L ∧ L ≤ 16 * dyadicScale j

/-- The genuinely residual boundary, with the zero residual quotient
removed (its refined block is exactly zero). -/
def mixedPositiveResidualBoundaryIndexSet
    (L N M : ℕ) : Finset ℕ :=
  (range M).filter fun j ↦
    L ≤ dyadicScale j ∧
      0 < N / (dyadicScale j * dyadicScale j) ∧
      N / (dyadicScale j * dyadicScale j) < L

theorem mixedTransition_indices_lt_add_four
    {L i j : ℕ}
    (hi : dyadicScale i < L)
    (hnear : L ≤ 16 * dyadicScale j) :
    i < j + 4 := by
  have hpow :
      2 ^ i < 2 ^ (j + 4) := by
    calc
      2 ^ i = dyadicScale i := by rfl
      _ < L := hi
      _ ≤ 16 * dyadicScale j := hnear
      _ = 2 ^ (j + 4) := by
        simp [dyadicScale, pow_add]
        ring
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow

theorem card_mixedTransitionBoundaryIndexSet_le_four
    (L M : ℕ) :
    (mixedTransitionBoundaryIndexSet L M).card ≤ 4 := by
  let s := mixedTransitionBoundaryIndexSet L M
  by_cases hs : s.Nonempty
  · let i := s.min' hs
    have hsubset : s ⊆ Ico i (i + 4) := by
      intro j hj
      have hiMem : i ∈ s := Finset.min'_mem s hs
      have hij : i ≤ j := Finset.min'_le s j hj
      dsimp [s] at hiMem hj
      rw [mixedTransitionBoundaryIndexSet, mem_filter] at hiMem hj
      exact mem_Ico.mpr
        ⟨hij,
          mixedTransition_indices_lt_add_four
            hj.2.1 hiMem.2.2⟩
    have hcard := Finset.card_le_card hsubset
    simpa [s] using hcard
  · have hs0 : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp [s, hs0]

theorem mixedResidualCutoff_ge_of_index_le
    {L N i J : ℕ}
    (hiJ : i ≤ J)
    (hN : L * dyadicScale J ^ 2 ≤ N) :
    L ≤ N / (dyadicScale i * dyadicScale i) := by
  have hscale : dyadicScale i ≤ dyadicScale J :=
    dyadicScale_mono hiJ
  have hsq : dyadicScale i ^ 2 ≤ dyadicScale J ^ 2 :=
    Nat.pow_le_pow_left hscale 2
  have hmul :
      L * (dyadicScale i * dyadicScale i) ≤ N := by
    simpa [pow_two] using
      (show L * dyadicScale i ^ 2 ≤ N by
        exact (Nat.mul_le_mul_left L hsq).trans hN)
  exact
    (Nat.le_div_iff_mul_le
      (Nat.mul_pos (dyadicScale_pos i) (dyadicScale_pos i))).2 hmul

theorem index_gt_of_mixedSmallResidual_of_large_N
    {L N i J : ℕ}
    (hsmall : N / (dyadicScale i * dyadicScale i) < L)
    (hN : L * dyadicScale J ^ 2 ≤ N) :
    J < i := by
  by_contra hnot
  exact (Nat.not_le_of_gt hsmall)
    (mixedResidualCutoff_ge_of_index_le
      (Nat.le_of_not_gt hnot) hN)

theorem mixedResidualCutoff_strictAnti
    {N i j : ℕ}
    (hij : i < j)
    (hi : 0 < N / (dyadicScale i * dyadicScale i)) :
    N / (dyadicScale j * dyadicScale j) <
      N / (dyadicScale i * dyadicScale i) := by
  have hsucc : i + 1 ≤ j := by omega
  have hscale :
      2 * dyadicScale i ≤ dyadicScale j := by
    have hmono := dyadicScale_mono hsucc
    simpa [dyadicScale, pow_succ, mul_comm, mul_left_comm,
      mul_assoc] using hmono
  have hden :
      4 * (dyadicScale i * dyadicScale i) ≤
        dyadicScale j * dyadicScale j := by
    calc
      4 * (dyadicScale i * dyadicScale i) =
          (2 * dyadicScale i) * (2 * dyadicScale i) := by ring
      _ ≤ dyadicScale j * dyadicScale j :=
        Nat.mul_le_mul hscale hscale
  have hdenPos :
      0 < 4 * (dyadicScale i * dyadicScale i) :=
    Nat.mul_pos (by norm_num)
      (Nat.mul_pos (dyadicScale_pos i) (dyadicScale_pos i))
  have hfirst :
      N / (dyadicScale j * dyadicScale j) ≤
        N / (4 * (dyadicScale i * dyadicScale i)) :=
    Nat.div_le_div_left hden hdenPos
  have heq :
      N / (4 * (dyadicScale i * dyadicScale i)) =
        (N / (dyadicScale i * dyadicScale i)) / 4 := by
    rw [Nat.div_div_eq_div_mul]
    congr 1
    ring
  calc
    N / (dyadicScale j * dyadicScale j) ≤
        N / (4 * (dyadicScale i * dyadicScale i)) := hfirst
    _ = (N / (dyadicScale i * dyadicScale i)) / 4 := heq
    _ < N / (dyadicScale i * dyadicScale i) :=
      Nat.div_lt_self hi (by norm_num)

theorem card_mixedPositiveResidualBoundaryIndexSet_le
    (L N M : ℕ) :
    (mixedPositiveResidualBoundaryIndexSet L N M).card ≤ L := by
  let s := mixedPositiveResidualBoundaryIndexSet L N M
  let f : ℕ → ℕ :=
    fun j ↦ N / (dyadicScale j * dyadicScale j)
  have hinj : Set.InjOn f s := by
    intro i hi j hj heq
    by_contra hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hi' : 0 < f i := by
        have hiFin : i ∈ s := hi
        dsimp [s] at hiFin
        rw [mixedPositiveResidualBoundaryIndexSet, mem_filter] at hiFin
        exact hiFin.2.2.1
      exact (Nat.ne_of_lt
        (mixedResidualCutoff_strictAnti hijlt hi')) heq.symm
    · have hj' : 0 < f j := by
        have hjFin : j ∈ s := hj
        dsimp [s] at hjFin
        rw [mixedPositiveResidualBoundaryIndexSet, mem_filter] at hjFin
        exact hjFin.2.2.1
      exact (Nat.ne_of_lt
        (mixedResidualCutoff_strictAnti hjilt hj')) heq
  have hsubset : s.image f ⊆ Ico 1 L := by
    intro y hy
    rw [mem_image] at hy
    rcases hy with ⟨j, hj, rfl⟩
    dsimp [s] at hj
    rw [mixedPositiveResidualBoundaryIndexSet, mem_filter] at hj
    exact mem_Ico.mpr ⟨hj.2.2.1, hj.2.2.2⟩
  calc
    s.card = (s.image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Ico 1 L).card := Finset.card_le_card hsubset
    _ ≤ L := by simp

/-- The boundary is exactly its transition part plus its positive
small-residual part. -/
theorem mixedCanonicalBoundaryBlock_eq_transition_add_residual
    {L N j : ℕ} {Kb Ko : ℝ} (hL : 17 ≤ L) :
    mixedCanonicalBoundaryBlock L N Kb Ko j =
      (if dyadicScale j < L then
        mixedCanonicalBoundaryBlock L N Kb Ko j else 0) +
      (if L ≤ dyadicScale j ∧
          0 < N / (dyadicScale j * dyadicScale j) ∧
          N / (dyadicScale j * dyadicScale j) < L then
        mixedCanonicalBoundaryBlock L N Kb Ko j else 0) := by
  by_cases hX : dyadicScale j < L
  · rw [if_pos hX, if_neg (by omega)]
    simp
  · have hLX : L ≤ dyadicScale j := Nat.le_of_not_gt hX
    rw [if_neg hX]
    by_cases hsmall :
        N / (dyadicScale j * dyadicScale j) < L
    · by_cases hpos :
          0 < N / (dyadicScale j * dyadicScale j)
      · rw [if_pos ⟨hLX, hpos, hsmall⟩]
        simp
      · have hzero :
            N / (dyadicScale j * dyadicScale j) = 0 :=
          Nat.eq_zero_of_not_pos hpos
        have hrefined :
            mixedRefinedScheduledBlockBound
              L N sourceAnatomySlope Kb oddAnatomySlope Ko
                mixedSourceWeightBase mixedOddWeightBase j = 0 :=
          mixedRefinedScheduledBlockBound_eq_zero_of_residual_eq_zero
            hL hzero
        rw [if_neg (by
          intro h
          exact hpos h.2.1)]
        unfold mixedCanonicalBoundaryBlock
        by_cases hnear : L ≤ 16 * dyadicScale j
        · rw [if_pos ⟨hnear, Or.inr hsmall⟩, hrefined]
          simp
        · rw [if_neg (by
            intro h
            exact hnear h.1)]
          simp
    · rw [if_neg (by
        intro h
        exact hsmall h.2.2)]
      unfold mixedCanonicalBoundaryBlock
      rw [if_neg (by
        intro h
        rcases h.2 with hb | hb
        · exact hX hb
        · exact hsmall hb)]
      simp

theorem sum_mixedCanonicalBoundaryBlock_eq_transition_add_residual
    {L N M : ℕ} {Kb Ko : ℝ} (hL : 17 ≤ L) :
    (∑ j ∈ range M,
        mixedCanonicalBoundaryBlock L N Kb Ko j) =
      (∑ j ∈ mixedTransitionBoundaryIndexSet L M,
        mixedCanonicalBoundaryBlock L N Kb Ko j) +
      ∑ j ∈ mixedPositiveResidualBoundaryIndexSet L N M,
        mixedCanonicalBoundaryBlock L N Kb Ko j := by
  calc
    _ = ∑ j ∈ range M,
        ((if dyadicScale j < L then
            mixedCanonicalBoundaryBlock L N Kb Ko j else 0) +
          (if L ≤ dyadicScale j ∧
              0 < N / (dyadicScale j * dyadicScale j) ∧
              N / (dyadicScale j * dyadicScale j) < L then
            mixedCanonicalBoundaryBlock L N Kb Ko j else 0)) := by
      apply sum_congr rfl
      intro j hj
      exact mixedCanonicalBoundaryBlock_eq_transition_add_residual hL
    _ = _ := by
      rw [sum_add_distrib]
      apply congrArg₂ (· + ·)
      · unfold mixedTransitionBoundaryIndexSet
        rw [sum_filter]
        apply sum_congr rfl
        intro j hj
        by_cases hX : dyadicScale j < L
        · rw [if_pos hX]
          by_cases hnear : L ≤ 16 * dyadicScale j
          · rw [if_pos ⟨hX, hnear⟩]
          · rw [if_neg (by
              intro h
              exact hnear h.2)]
            unfold mixedCanonicalBoundaryBlock
            rw [if_neg (by
              intro h
              exact hnear h.1)]
        · rw [if_neg hX, if_neg (by
            intro h
            exact hX h.1)]
      · unfold mixedPositiveResidualBoundaryIndexSet
        rw [sum_filter]

/-! ## Power profiles and scheduled-tail setup -/

def mixedBoundaryMainRaw
    (L N : ℕ) (Kb Ko : ℝ) (j : ℕ) : ℝ :=
  mixedBoundaryMainConstant Kb Ko * (N : ℝ) *
    log (L : ℝ) ^
      (-mixedCanonicalRegularityExponent +
        mixedCanonicalRoughnessExponent) *
    log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent *
    scheduledLogLoss j ^ (2 : ℝ)

def mixedBoundaryErrorRaw
    (L N : ℕ) (Kb Ko : ℝ) (j : ℕ) : ℝ :=
  mixedBoundaryErrorConstant Kb Ko * (N : ℝ) *
    log (L : ℝ) ^ (-mixedCanonicalRegularityExponent) *
    ((((j + 1 : ℕ) : ℝ) ^ 2) /
      (((j + 1 : ℕ) : ℝ) ^ 8))

theorem mixedCanonicalBoundaryBlock_le_mainRaw_add_errorRaw
    {L N j : ℕ} {Kb Ko : ℝ}
    (hL : 3 ≤ L) (hj : 1 ≤ j)
    (hdom : 32 * sieveRadius j ≤ j)
    (herrors : mixedCanonicalScheduleErrorsHold j) :
    mixedCanonicalBoundaryBlock L N Kb Ko j ≤
      mixedBoundaryMainRaw L N Kb Ko j +
        mixedBoundaryErrorRaw L N Kb Ko j := by
  simpa [mixedBoundaryMainRaw, mixedBoundaryErrorRaw] using
    (mixedCanonicalBoundaryBlock_le_raw
      (L := L) (N := N) (j := j)
      (Kb := Kb) (Ko := Ko) hL hj hdom herrors)

theorem exists_mixedBoundaryScheduleStart :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ j ≥ H,
      32 * sieveRadius j ≤ j ∧
        mixedCanonicalScheduleErrorsHold j := by
  have hevent :
      ∀ᶠ j : ℕ in atTop,
        32 * sieveRadius j ≤ j ∧
          mixedCanonicalScheduleErrorsHold j := by
    filter_upwards
      [eventually_sieveSchedule_dominates,
        eventually_scheduledFactorialTail_le_inv_add_one_pow_eight,
        eventually_scheduledPolynomialBoundary_le] with
        j hdom htail hboundary
    exact ⟨hdom, htail, hboundary⟩
  rcases eventually_atTop.1 hevent with ⟨H₀, hH₀⟩
  refine ⟨max H₀ 1, le_max_right _ _, ?_⟩
  intro j hj
  exact hH₀ j ((le_max_left H₀ 1).trans hj)

/-- The small logarithmic absorption already used for the bulk leaves
the boundary dyadic exponent strictly negative. -/
theorem mixedBoundaryAbsorbedExponent_lt_zero :
    mixedCanonicalDyadicExponent + mixedBulkLogAbsorption < 0 := by
  have hcross := mixedCanonicalCross_add_absorption_lt_neg_one
  have hres := mixedCanonicalResidualExponent_gt_neg_one
  rw [← mixedCanonicalDyadic_add_residualExponent] at hcross
  linarith

def mixedBoundaryProfileConstant : ℝ :=
  mixedTerminalDyadicIndexConstant * mixedScheduleLogConstant

theorem mixedBoundaryProfileConstant_pos :
    0 < mixedBoundaryProfileConstant := by
  unfold mixedBoundaryProfileConstant
  exact mul_pos mixedTerminalDyadicIndexConstant_pos
    mixedScheduleLogConstant_pos

theorem eventually_mixedBoundaryMainProfile_absorbed :
    ∀ᶠ j : ℕ in atTop,
      log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent *
          scheduledLogLoss j ^ (2 : ℝ) ≤
        mixedBoundaryProfileConstant *
          (((j + 1 : ℕ) : ℝ) ^
            (mixedCanonicalDyadicExponent +
              mixedBulkLogAbsorption)) := by
  filter_upwards
    [eventually_log_add_one_rpow_le_rpow
      (4 : ℝ) mixedBulkLogAbsorption_pos,
      eventually_ge_atTop 1] with j habs hj
  have hdyadic :=
    log_dyadicScale_rpow_terminal_le_index
      (j := j) hj
  have hloss := scheduledLogLoss_sq_le_log_four hj
  have hindex0 :
      0 ≤ (((j + 1 : ℕ) : ℝ) ^
        mixedCanonicalDyadicExponent) :=
    Real.rpow_nonneg (by positivity) _
  have hlog0 :
      0 ≤ log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ) :=
    Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  calc
    log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent *
          scheduledLogLoss j ^ (2 : ℝ)
        ≤
      (mixedTerminalDyadicIndexConstant *
          (((j + 1 : ℕ) : ℝ) ^
            mixedCanonicalDyadicExponent)) *
        (mixedScheduleLogConstant *
          log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) :=
      mul_le_mul hdyadic hloss
        (by
          exact Real.rpow_nonneg
            (zero_le_one.trans (scheduledLogLoss_one_le j)) _)
        (mul_nonneg mixedTerminalDyadicIndexConstant_pos.le hindex0)
    _ ≤
      (mixedTerminalDyadicIndexConstant *
          mixedScheduleLogConstant) *
        ((((j + 1 : ℕ) : ℝ) ^
            mixedCanonicalDyadicExponent) *
          (((j + 1 : ℕ) : ℝ) ^ mixedBulkLogAbsorption)) := by
      have habs' :=
        mul_le_mul_of_nonneg_left habs hindex0
      calc
        _ =
            (mixedTerminalDyadicIndexConstant *
              mixedScheduleLogConstant) *
            ((((j + 1 : ℕ) : ℝ) ^
                mixedCanonicalDyadicExponent) *
              log (((j + 1 : ℕ) : ℝ)) ^ (4 : ℝ)) := by ring
        _ ≤
            (mixedTerminalDyadicIndexConstant *
              mixedScheduleLogConstant) *
            ((((j + 1 : ℕ) : ℝ) ^
                mixedCanonicalDyadicExponent) *
              (((j + 1 : ℕ) : ℝ) ^ mixedBulkLogAbsorption)) :=
          mul_le_mul_of_nonneg_left habs'
            (mul_nonneg mixedTerminalDyadicIndexConstant_pos.le
              mixedScheduleLogConstant_pos.le)
    _ = _ := by
      unfold mixedBoundaryProfileConstant
      rw [← Real.rpow_add (by positivity :
        (0 : ℝ) < ((j + 1 : ℕ) : ℝ))]

theorem tendsto_mixedBoundaryAbsorbedPower_zero :
    Tendsto
      (fun j : ℕ ↦
        (((j + 1 : ℕ) : ℝ) ^
          (mixedCanonicalDyadicExponent +
            mixedBulkLogAbsorption)))
      atTop (𝓝 0) := by
  let η : ℝ :=
    -(mixedCanonicalDyadicExponent + mixedBulkLogAbsorption)
  have hη : 0 < η := by
    dsimp [η]
    linarith [mixedBoundaryAbsorbedExponent_lt_zero]
  have ht := tendsto_rpow_neg_atTop hη
  have hcast :
      Tendsto (fun j : ℕ ↦ (((j + 1 : ℕ) : ℝ)))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have heq :
      -η =
        mixedCanonicalDyadicExponent + mixedBulkLogAbsorption := by
    dsimp [η]
    ring
  rw [← heq]
  exact ht.comp hcast

theorem tendsto_mixedBoundaryErrorProfile_zero :
    Tendsto
      (fun j : ℕ ↦
        ((((j + 1 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)))
      atTop (𝓝 0) := by
  have ht := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 6)
  have hcast :
      Tendsto (fun j : ℕ ↦ (((j + 1 : ℕ) : ℝ)))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  refine (ht.comp hcast).congr' ?_
  filter_upwards with j
  simpa using mixedCanonicalErrorProfile_eq j

/-- For fixed `L`, the positive small-residual boundary is `o(N)`,
uniformly in the finite dyadic endpoint. -/
theorem eventually_sum_mixedPositiveResidualBoundary_le
    (L : ℕ) (Kb : ℝ) (hL : 17 ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
      (∑ j ∈ mixedPositiveResidualBoundaryIndexSet L N M,
        mixedCanonicalBoundaryBlock
          L N Kb (oddBudget L) j) ≤
        ε * (N : ℝ) := by
  let CM : ℝ :=
    mixedBoundaryMainConstant Kb (oddBudget L) *
      log (L : ℝ) ^
        (-mixedCanonicalRegularityExponent +
          mixedCanonicalRoughnessExponent) *
      mixedBoundaryProfileConstant
  let CE : ℝ :=
    mixedBoundaryErrorConstant Kb (oddBudget L) *
      log (L : ℝ) ^ (-mixedCanonicalRegularityExponent)
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hCM : 0 < CM := by
    dsimp [CM]
    exact mul_pos
      (mul_pos (mixedBoundaryMainConstant_pos _ _)
        (Real.rpow_pos_of_pos hlogL _))
      mixedBoundaryProfileConstant_pos
  have hCE : 0 < CE := by
    dsimp [CE]
    exact mul_pos (mixedBoundaryErrorConstant_pos _ _)
      (Real.rpow_pos_of_pos hlogL _)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hmainSmall :
      ∀ᶠ j : ℕ in atTop,
        (((j + 1 : ℕ) : ℝ) ^
          (mixedCanonicalDyadicExponent +
            mixedBulkLogAbsorption)) <
          ε / (2 * (L : ℝ) * CM) :=
    (tendsto_order.1 tendsto_mixedBoundaryAbsorbedPower_zero).2
      _ (div_pos hε (mul_pos (mul_pos (by norm_num) hLpos) hCM))
  have herrorSmall :
      ∀ᶠ j : ℕ in atTop,
        ((((j + 1 : ℕ) : ℝ) ^ 2) /
          (((j + 1 : ℕ) : ℝ) ^ 8)) <
          ε / (2 * (L : ℝ) * CE) :=
    (tendsto_order.1 tendsto_mixedBoundaryErrorProfile_zero).2
      _ (div_pos hε (mul_pos (mul_pos (by norm_num) hLpos) hCE))
  have hprofile := eventually_mixedBoundaryMainProfile_absorbed
  rcases exists_mixedBoundaryScheduleStart with ⟨HS, hHS1, hHS⟩
  rcases eventually_atTop.1 hmainSmall with ⟨HM, hHM⟩
  rcases eventually_atTop.1 herrorSmall with ⟨HE, hHE⟩
  rcases eventually_atTop.1 hprofile with ⟨HP, hHP⟩
  let J : ℕ := max HS (max HM (max HE HP))
  filter_upwards
    [eventually_ge_atTop (L * dyadicScale J ^ 2)] with N hN
  intro M
  let s := mixedPositiveResidualBoundaryIndexSet L N M
  have hpoint :
      ∀ j ∈ s,
        mixedCanonicalBoundaryBlock
            L N Kb (oddBudget L) j ≤
          (ε / (L : ℝ)) * (N : ℝ) := by
    intro j hj
    have hj' := hj
    dsimp [s] at hj'
    rw [mixedPositiveResidualBoundaryIndexSet, mem_filter] at hj'
    have hJj :
        J < j :=
      index_gt_of_mixedSmallResidual_of_large_N
        hj'.2.2.2 hN
    have hSj : HS ≤ j :=
      (le_max_left HS (max HM (max HE HP))).trans hJj.le
    have hMj : HM ≤ j :=
      (le_max_left HM (max HE HP)).trans
        ((le_max_right HS (max HM (max HE HP))).trans hJj.le)
    have hEj : HE ≤ j :=
      (le_max_left HE HP).trans
        ((le_max_right HM (max HE HP)).trans
          ((le_max_right HS (max HM (max HE HP))).trans hJj.le))
    have hPj : HP ≤ j :=
      (le_max_right HE HP).trans
        ((le_max_right HM (max HE HP)).trans
          ((le_max_right HS (max HM (max HE HP))).trans hJj.le))
    have hraw :=
      mixedCanonicalBoundaryBlock_le_mainRaw_add_errorRaw
        (L := L) (N := N) (j := j)
        (Kb := Kb) (Ko := oddBudget L)
        (by omega) (hHS1.trans hSj) (hHS j hSj).1 (hHS j hSj).2
    have hmainProfile := hHP j hPj
    have hmainSmall' := (hHM j hMj).le
    have herrorSmall' := (hHE j hEj).le
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hmain :
        mixedBoundaryMainRaw L N Kb (oddBudget L) j ≤
          (ε / (2 * (L : ℝ))) * (N : ℝ) := by
      calc
        mixedBoundaryMainRaw L N Kb (oddBudget L) j
            =
          ((N : ℝ) *
            (mixedBoundaryMainConstant Kb (oddBudget L) *
              log (L : ℝ) ^
                (-mixedCanonicalRegularityExponent +
                  mixedCanonicalRoughnessExponent))) *
            (log (dyadicScale j : ℝ) ^
                mixedCanonicalDyadicExponent *
              scheduledLogLoss j ^ (2 : ℝ)) := by
          unfold mixedBoundaryMainRaw
          ring
        _ ≤
          ((N : ℝ) *
            (mixedBoundaryMainConstant Kb (oddBudget L) *
              log (L : ℝ) ^
                (-mixedCanonicalRegularityExponent +
                  mixedCanonicalRoughnessExponent))) *
            (mixedBoundaryProfileConstant *
              (((j + 1 : ℕ) : ℝ) ^
                (mixedCanonicalDyadicExponent +
                  mixedBulkLogAbsorption))) := by
          apply mul_le_mul_of_nonneg_left hmainProfile
          exact mul_nonneg hN0
            (mul_nonneg
              (mixedBoundaryMainConstant_pos _ _).le
              (Real.rpow_nonneg hlogL.le _))
        _ =
          (N : ℝ) * CM *
            (((j + 1 : ℕ) : ℝ) ^
              (mixedCanonicalDyadicExponent +
                mixedBulkLogAbsorption)) := by
          dsimp [CM]
          ring
        _ ≤
          (N : ℝ) * CM *
            (ε / (2 * (L : ℝ) * CM)) :=
          mul_le_mul_of_nonneg_left hmainSmall'
            (mul_nonneg hN0 hCM.le)
        _ = (ε / (2 * (L : ℝ))) * (N : ℝ) := by
          field_simp [hCM.ne', hLpos.ne']
    have herror :
        mixedBoundaryErrorRaw L N Kb (oddBudget L) j ≤
          (ε / (2 * (L : ℝ))) * (N : ℝ) := by
      calc
        mixedBoundaryErrorRaw L N Kb (oddBudget L) j =
            (N : ℝ) * CE *
              ((((j + 1 : ℕ) : ℝ) ^ 2) /
                (((j + 1 : ℕ) : ℝ) ^ 8)) := by
          unfold mixedBoundaryErrorRaw
          dsimp [CE]
          ring
        _ ≤
            (N : ℝ) * CE *
              (ε / (2 * (L : ℝ) * CE)) :=
          mul_le_mul_of_nonneg_left herrorSmall'
            (mul_nonneg hN0 hCE.le)
        _ = (ε / (2 * (L : ℝ))) * (N : ℝ) := by
          field_simp [hCE.ne', hLpos.ne']
    calc
      _ ≤ mixedBoundaryMainRaw L N Kb (oddBudget L) j +
          mixedBoundaryErrorRaw L N Kb (oddBudget L) j := hraw
      _ ≤
          (ε / (2 * (L : ℝ))) * (N : ℝ) +
            (ε / (2 * (L : ℝ))) * (N : ℝ) :=
        add_le_add hmain herror
      _ = (ε / (L : ℝ)) * (N : ℝ) := by ring
  have hsumCard :=
    Finset.sum_le_card_nsmul s _
      ((ε / (L : ℝ)) * (N : ℝ)) hpoint
  have hcard : s.card ≤ L := by
    dsimp [s]
    exact card_mixedPositiveResidualBoundaryIndexSet_le L N M
  have htarget0 :
      0 ≤ (ε / (L : ℝ)) * (N : ℝ) :=
    mul_nonneg (div_nonneg hε.le hLpos.le) (Nat.cast_nonneg N)
  calc
    (∑ j ∈ mixedPositiveResidualBoundaryIndexSet L N M,
        mixedCanonicalBoundaryBlock L N Kb (oddBudget L) j)
        ≤ s.card • ((ε / (L : ℝ)) * (N : ℝ)) := hsumCard
    _ = (s.card : ℝ) * ((ε / (L : ℝ)) * (N : ℝ)) := by simp
    _ ≤ (L : ℝ) * ((ε / (L : ℝ)) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) htarget0
    _ = ε * (N : ℝ) := by
      field_simp [hLpos.ne']

/-! ## The short transition window -/

def mixedBoundaryMainFixedConstant (Kb : ℝ) : ℝ :=
  8 *
    (mixedSourceWeightBase ^ Kb *
      (5 : ℝ) ^ mixedCanonicalRegularityExponent) *
    mixedCanonicalScheduledProductConstant

theorem mixedBoundaryMainFixedConstant_pos (Kb : ℝ) :
    0 < mixedBoundaryMainFixedConstant Kb := by
  unfold mixedBoundaryMainFixedConstant
  positivity [mixedSourceWeightBase_gt_one,
    mixedCanonicalScheduledProductConstant_pos]

theorem mixedBoundaryMainConstant_eq_fixed (Kb Ko : ℝ) :
    mixedBoundaryMainConstant Kb Ko =
      mixedBoundaryMainFixedConstant Kb *
        mixedOddWeightBase ^ Ko := by
  unfold mixedBoundaryMainConstant mixedBoundaryMainFixedConstant
    mixedCanonicalPrefactorConstant
  ring

def mixedBoundaryErrorFixedConstant (Kb : ℝ) : ℝ :=
  9 *
    (mixedSourceWeightBase ^ Kb *
      (5 : ℝ) ^ mixedCanonicalRegularityExponent)

theorem mixedBoundaryErrorFixedConstant_pos (Kb : ℝ) :
    0 < mixedBoundaryErrorFixedConstant Kb := by
  unfold mixedBoundaryErrorFixedConstant
  positivity [mixedSourceWeightBase_gt_one]

theorem mixedBoundaryErrorConstant_eq_fixed (Kb Ko : ℝ) :
    mixedBoundaryErrorConstant Kb Ko =
      mixedBoundaryErrorFixedConstant Kb *
        mixedOddWeightBase ^ Ko := by
  unfold mixedBoundaryErrorConstant mixedBoundaryErrorFixedConstant
    mixedCanonicalPrefactorConstant
  ring

def mixedTransitionMainAsymptoticConstant (Kb : ℝ) : ℝ :=
  mixedBoundaryMainFixedConstant Kb *
    mixedBoundaryProfileConstant *
    (1 / (2 * log 2)) ^
      (mixedCanonicalDyadicExponent + mixedBulkLogAbsorption)

theorem mixedTransitionMainAsymptoticConstant_pos (Kb : ℝ) :
    0 < mixedTransitionMainAsymptoticConstant Kb := by
  unfold mixedTransitionMainAsymptoticConstant
  exact mul_pos
    (mul_pos (mixedBoundaryMainFixedConstant_pos Kb)
      mixedBoundaryProfileConstant_pos)
    (Real.rpow_pos_of_pos
      (by positivity [log_pos (by norm_num : (1 : ℝ) < 2)]) _)

def mixedTransitionErrorAsymptoticConstant (Kb : ℝ) : ℝ :=
  mixedBoundaryErrorFixedConstant Kb *
    (1 / (2 * log 2)) ^ (-6 : ℝ)

theorem mixedTransitionErrorAsymptoticConstant_pos (Kb : ℝ) :
    0 < mixedTransitionErrorAsymptoticConstant Kb := by
  unfold mixedTransitionErrorAsymptoticConstant
  exact mul_pos (mixedBoundaryErrorFixedConstant_pos Kb)
    (Real.rpow_pos_of_pos
      (by positivity [log_pos (by norm_num : (1 : ℝ) < 2)]) _)

theorem eventually_mixedTransitionMainCoefficient_le
    (Kb D : ℝ) (hD : 0 < D) :
    ∀ᶠ L : ℕ in atTop,
      mixedTransitionMainAsymptoticConstant Kb *
          mixedOddWeightBase ^ oddBudget L *
          log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption) ≤
        Erdos327.roughDensity L / (16 * D) := by
  let η : ℝ :=
    2 - oddBudgetSlope * log mixedOddWeightBase -
      mixedBulkLogAbsorption
  have hη : 1 < η := by
    dsimp [η]
    linarith [mixedOddBudget_add_absorption_lt_one]
  have hbase :=
    eventually_const_mul_log_rpow_neg_mul_loglog_rpow_le_roughDensity
      (C := mixedTransitionMainAsymptoticConstant Kb)
      (D := 16 * D) (η := η) (m := 0)
      (mixedTransitionMainAsymptoticConstant_pos Kb).le
      (mul_pos (by norm_num) hD) hη
  filter_upwards [hbase, eventually_ge_atTop 3] with L hbound hL
  have hLreal : (1 : ℝ) < L := by
    exact_mod_cast (show 1 < L by omega)
  have hlogL : 0 < log (L : ℝ) := log_pos hLreal
  rw [oddBudget, base_rpow_mul_loglog
    (by linarith [mixedOddWeightBase_gt_one]) hLreal]
  have hcombine :
      log (L : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption) =
        log (L : ℝ) ^ (-η) := by
    rw [← Real.rpow_add hlogL]
    congr 1
    dsimp [η]
    ring
  calc
    _ =
      mixedTransitionMainAsymptoticConstant Kb *
        (log (L : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (L : ℝ) ^ (-2 + mixedBulkLogAbsorption)) := by ring
    _ =
      mixedTransitionMainAsymptoticConstant Kb *
        log (L : ℝ) ^ (-η) := by rw [hcombine]
    _ =
      mixedTransitionMainAsymptoticConstant Kb *
        log (L : ℝ) ^ (-η) *
        log (log (L : ℝ)) ^ (0 : ℝ) := by
      rw [Real.rpow_zero, mul_one]
    _ ≤ _ := hbound

theorem eventually_mixedTransitionErrorCoefficient_le
    (Kb D : ℝ) (hD : 0 < D) :
    ∀ᶠ L : ℕ in atTop,
      mixedTransitionErrorAsymptoticConstant Kb *
          mixedOddWeightBase ^ oddBudget L *
          log (L : ℝ) ^
            (-mixedCanonicalRegularityExponent - 6) ≤
        Erdos327.roughDensity L / (16 * D) := by
  let η : ℝ :=
    mixedCanonicalRegularityExponent + 6 -
      oddBudgetSlope * log mixedOddWeightBase
  have hη : 1 < η := by
    dsimp [η]
    linarith [mixedOddBudgetExponent_lt_regularity]
  have hbase :=
    eventually_const_mul_log_rpow_neg_mul_loglog_rpow_le_roughDensity
      (C := mixedTransitionErrorAsymptoticConstant Kb)
      (D := 16 * D) (η := η) (m := 0)
      (mixedTransitionErrorAsymptoticConstant_pos Kb).le
      (mul_pos (by norm_num) hD) hη
  filter_upwards [hbase, eventually_ge_atTop 3] with L hbound hL
  have hLreal : (1 : ℝ) < L := by
    exact_mod_cast (show 1 < L by omega)
  have hlogL : 0 < log (L : ℝ) := log_pos hLreal
  rw [oddBudget, base_rpow_mul_loglog
    (by linarith [mixedOddWeightBase_gt_one]) hLreal]
  have hcombine :
      log (L : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (L : ℝ) ^
            (-mixedCanonicalRegularityExponent - 6) =
        log (L : ℝ) ^ (-η) := by
    rw [← Real.rpow_add hlogL]
    congr 1
    dsimp [η]
    ring
  calc
    _ =
      mixedTransitionErrorAsymptoticConstant Kb *
        (log (L : ℝ) ^
            (oddBudgetSlope * log mixedOddWeightBase) *
          log (L : ℝ) ^
            (-mixedCanonicalRegularityExponent - 6)) := by ring
    _ =
      mixedTransitionErrorAsymptoticConstant Kb *
        log (L : ℝ) ^ (-η) := by rw [hcombine]
    _ =
      mixedTransitionErrorAsymptoticConstant Kb *
        log (L : ℝ) ^ (-η) *
        log (log (L : ℝ)) ^ (0 : ℝ) := by
      rw [Real.rpow_zero, mul_one]
    _ ≤ _ := hbound

/-- Uniform estimate for the complete four-block transition window. -/
theorem eventually_sum_mixedTransitionBoundary_le
    (Kb D : ℝ) (hD : 0 < D) :
    ∀ᶠ L : ℕ in atTop, ∀ N M : ℕ,
      (∑ j ∈ mixedTransitionBoundaryIndexSet L M,
        mixedCanonicalBoundaryBlock
          L N Kb (oddBudget L) j) ≤
        (N : ℝ) * Erdos327.roughDensity L / (2 * D) := by
  rcases exists_mixedBoundaryScheduleStart with ⟨HS, hHS1, hHS⟩
  rcases eventually_atTop.1
      eventually_mixedBoundaryMainProfile_absorbed with ⟨HP, hHP⟩
  let H : ℕ := max HS HP
  filter_upwards
    [eventually_mixedTransitionMainCoefficient_le Kb D hD,
      eventually_mixedTransitionErrorCoefficient_le Kb D hD,
      eventually_ge_atTop (2 ^ 9),
      eventually_ge_atTop 17,
      eventually_fixed_le_mixedBulkMovingStart (max H 1)] with
      L hmainCoef herrorCoef hL512 hL17 hstart
  intro N M
  have hL3 : 3 ≤ L := by omega
  have hlogNat : 9 ≤ Nat.log 2 L := by
    have h :=
      Nat.log_mono_right (b := 2) hL512
    rw [Nat.log_pow (by norm_num : 1 < 2)] at h
    exact h
  have hstartH : H ≤ mixedBulkMovingStart L :=
    (le_max_left H 1).trans hstart
  have hstart1 : 1 ≤ mixedBulkMovingStart L :=
    (le_max_right H 1).trans hstart
  have hlogStart :=
    log_div_le_mixedBulkMovingStart hL3 hlogNat
  have hlogL : 0 < log (L : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < L by omega))
  have hratioPos :
      0 < log (L : ℝ) / (2 * log 2) := by
    positivity [log_pos (by norm_num : (1 : ℝ) < 2)]
  have hinvPos : 0 < (1 / (2 * log 2) : ℝ) := by
    positivity [log_pos (by norm_num : (1 : ℝ) < 2)]
  let s := mixedTransitionBoundaryIndexSet L M
  have hpoint :
      ∀ j ∈ s,
        mixedCanonicalBoundaryBlock
            L N Kb (oddBudget L) j ≤
          (N : ℝ) *
              (Erdos327.roughDensity L / (16 * D)) +
            (N : ℝ) *
              (Erdos327.roughDensity L / (16 * D)) := by
    intro j hj
    have hj' := hj
    dsimp [s] at hj'
    rw [mixedTransitionBoundaryIndexSet, mem_filter] at hj'
    have hnear := hj'.2.2
    have hstartj :
        mixedBulkMovingStart L ≤ j :=
      mixedBulkMovingStart_le_of_near hnear
    have hHj : H ≤ j := hstartH.trans hstartj
    have hSj : HS ≤ j := (le_max_left HS HP).trans hHj
    have hPj : HP ≤ j := (le_max_right HS HP).trans hHj
    have hraw :=
      mixedCanonicalBoundaryBlock_le_mainRaw_add_errorRaw
        (L := L) (N := N) (j := j)
        (Kb := Kb) (Ko := oddBudget L)
        hL3 (hHS1.trans hSj) (hHS j hSj).1 (hHS j hSj).2
    let r : ℝ :=
      mixedCanonicalDyadicExponent + mixedBulkLogAbsorption
    have hr : r < 0 := by
      dsimp [r]
      exact mixedBoundaryAbsorbedExponent_lt_zero
    have hstartReal :
        (0 : ℝ) < mixedBulkMovingStart L := by
      exact_mod_cast (show 0 < mixedBulkMovingStart L by omega)
    have hstartLe :
        (mixedBulkMovingStart L : ℝ) ≤
          (((j + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (show mixedBulkMovingStart L ≤ j + 1 by omega)
    have hjpow :
        (((j + 1 : ℕ) : ℝ) ^ r) ≤
          (mixedBulkMovingStart L : ℝ) ^ r :=
      Real.rpow_le_rpow_of_nonpos hstartReal hstartLe hr.le
    have hstartPow :
        (mixedBulkMovingStart L : ℝ) ^ r ≤
          (1 / (2 * log 2)) ^ r *
            log (L : ℝ) ^ r := by
      have hanti :=
        Real.rpow_le_rpow_of_nonpos
          hratioPos hlogStart hr.le
      calc
        _ ≤ (log (L : ℝ) / (2 * log 2)) ^ r := hanti
        _ =
            (1 / (2 * log 2)) ^ r *
              log (L : ℝ) ^ r := by
          rw [show log (L : ℝ) / (2 * log 2) =
              (1 / (2 * log 2)) * log (L : ℝ) by ring,
            Real.mul_rpow hinvPos.le hlogL.le]
    have hprofile :
        log (dyadicScale j : ℝ) ^ mixedCanonicalDyadicExponent *
            scheduledLogLoss j ^ (2 : ℝ) ≤
          mixedBoundaryProfileConstant *
            ((1 / (2 * log 2)) ^ r *
              log (L : ℝ) ^ r) := by
      calc
        _ ≤ mixedBoundaryProfileConstant *
            (((j + 1 : ℕ) : ℝ) ^ r) := by
          simpa [r] using hHP j hPj
        _ ≤ mixedBoundaryProfileConstant *
            ((mixedBulkMovingStart L : ℝ) ^ r) :=
          mul_le_mul_of_nonneg_left hjpow
            mixedBoundaryProfileConstant_pos.le
        _ ≤ mixedBoundaryProfileConstant *
            ((1 / (2 * log 2)) ^ r *
              log (L : ℝ) ^ r) :=
          mul_le_mul_of_nonneg_left hstartPow
            mixedBoundaryProfileConstant_pos.le
    have herrorProfile :
        ((((j + 1 : ℕ) : ℝ) ^ 2) /
            (((j + 1 : ℕ) : ℝ) ^ 8)) ≤
          (1 / (2 * log 2)) ^ (-6 : ℝ) *
            log (L : ℝ) ^ (-6 : ℝ) := by
      have hjpow6 :
          (((j + 1 : ℕ) : ℝ) ^ (-6 : ℝ)) ≤
            (mixedBulkMovingStart L : ℝ) ^ (-6 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hstartReal hstartLe (by norm_num)
      have hstartPow6 :
          (mixedBulkMovingStart L : ℝ) ^ (-6 : ℝ) ≤
            (1 / (2 * log 2)) ^ (-6 : ℝ) *
              log (L : ℝ) ^ (-6 : ℝ) := by
        have hanti :=
          Real.rpow_le_rpow_of_nonpos
            hratioPos hlogStart (by norm_num : (-6 : ℝ) ≤ 0)
        calc
          _ ≤ (log (L : ℝ) / (2 * log 2)) ^ (-6 : ℝ) := hanti
          _ =
              (1 / (2 * log 2)) ^ (-6 : ℝ) *
                log (L : ℝ) ^ (-6 : ℝ) := by
            rw [show log (L : ℝ) / (2 * log 2) =
                (1 / (2 * log 2)) * log (L : ℝ) by ring,
              Real.mul_rpow hinvPos.le hlogL.le]
      calc
        _ = (((j + 1 : ℕ) : ℝ) ^ (-6 : ℝ)) := by
          simpa using (mixedCanonicalErrorProfile_eq j).symm
        _ ≤ _ := hjpow6.trans hstartPow6
    have hmain :
        mixedBoundaryMainRaw L N Kb (oddBudget L) j ≤
          (N : ℝ) *
            (mixedTransitionMainAsymptoticConstant Kb *
              mixedOddWeightBase ^ oddBudget L *
              log (L : ℝ) ^
                (-2 + mixedBulkLogAbsorption)) := by
      calc
        _ =
          (mixedBoundaryMainConstant Kb (oddBudget L) * (N : ℝ) *
            log (L : ℝ) ^
              (-mixedCanonicalRegularityExponent +
                mixedCanonicalRoughnessExponent)) *
            (log (dyadicScale j : ℝ) ^
                mixedCanonicalDyadicExponent *
              scheduledLogLoss j ^ (2 : ℝ)) := by
          unfold mixedBoundaryMainRaw
          ring
        _ ≤
          (mixedBoundaryMainConstant Kb (oddBudget L) * (N : ℝ) *
            log (L : ℝ) ^
              (-mixedCanonicalRegularityExponent +
                mixedCanonicalRoughnessExponent)) *
            (mixedBoundaryProfileConstant *
              ((1 / (2 * log 2)) ^ r *
                log (L : ℝ) ^ r)) := by
          apply mul_le_mul_of_nonneg_left hprofile
          exact mul_nonneg
            (mul_nonneg
              (mixedBoundaryMainConstant_pos _ _).le
              (Nat.cast_nonneg N))
            (Real.rpow_nonneg hlogL.le _)
        _ =
          mixedBoundaryMainConstant Kb (oddBudget L) * (N : ℝ) *
            log (L : ℝ) ^
              (-mixedCanonicalRegularityExponent +
                mixedCanonicalRoughnessExponent) *
            (mixedBoundaryProfileConstant *
              ((1 / (2 * log 2)) ^ r *
                log (L : ℝ) ^ r)) := by
          ring
        _ = _ := by
          rw [mixedBoundaryMainConstant_eq_fixed]
          unfold mixedTransitionMainAsymptoticConstant
          dsimp [r]
          have hout :
              -mixedCanonicalRegularityExponent +
                    mixedCanonicalRoughnessExponent +
                  (mixedCanonicalDyadicExponent +
                    mixedBulkLogAbsorption) =
                -2 + mixedBulkLogAbsorption := by
            unfold mixedCanonicalDyadicExponent
            calc
              _ =
                  mixedCanonicalProductExponent +
                    mixedCanonicalRoughnessExponent +
                    mixedBulkLogAbsorption := by ring
              _ = -2 + mixedBulkLogAbsorption := by
                rw [mixedCanonicalProduct_add_roughnessExponent]
          have hlogCombine :
              log (L : ℝ) ^
                    (-mixedCanonicalRegularityExponent +
                      mixedCanonicalRoughnessExponent) *
                  log (L : ℝ) ^
                    (mixedCanonicalDyadicExponent +
                      mixedBulkLogAbsorption) =
                log (L : ℝ) ^
                  (-2 + mixedBulkLogAbsorption) := by
            rw [← Real.rpow_add hlogL, hout]
          rw [show
            mixedBoundaryMainFixedConstant Kb *
                  mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
                  log (L : ℝ) ^
                    (-mixedCanonicalRegularityExponent +
                      mixedCanonicalRoughnessExponent) *
                  (mixedBoundaryProfileConstant *
                    ((1 / (2 * log 2)) ^
                        (mixedCanonicalDyadicExponent +
                          mixedBulkLogAbsorption) *
                      log (L : ℝ) ^
                        (mixedCanonicalDyadicExponent +
                          mixedBulkLogAbsorption))) =
                (mixedBoundaryMainFixedConstant Kb *
                  mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
                  mixedBoundaryProfileConstant *
                  (1 / (2 * log 2)) ^
                    (mixedCanonicalDyadicExponent +
                      mixedBulkLogAbsorption)) *
                  (log (L : ℝ) ^
                      (-mixedCanonicalRegularityExponent +
                        mixedCanonicalRoughnessExponent) *
                    log (L : ℝ) ^
                      (mixedCanonicalDyadicExponent +
                        mixedBulkLogAbsorption)) by ring,
            hlogCombine]
          ring
    have herror :
        mixedBoundaryErrorRaw L N Kb (oddBudget L) j ≤
          (N : ℝ) *
            (mixedTransitionErrorAsymptoticConstant Kb *
              mixedOddWeightBase ^ oddBudget L *
              log (L : ℝ) ^
                (-mixedCanonicalRegularityExponent - 6)) := by
      calc
        _ ≤
          mixedBoundaryErrorConstant Kb (oddBudget L) * (N : ℝ) *
            log (L : ℝ) ^ (-mixedCanonicalRegularityExponent) *
            ((1 / (2 * log 2)) ^ (-6 : ℝ) *
              log (L : ℝ) ^ (-6 : ℝ)) := by
          unfold mixedBoundaryErrorRaw
          apply mul_le_mul_of_nonneg_left herrorProfile
          exact mul_nonneg
            (mul_nonneg
              (mixedBoundaryErrorConstant_pos _ _).le
              (Nat.cast_nonneg N))
            (Real.rpow_nonneg hlogL.le _)
        _ = _ := by
          rw [mixedBoundaryErrorConstant_eq_fixed]
          unfold mixedTransitionErrorAsymptoticConstant
          have hlogCombine :
              log (L : ℝ) ^ (-mixedCanonicalRegularityExponent) *
                  log (L : ℝ) ^ (-6 : ℝ) =
                log (L : ℝ) ^
                  (-mixedCanonicalRegularityExponent - 6) := by
            rw [← Real.rpow_add hlogL]
            congr 1
          rw [show
            mixedBoundaryErrorFixedConstant Kb *
                  mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
                  log (L : ℝ) ^
                    (-mixedCanonicalRegularityExponent) *
                  ((1 / (2 * log 2)) ^ (-6 : ℝ) *
                    log (L : ℝ) ^ (-6 : ℝ)) =
                (mixedBoundaryErrorFixedConstant Kb *
                  mixedOddWeightBase ^ oddBudget L * (N : ℝ) *
                  (1 / (2 * log 2)) ^ (-6 : ℝ)) *
                  (log (L : ℝ) ^
                      (-mixedCanonicalRegularityExponent) *
                    log (L : ℝ) ^ (-6 : ℝ)) by ring,
            hlogCombine]
          ring
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    calc
      _ ≤ mixedBoundaryMainRaw L N Kb (oddBudget L) j +
          mixedBoundaryErrorRaw L N Kb (oddBudget L) j := hraw
      _ ≤
          (N : ℝ) *
              (mixedTransitionMainAsymptoticConstant Kb *
                mixedOddWeightBase ^ oddBudget L *
                log (L : ℝ) ^
                  (-2 + mixedBulkLogAbsorption)) +
            (N : ℝ) *
              (mixedTransitionErrorAsymptoticConstant Kb *
                mixedOddWeightBase ^ oddBudget L *
                log (L : ℝ) ^
                  (-mixedCanonicalRegularityExponent - 6)) :=
        add_le_add hmain herror
      _ ≤
          (N : ℝ) *
              (Erdos327.roughDensity L / (16 * D)) +
            (N : ℝ) *
              (Erdos327.roughDensity L / (16 * D)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hmainCoef hN0)
          (mul_le_mul_of_nonneg_left herrorCoef hN0)
  have hsumCard :=
    Finset.sum_le_card_nsmul s _
      ((N : ℝ) * (Erdos327.roughDensity L / (16 * D)) +
        (N : ℝ) * (Erdos327.roughDensity L / (16 * D))) hpoint
  have hcard : s.card ≤ 4 := by
    dsimp [s]
    exact card_mixedTransitionBoundaryIndexSet_le_four L M
  have htarget0 :
      0 ≤
        (N : ℝ) * (Erdos327.roughDensity L / (16 * D)) +
          (N : ℝ) * (Erdos327.roughDensity L / (16 * D)) := by
    positivity [Erdos327.roughDensity_pos hL3]
  calc
    (∑ j ∈ mixedTransitionBoundaryIndexSet L M,
        mixedCanonicalBoundaryBlock L N Kb (oddBudget L) j)
        ≤ s.card •
          ((N : ℝ) * (Erdos327.roughDensity L / (16 * D)) +
            (N : ℝ) * (Erdos327.roughDensity L / (16 * D))) :=
      hsumCard
    _ = (s.card : ℝ) *
          ((N : ℝ) * (Erdos327.roughDensity L / (16 * D)) +
            (N : ℝ) * (Erdos327.roughDensity L / (16 * D))) := by
      simp only [nsmul_eq_mul]
    _ ≤ (4 : ℝ) *
          ((N : ℝ) * (Erdos327.roughDensity L / (16 * D)) +
            (N : ℝ) * (Erdos327.roughDensity L / (16 * D))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) htarget0
    _ = (N : ℝ) * Erdos327.roughDensity L / (2 * D) := by
      field_simp [hD.ne']
      <;> ring

/-- Complete boundary estimate with an arbitrary positive density
denominator.  The transition is uniform in `N`; after fixing `L`, the
positive residual boundary is made equally small by increasing `N`. -/
theorem eventually_sum_mixedCanonicalBoundaryBlock_le
    (Kb D : ℝ) (hD : 0 < D) :
    ∀ᶠ L : ℕ in atTop, ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
      (∑ j ∈ range M,
        mixedCanonicalBoundaryBlock
          L N Kb (oddBudget L) j) ≤
        (N : ℝ) * Erdos327.roughDensity L / D := by
  filter_upwards
    [eventually_sum_mixedTransitionBoundary_le Kb D hD,
      eventually_ge_atTop 17] with L htransition hL
  have hL3 : 3 ≤ L := by omega
  have hε :
      0 < Erdos327.roughDensity L / (2 * D) :=
    div_pos (Erdos327.roughDensity_pos hL3)
      (mul_pos (by norm_num) hD)
  filter_upwards
    [eventually_sum_mixedPositiveResidualBoundary_le
      L Kb hL hε] with N hresidual
  intro M
  rw [sum_mixedCanonicalBoundaryBlock_eq_transition_add_residual hL]
  calc
    (∑ j ∈ mixedTransitionBoundaryIndexSet L M,
        mixedCanonicalBoundaryBlock L N Kb (oddBudget L) j) +
        ∑ j ∈ mixedPositiveResidualBoundaryIndexSet L N M,
          mixedCanonicalBoundaryBlock L N Kb (oddBudget L) j
        ≤
      (N : ℝ) * Erdos327.roughDensity L / (2 * D) +
        (Erdos327.roughDensity L / (2 * D)) * (N : ℝ) :=
      add_le_add (htransition N M) (hresidual M)
    _ = (N : ℝ) * Erdos327.roughDensity L / D := by
      field_simp [hD.ne']
      <;> ring

/-- The concrete allocation used in the final five-part mixed budget. -/
theorem eventually_sum_mixedCanonicalBoundaryBlock_le_roughDensity
    (Kb : ℝ) :
    ∀ᶠ L : ℕ in atTop, ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
      (∑ j ∈ range M,
        mixedCanonicalBoundaryBlock
          L N Kb (oddBudget L) j) ≤
        (N : ℝ) * Erdos327.roughDensity L / 512 := by
  simpa using
    (eventually_sum_mixedCanonicalBoundaryBlock_le
      Kb (512 : ℝ) (by norm_num))

end

end Erdos327.Analytic
