/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaCapBound
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaCapBound

/-!
# Walk-measure cap bound for the broad one-sided Theta slot

This converts the finite geometric comparison into literal path-space
stopped fibres.  The denominator is the finite sum of honest actual-rank
walk fibres, retaining the common physical-prefix cylinder factor.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaWalkCap

open HLOZCandidateLocalBroadThetaActualDeltaCapBound
open HLOZCandidateLocalBroadThetaActualDeltaProduct
open HLOZCandidateLocalBroadThetaActualDeltaSelected
open HLOZCandidateLocalBroadThetaExternalProduct
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaCapBound
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PreStoppingFiber SpatialInsertionFiber
open StoppedInsertion TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def broadSourceZeroDeltaCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (cap width externalThreshold : ℕ) : Set WalkPath :=
  let data := concreteFiber o m k supportAt supportData eta
  walkLift (prefixedTilingPreStoppingFiberEvent
    (truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (data.coordinateCap cap) eta.1.1.tail.1
    (broadSourceZeroDeltaBadPredicate data width externalThreshold cap))

def broadSourceActualDeltaCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (cap width externalThreshold : ℕ)
    (delta : SourceActualDeltaIndex
      (concreteFiber o m k supportAt supportData eta)) : Set WalkPath :=
  let data := concreteFiber o m k supportAt supportData eta
  walkLift (prefixedTilingPreStoppingFiberEvent
    (sourceActualDeltaStoppingTime data cap delta)
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (data.coordinateCap cap) eta.1.1.tail.1
    (broadSourceActualDeltaPredicate data width externalThreshold cap delta))

theorem measurableSet_broadSourceZeroDeltaCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (cap width externalThreshold : ℕ) :
    MeasurableSet (broadSourceZeroDeltaCap supportData eta cap width
      externalThreshold) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    (isFiniteStoppingTime_truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1
        ((concreteFiber o m k supportAt supportData eta).coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    ((concreteFiber o m k supportAt supportData eta).coordinateCap cap)
    eta.1.1.tail.1
    (broadSourceZeroDeltaBadPredicate
      (concreteFiber o m k supportAt supportData eta)
      width externalThreshold cap)

theorem measurableSet_broadSourceActualDeltaCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (cap width externalThreshold : ℕ)
    (delta : SourceActualDeltaIndex
      (concreteFiber o m k supportAt supportData eta)) :
    MeasurableSet (broadSourceActualDeltaCap supportData eta cap width
      externalThreshold delta) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    (isFiniteStoppingTime_truncatedLevelTime m (k + (delta : ℕ))
      (externalCoordinateCutoff eta.1.1
        ((concreteFiber o m k supportAt supportData eta).coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    ((concreteFiber o m k supportAt supportData eta).coordinateCap cap)
    eta.1.1.tail.1
    (broadSourceActualDeltaPredicate
      (concreteFiber o m k supportAt supportData eta)
      width externalThreshold cap delta)

/-- Literal walk-measure cap comparison. -/
theorem simpleRandomWalk_broadSourceZeroDeltaCap_le_actualDelta_sum
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap width externalThreshold : ℕ)
    (arith : ExternalBroadSourceThetaProductArithmetic
      (concreteFiber o m k supportAt supportData eta)
      width externalThreshold cap) :
    simpleRandomWalk
        (broadSourceZeroDeltaCap supportData eta cap width externalThreshold) ≤
      ENNReal.ofReal (2 * ∑ c, externalThetaCost
          (concreteFiber o m k supportAt supportData eta) cap c) *
        ∑' delta, simpleRandomWalk
          (broadSourceActualDeltaCap supportData eta cap width
            externalThreshold delta) := by
  let data := concreteFiber o m k supportAt supportData eta
  have hcommon : 0 ≤ prefixedPrefixFiberConstant eta.1.1.initial.1
      eta.1.1.retainedCount eta.1.1.tail.1 :=
    prefixedPrefixFiberConstant_nonneg _ _ _
  have hcost : 0 ≤ 2 * ∑ c, externalThetaCost data cap c := by
    apply mul_nonneg
    · norm_num
    · apply Finset.sum_nonneg
      intro c _hc
      unfold externalThetaCost
      unfold HLOZSourceOrientedThetaProduct.thetaCoordinateCost
      split <;> positivity
  have hsourceMeasure : simpleRandomWalk
      (broadSourceZeroDeltaCap supportData eta cap width externalThreshold) =
      ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
          eta.1.1.retainedCount eta.1.1.tail.1 *
        prefixedTilingStoppedAcceptedGeometricMass
          (truncatedLevelTime m k
            (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (data.coordinateCap cap) eta.1.1.tail.1
          (broadSourceZeroDeltaBadPredicate data width externalThreshold cap)) := by
    unfold broadSourceZeroDeltaCap
    dsimp only
    simp only [OrientedTilingTypedExternalWordCode.start]
    exact simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
      (isFiniteStoppingTime_truncatedLevelTime m k
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      _ _ _ _ _ _ _
  have hrankMeasure (delta : SourceActualDeltaIndex data) :
      simpleRandomWalk (broadSourceActualDeltaCap supportData eta cap width
          externalThreshold delta) =
        ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
            eta.1.1.retainedCount eta.1.1.tail.1 *
          prefixedTilingStoppedAcceptedGeometricMass
            (sourceActualDeltaStoppingTime data cap delta)
            eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (data.coordinateCap cap) eta.1.1.tail.1
            (broadSourceActualDeltaPredicate data width externalThreshold cap
              delta)) := by
    unfold broadSourceActualDeltaCap
    dsimp only
    simp only [OrientedTilingTypedExternalWordCode.start]
    exact simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
      (isFiniteStoppingTime_truncatedLevelTime m (k + (delta : ℕ))
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      _ _ _ _ _ _ _
  rw [hsourceMeasure]
  simp_rw [hrankMeasure]
  simp_rw [ENNReal.ofReal_mul hcommon]
  rw [ENNReal.tsum_mul_left]
  calc
    ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
          eta.1.1.retainedCount eta.1.1.tail.1) *
        ENNReal.ofReal (prefixedTilingStoppedAcceptedGeometricMass
          (truncatedLevelTime m k
            (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (data.coordinateCap cap) eta.1.1.tail.1
          (broadSourceZeroDeltaBadPredicate data width externalThreshold cap)) ≤
      ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
          eta.1.1.retainedCount eta.1.1.tail.1) *
        ENNReal.ofReal ((2 * ∑ c, externalThetaCost data cap c) *
          (∑ delta : SourceActualDeltaIndex data,
            prefixedTilingStoppedAcceptedGeometricMass
              (sourceActualDeltaStoppingTime data cap delta)
              eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
              (data.coordinateCap cap) eta.1.1.tail.1
              (broadSourceActualDeltaPredicate data width externalThreshold
                cap delta))) := by
      apply mul_le_mul_of_nonneg_left
      · exact ENNReal.ofReal_mono
          (broadSourceZeroDeltaBadStoppedGeometricMass_le_actualDelta_sum
            supportData eta hm hk hfixedPos cap width externalThreshold arith)
      · exact bot_le
    _ = ENNReal.ofReal (2 * ∑ c, externalThetaCost data cap c) *
        (∑' delta : SourceActualDeltaIndex data,
          ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
              eta.1.1.retainedCount eta.1.1.tail.1) *
            ENNReal.ofReal (prefixedTilingStoppedAcceptedGeometricMass
              (sourceActualDeltaStoppingTime data cap delta)
              eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
              (data.coordinateCap cap) eta.1.1.tail.1
              (broadSourceActualDeltaPredicate data width externalThreshold
                cap delta))) := by
      rw [ENNReal.ofReal_mul hcost]
      rw [ENNReal.tsum_mul_left, tsum_fintype]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · ac_rfl
      · intro delta _hdelta
        exact prefixedTilingStoppedAcceptedGeometricMass_nonneg
          (sourceActualDeltaStoppingTime data cap delta)
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (data.coordinateCap cap) eta.1.1.tail.1
          (broadSourceActualDeltaPredicate data width externalThreshold cap
            delta)
    _ = _ := by rw [ENNReal.tsum_mul_left]

end

end Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaWalkCap
