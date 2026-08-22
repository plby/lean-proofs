/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairActualDeltaCapBound

set_option linter.style.haveILetI false

/-!
# Walk-measure cap bound for the physical interface pair

This converts the exact finite geometric comparison into stopped path-space
fibres, retaining the common prefix-cylinder factor on both sides.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPositiveInterfacePairActualDeltaWalkCap

open HLOZActualDeltaSelectedProduct
open HLOZPositiveInterfacePairActualDeltaCapBound
open HLOZPositiveInterfacePairActualDeltaSelected
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWeightedScreen
open HLOZSharpProductNumerics
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PreStoppingFiber StoppedInsertion
open TilingCappedMarginalization
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The capped physical source tail at its original creation rank. -/
def positiveInterfaceExternalPairSourceCap
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ) : Set WalkPath :=
  let data := PositiveInterfaceExternalPairFiber eta
  walkLift (prefixedTilingPreStoppingFiberEvent
    (truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (data.coordinateCap cap) eta.1.1.tail.1
    (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound))

/-- One capped honest actual-rank replacement fibre. -/
def positiveInterfaceExternalPairActualDeltaCap
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (delta : SourceActualDeltaIndex
      (PositiveInterfaceExternalPairFiber eta)) : Set WalkPath :=
  let data := PositiveInterfaceExternalPairFiber eta
  walkLift (prefixedTilingPreStoppingFiberEvent
    (sourceActualDeltaStoppingTime data cap delta)
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (data.coordinateCap cap) eta.1.1.tail.1
    (actualDeltaSelectedPredicate data
      (positiveInterfaceExternalPairSelected eta) cap delta))

theorem measurableSet_positiveInterfaceExternalPairSourceCap
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ) :
    MeasurableSet (positiveInterfaceExternalPairSourceCap eta cap threshold
      bound) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    (isFiniteStoppingTime_truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1
        ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)
    eta.1.1.tail.1
    (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound)

theorem measurableSet_positiveInterfaceExternalPairActualDeltaCap
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (delta : SourceActualDeltaIndex
      (PositiveInterfaceExternalPairFiber eta)) :
    MeasurableSet (positiveInterfaceExternalPairActualDeltaCap eta cap
      delta) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    (isFiniteStoppingTime_truncatedLevelTime m (k + (delta : ℕ))
      (externalCoordinateCutoff eta.1.1
        ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)
    eta.1.1.tail.1
    (actualDeltaSelectedPredicate (PositiveInterfaceExternalPairFiber eta)
      (positiveInterfaceExternalPairSelected eta) cap delta)

/-- Literal cap comparison.  The actual-rank multiplicity has already been
absorbed into the sharp interface coefficient. -/
theorem rankMultiplicity_mul_simpleRandomWalk_sourceCap_le_actualDelta_sum
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (arith : PositiveInterfaceExternalPairArithmetic eta cap) :
    ENNReal.ofReal (positiveInterfaceExternalPairRankMultiplicity eta : ℝ) *
        simpleRandomWalk
          (positiveInterfaceExternalPairSourceCap eta cap threshold bound) ≤
      ENNReal.ofReal (sharpRankConstant * sharpInterfaceCost threshold shell) *
        ∑' delta : SourceActualDeltaIndex
            (PositiveInterfaceExternalPairFiber eta),
          simpleRandomWalk
            (positiveInterfaceExternalPairActualDeltaCap eta cap delta) := by
  classical
  let data := PositiveInterfaceExternalPairFiber eta
  let common := prefixedPrefixFiberConstant eta.1.1.initial.1
    eta.1.1.retainedCount eta.1.1.tail.1
  let sourceMass := prefixedTilingStoppedAcceptedGeometricMass
    (truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (data.coordinateCap cap) eta.1.1.tail.1
    (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound)
  let rankMass := fun delta : SourceActualDeltaIndex data ↦
    prefixedTilingStoppedAcceptedGeometricMass
      (sourceActualDeltaStoppingTime data cap delta)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (data.coordinateCap cap) eta.1.1.tail.1
      (actualDeltaSelectedPredicate data
        (positiveInterfaceExternalPairSelected eta) cap delta)
  have hcommon : 0 ≤ common :=
    prefixedPrefixFiberConstant_nonneg _ _ _
  have hsource : 0 ≤ sourceMass :=
    prefixedTilingStoppedAcceptedGeometricMass_nonneg _ _ _ _ _ _ _ _
  have hrank : ∀ delta, 0 ≤ rankMass delta := by
    intro delta
    exact prefixedTilingStoppedAcceptedGeometricMass_nonneg _ _ _ _ _ _ _ _
  have hsourceMeasure : simpleRandomWalk
      (positiveInterfaceExternalPairSourceCap eta cap threshold bound) =
      ENNReal.ofReal (common * sourceMass) := by
    unfold positiveInterfaceExternalPairSourceCap
    dsimp only
    simp only [OrientedTilingTypedExternalWordCode.start]
    exact simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
      (isFiniteStoppingTime_truncatedLevelTime m k
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      _ _ _ _ _ _ _
  have hrankMeasure (delta : SourceActualDeltaIndex data) :
      simpleRandomWalk
          (positiveInterfaceExternalPairActualDeltaCap eta cap delta) =
        ENNReal.ofReal (common * rankMass delta) := by
    unfold positiveInterfaceExternalPairActualDeltaCap
    dsimp only
    simp only [OrientedTilingTypedExternalWordCode.start]
    exact simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
      (isFiniteStoppingTime_truncatedLevelTime m (k + (delta : ℕ))
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      _ _ _ _ _ _ _
  have hreal :=
    pairRankMultiplicity_mul_sourceStoppedGeometricMass_le_actualDeltaSum
      eta hm hk hfixedPos cap threshold bound arith
  change (positiveInterfaceExternalPairRankMultiplicity eta : ℝ) *
      sourceMass ≤
    (sharpRankConstant * sharpInterfaceCost threshold shell) *
      ∑ delta, rankMass delta at hreal
  rw [hsourceMeasure]
  simp_rw [hrankMeasure]
  have hN : 0 ≤ (positiveInterfaceExternalPairRankMultiplicity eta : ℝ) :=
    Nat.cast_nonneg _
  have hcost : 0 ≤ sharpRankConstant * sharpInterfaceCost threshold shell :=
    mul_nonneg sharpRankConstant_pos.le (sharpInterfaceCost_nonneg _ _)
  calc
    ENNReal.ofReal (positiveInterfaceExternalPairRankMultiplicity eta : ℝ) *
        ENNReal.ofReal (common * sourceMass) =
      ENNReal.ofReal common *
        (ENNReal.ofReal
          (positiveInterfaceExternalPairRankMultiplicity eta : ℝ) *
            ENNReal.ofReal sourceMass) := by
        rw [ENNReal.ofReal_mul hcommon]
        ac_rfl
    _ =
      ENNReal.ofReal (common *
        ((positiveInterfaceExternalPairRankMultiplicity eta : ℝ) *
          sourceMass)) := by
        rw [ENNReal.ofReal_mul hcommon, ENNReal.ofReal_mul hN]
    _ ≤ ENNReal.ofReal (common *
        ((sharpRankConstant * sharpInterfaceCost threshold shell) *
          ∑ delta, rankMass delta)) :=
      ENNReal.ofReal_mono (mul_le_mul_of_nonneg_left hreal hcommon)
    _ = ENNReal.ofReal (sharpRankConstant * sharpInterfaceCost threshold shell) *
        ∑' delta : SourceActualDeltaIndex data,
          ENNReal.ofReal (common * rankMass delta) := by
      rw [ENNReal.ofReal_mul hcommon, ENNReal.ofReal_mul hcost]
      simp_rw [ENNReal.ofReal_mul hcommon]
      rw [ENNReal.tsum_mul_left, tsum_fintype]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · ac_rfl
      · intro delta _hdelta
        exact hrank delta

end

end Erdos1165.HLOZPositiveInterfacePairActualDeltaWalkCap
