/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZActualDeltaSelectedScreenedProduct
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairActualDeltaWalkCap
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSupportPreservingBound

/-!
# Support-preserving actual-rank caps for a positive-interface pair

The replacement vectors remain in the same two adjacent physical rows.
Consequently their pair support is visible on the replacement path, while
the strict product estimate still pays the full actual-rank multiplicity.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPositiveInterfacePairSupportActualDeltaWalkCap

open FiniteDominoProductLaw
open HLOZActualDeltaSelectedProduct
open HLOZActualDeltaSelectedScreenedProduct
open HLOZPositiveInterfacePairActualDeltaCapBound
open HLOZPositiveInterfacePairActualDeltaSelected
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairSupportPreservingBound
open HLOZPositiveInterfacePairWeightedScreen
open HLOZSharpProductNumerics
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PreStoppingFiber StoppedInsertion
open TilingCappedMarginalization
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- One honest actual-rank replacement predicate retaining full pair
support. -/
def positiveInterfaceExternalPairSupportActualDeltaPredicate
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (delta : SourceActualDeltaIndex
      (PositiveInterfaceExternalPairFiber eta)) :=
  actualDeltaSelectedScreenedPredicate
    (PositiveInterfaceExternalPairFiber eta)
    (positiveInterfaceExternalPairSelected eta) cap
    (positiveInterfaceExternalPairReplacementScreen eta cap) delta

/-- One capped support-preserving replacement fibre. -/
def positiveInterfaceExternalPairSupportActualDeltaCap
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
    (positiveInterfaceExternalPairSupportActualDeltaPredicate eta cap delta))

theorem measurableSet_positiveInterfaceExternalPairSupportActualDeltaCap
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (delta : SourceActualDeltaIndex
      (PositiveInterfaceExternalPairFiber eta)) :
    MeasurableSet
      (positiveInterfaceExternalPairSupportActualDeltaCap eta cap delta) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    (isFiniteStoppingTime_truncatedLevelTime m (k + (delta : ℕ))
      (externalCoordinateCutoff eta.1.1
        ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)
    eta.1.1.tail.1
    (positiveInterfaceExternalPairSupportActualDeltaPredicate eta cap delta)

/-- The finite stopped masses satisfy the support-preserving cap
comparison. -/
theorem pairRankMultiplicity_mul_sourceStoppedGeometricMass_le_supportActualDeltaSum
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (arith : PositiveInterfaceExternalPairArithmetic eta cap) :
    let data := PositiveInterfaceExternalPairFiber eta
    (positiveInterfaceExternalPairRankMultiplicity eta : ℝ) *
        prefixedTilingStoppedAcceptedGeometricMass
          (truncatedLevelTime m k
            (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (data.coordinateCap cap) eta.1.1.tail.1
          (positiveInterfaceExternalPairSourcePredicate eta cap threshold
            bound) ≤
      (sharpRankConstant * sharpInterfaceCost threshold shell) *
        ∑ delta : SourceActualDeltaIndex data,
          prefixedTilingStoppedAcceptedGeometricMass
            (sourceActualDeltaStoppingTime data cap delta)
            eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (data.coordinateCap cap) eta.1.1.tail.1
            (positiveInterfaceExternalPairSupportActualDeltaPredicate eta cap
              delta) := by
  classical
  dsimp only
  let data := PositiveInterfaceExternalPairFiber eta
  let carrier := externalAcceptedThetaCarrier
    (withSelected data (positiveInterfaceExternalPairSelected eta)) cap
  have hsource := positiveInterfaceExternalPairSourceStoppedGeometricMass_eq
    eta hm hk hfixedPos cap threshold bound
  have hranks := sum_actualDeltaSelectedScreenedStoppedGeometricMass_eq
    data (positiveInterfaceExternalPairSelected eta) cap
    (positiveInterfaceExternalPairReplacementScreen eta cap)
    (positiveInterfaceExternalPair_actualDeltaAccepted eta hm hk hfixedPos cap)
  have hscreen :=
    pairRankMultiplicity_mul_sourceScreenMass_le_replacementScreenMass
      eta cap threshold bound arith
  have hcarrier : 0 ≤ carrier := externalAcceptedThetaCarrier_nonneg
    (withSelected data (positiveInterfaceExternalPairSelected eta)) cap
  have hranks' :
      (∑ delta : SourceActualDeltaIndex data,
        prefixedTilingStoppedAcceptedGeometricMass
          (sourceActualDeltaStoppingTime data cap delta)
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (data.coordinateCap cap) eta.1.1.tail.1
          (positiveInterfaceExternalPairSupportActualDeltaPredicate eta cap
            delta)) =
        positiveInterfaceExternalPairReplacementScreenMass eta cap *
          carrier := by
    simpa only [positiveInterfaceExternalPairSupportActualDeltaPredicate,
      positiveInterfaceExternalPairReplacementScreenMass, carrier, data]
      using hranks
  calc
    (positiveInterfaceExternalPairRankMultiplicity eta : ℝ) *
        prefixedTilingStoppedAcceptedGeometricMass
          (truncatedLevelTime m k
            (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (data.coordinateCap cap) eta.1.1.tail.1
          (positiveInterfaceExternalPairSourcePredicate eta cap threshold
            bound) =
        ((positiveInterfaceExternalPairRankMultiplicity eta : ℝ) *
          positiveInterfaceExternalPairSourceScreenMass eta cap threshold
            bound) * carrier := by rw [hsource]; ring
    _ ≤ ((sharpRankConstant * sharpInterfaceCost threshold shell) *
        positiveInterfaceExternalPairReplacementScreenMass eta cap) *
          carrier := mul_le_mul_of_nonneg_right hscreen hcarrier
    _ = (sharpRankConstant * sharpInterfaceCost threshold shell) *
        ∑ delta : SourceActualDeltaIndex data,
          prefixedTilingStoppedAcceptedGeometricMass
            (sourceActualDeltaStoppingTime data cap delta)
            eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (data.coordinateCap cap) eta.1.1.tail.1
            (positiveInterfaceExternalPairSupportActualDeltaPredicate eta cap
              delta) := by rw [hranks']; ring

/-- Path-measure version of the support-preserving cap comparison. -/
theorem rankMultiplicity_mul_simpleRandomWalk_sourceCap_le_supportActualDelta_sum
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
            (positiveInterfaceExternalPairSupportActualDeltaCap eta cap
              delta) := by
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
      (positiveInterfaceExternalPairSupportActualDeltaPredicate eta cap delta)
  have hcommon : 0 ≤ common := prefixedPrefixFiberConstant_nonneg _ _ _
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
          (positiveInterfaceExternalPairSupportActualDeltaCap eta cap delta) =
        ENNReal.ofReal (common * rankMass delta) := by
    unfold positiveInterfaceExternalPairSupportActualDeltaCap
    dsimp only
    simp only [OrientedTilingTypedExternalWordCode.start]
    exact simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
      (isFiniteStoppingTime_truncatedLevelTime m (k + (delta : ℕ))
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      _ _ _ _ _ _ _
  have hreal :=
    pairRankMultiplicity_mul_sourceStoppedGeometricMass_le_supportActualDeltaSum
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
    _ = ENNReal.ofReal (common *
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

end Erdos1165.HLOZPositiveInterfacePairSupportActualDeltaWalkCap
