/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZShellZeroDeltaIndexedCapScreen
import ErdosProblems.Erdos1165.TilingShellZeroActualDeltaPartition
import ErdosProblems.Erdos1165.TilingShellZeroExternalStaticSupportData
import ErdosProblems.Erdos1165.TilingPrefixedStoppedProductDisintegration

/-!
# Literal stopped coordinates with one fixed clock per actual increment

This is the walk-facing target for a future concrete reconstruction.  It
contains no probability comparison premise.  The analytic input is the
finite-product geometric-mass comparison, while stopped-product
disintegration supplies the walk probabilities.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingShellZeroDeltaIndexedStoppedCoordinateSpec

open HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroDeltaIndexedCapScreen
open HLOZShellZeroReplacementWindows LazyDecomposition
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroActualDeltaPartition
open TilingShellZeroExternalStaticSupportData
open TilingShellZeroExternalStaticSupportPartition
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Source cap data and a separate stopped replacement clock at every
actual endpoint increment.  `geometric_bound` is a finite-coordinate mass
statement, not an event-probability hypothesis. -/
structure LiteralShellZeroDeltaIndexedStoppedCoordinateSpec
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) where
  coordinateCap : ℕ → ℕ
  sourceStoppingTime : ℕ → StepPath → ℕ
  replacementStoppingTime :
    ReplacementEndpointIncrement total
      (centralReplacementUpperCount shellZeroLocalRatioConstant total) →
      ℕ → StepPath → ℕ
  sourceIsStoppingTime : ∀ cap, IsFiniteStoppingTime (sourceStoppingTime cap)
  replacementIsStoppingTime : ∀ delta cap,
    IsFiniteStoppingTime (replacementStoppingTime delta cap)
  sourcePredicate : ∀ cap,
    TilingCappedCoordinates z.retainedCount (coordinateCap cap) → Prop
  replacementPredicate : ∀ delta cap,
    TilingCappedCoordinates z.retainedCount (coordinateCap cap) → Prop
  geometric_bound : ∀ cap,
    ENNReal.ofReal (prefixedTilingStoppedAcceptedGeometricMass
        (sourceStoppingTime cap) z.initial.1 t z.start z.retained
          (coordinateCap cap) z.tail.1 (sourcePredicate cap)) ≤
      ENNReal.ofReal
          (centralReplacementRatio shellZeroLocalRatioConstant total) *
        ∑' delta, ENNReal.ofReal
          (prefixedTilingStoppedAcceptedGeometricMass
            (replacementStoppingTime delta cap) z.initial.1 t z.start
              z.retained (coordinateCap cap) z.tail.1
                (replacementPredicate delta cap))
  source_sound : ∀ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (sourceStoppingTime cap)
      z.initial.1 t z.start z.retained (coordinateCap cap) z.tail.1
        (sourcePredicate cap)) ⊆
      orientedValidShellZeroExactSourceStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total z S
  source_complete :
    orientedValidShellZeroExactSourceStaticSupportAtom t o m k
        (shellWidth48 m) low externalLow externalHigh total z S ⊆
      ⋃ cap, walkLift (prefixedTilingPreStoppingFiberEvent
        (sourceStoppingTime cap) z.initial.1 t z.start z.retained
        (coordinateCap cap) z.tail.1 (sourcePredicate cap))
  replacement_sound : ∀ delta cap,
    walkLift (prefixedTilingPreStoppingFiberEvent
      (replacementStoppingTime delta cap) z.initial.1 t z.start z.retained
      (coordinateCap cap) z.tail.1 (replacementPredicate delta cap)) ⊆
      orientedValidShellZeroActualDeltaReplacementStaticSupportAtom
        t o m k (shellWidth48 m) low externalLow externalHigh total
        (centralReplacementUpperCount shellZeroLocalRatioConstant total)
        delta z S
  source_monotone : Monotone fun cap ↦
    walkLift (prefixedTilingPreStoppingFiberEvent (sourceStoppingTime cap)
      z.initial.1 t z.start z.retained (coordinateCap cap) z.tail.1
        (sourcePredicate cap))

/-- Stopped-product disintegration turns the geometric finite-sum bound
into the delta-indexed cap family used by the global measure theorem. -/
noncomputable def literalShellZeroDeltaIndexedCapFamily
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : SupportedSourceStaticSupportIndex t o m k
        (shellWidth48 m) low externalLow externalHigh total,
      LiteralShellZeroDeltaIndexedStoppedCoordinateSpec t o m k low
        externalLow externalHigh total eta.1.1 eta.1.2) :
    DeltaIndexedMonotoneCapStoppedFiberFamily
      (SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
        externalLow externalHigh total)
      (ReplacementEndpointIncrement total
        (centralReplacementUpperCount shellZeroLocalRatioConstant total))
      (centralReplacementRatio shellZeroLocalRatioConstant total) where
  sourceCap := fun cap eta ↦
    walkLift (prefixedTilingPreStoppingFiberEvent
      ((data eta).sourceStoppingTime cap) eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained ((data eta).coordinateCap cap)
        eta.1.1.tail.1 ((data eta).sourcePredicate cap))
  replacementCap := fun cap delta eta ↦
    walkLift (prefixedTilingPreStoppingFiberEvent
      ((data eta).replacementStoppingTime delta cap) eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained ((data eta).coordinateCap cap)
        eta.1.1.tail.1 ((data eta).replacementPredicate delta cap))
  measurable_replacementCap := fun cap delta eta ↦ by
    apply measurableSet_walkLift
    exact measurableSet_prefixedTilingPreStoppingFiberEvent
      ((data eta).replacementIsStoppingTime delta cap)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      ((data eta).coordinateCap cap) eta.1.1.tail.1
      ((data eta).replacementPredicate delta cap)
  cap_le := fun cap eta ↦ by
    simp only [OrientedTilingTypedExternalWordCode.start]
    rw [simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
        ((data eta).sourceIsStoppingTime cap)]
    simp_rw [simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
      ((data eta).replacementIsStoppingTime _ cap)]
    have hcommon : 0 ≤ prefixedPrefixFiberConstant eta.1.1.initial.1
        eta.1.1.retainedCount eta.1.1.tail.1 :=
      prefixedPrefixFiberConstant_nonneg _ _ _
    simp_rw [ENNReal.ofReal_mul hcommon]
    rw [ENNReal.tsum_mul_left]
    calc
      ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
          eta.1.1.retainedCount eta.1.1.tail.1) *
          ENNReal.ofReal (prefixedTilingStoppedAcceptedGeometricMass
            ((data eta).sourceStoppingTime cap) eta.1.1.initial.1 t
            eta.1.1.start eta.1.1.retained ((data eta).coordinateCap cap)
            eta.1.1.tail.1 ((data eta).sourcePredicate cap)) ≤
        ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
          eta.1.1.retainedCount eta.1.1.tail.1) *
          (ENNReal.ofReal
              (centralReplacementRatio shellZeroLocalRatioConstant total) *
            ∑' delta, ENNReal.ofReal
              (prefixedTilingStoppedAcceptedGeometricMass
                ((data eta).replacementStoppingTime delta cap)
                eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
                ((data eta).coordinateCap cap) eta.1.1.tail.1
                ((data eta).replacementPredicate delta cap))) :=
        mul_le_mul_of_nonneg_left ((data eta).geometric_bound cap) bot_le
      _ = ENNReal.ofReal
            (centralReplacementRatio shellZeroLocalRatioConstant total) *
          (ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
              eta.1.1.retainedCount eta.1.1.tail.1) *
            ∑' delta, ENNReal.ofReal
              (prefixedTilingStoppedAcceptedGeometricMass
                ((data eta).replacementStoppingTime delta cap)
                eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
                ((data eta).coordinateCap cap) eta.1.1.tail.1
                ((data eta).replacementPredicate delta cap))) := by
        ac_rfl
  source_monotone := fun eta ↦ (data eta).source_monotone

end

end Erdos1165.TilingShellZeroDeltaIndexedStoppedCoordinateSpec
