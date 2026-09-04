/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairWindowTailSingletonWalkCap
import ErdosProblems.Erdos1165.HLOZPrefixedStoppedProductUpperFactorization
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSupportActualDeltaAtom

/-!
# Observable singleton payments for a bad positive-interface pair window

The one-coordinate tail payment must retain the exact source pair history.
The selected distinguished assignment therefore carries both the permissive
singleton source witness and an exact-pair source witness.  This costs no
mass on the source event, but makes the original pair support recoverable
from a replacement path up to deletion of the one exposed base.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPositiveInterfacePairWindowTailObservableCap

open FiniteDominoProductLaw
open HLOZActualDeltaSelectedProduct
open HLOZPathEvents
open HLOZPositiveInterfacePairActualDeltaCapBound
open HLOZPositiveInterfacePairActualDeltaSelected
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairSupportActualDeltaAtom
open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfacePairWeightedScreen
open HLOZPositiveInterfacePairWindowTailProduct
open HLOZPositiveInterfacePairWindowTailSingleton
open HLOZPositiveInterfacePairWindowTailSingletonWalkCap
open HLOZPrefixedStoppedProductUpperFactorization
open HLOZProposition48Candidates
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PathInsertion PreStoppingFiber StoppedInsertion
open ScreeningInstantiation
open TilingCappedMarginalization
open TilingDistinguishedTraceInvariant TilingInsertedLocalTime
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedExternalStaticDStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A singleton distinguished assignment together with a source completion
which belongs to the original exact-pair atom. -/
def singletonPairObservableSelected
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ)
    (d : TilingDistinguishedCoordinates
      (cap := (singletonPairFiber eta b).coordinateCap cap)
      t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point))) : Prop :=
  singletonPairSelected eta b cap d ∧
    ∃ q : TilingCappedCoordinates eta.1.1.retainedCount
        ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap),
      positiveInterfaceExternalPairSourcePredicate eta cap threshold bound q ∧
        (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            ({b.1.1} : Finset Point)) q).1 = d

/-- The distinguished projection associated with the exposed singleton.
Naming this projection keeps subsequent theorem statements from repeatedly
normalizing the concrete-fibre coordinate cap. -/
noncomputable def singletonPairObservableDistinguished
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)) :
    TilingDistinguishedCoordinates
      (cap := (singletonPairFiber eta b).coordinateCap cap)
      t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point)) :=
  (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
    (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
      ({b.1.1} : Finset Point)) q).1

/-- The away projection associated with the exposed singleton. -/
noncomputable def singletonPairObservableAway
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)) :
    TilingAwayCoordinates
      (cap := (singletonPairFiber eta b).coordinateCap cap)
      t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point)) :=
  (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
    (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
      ({b.1.1} : Finset Point)) q).2

/-- The singleton away-total screen, packaged to keep its concrete-fibre
indices opaque to later theorem statements. -/
def singletonPairObservableSourceScreen
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)) : Prop :=
  TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
    (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
      ({b.1.1} : Finset Point)) ((singletonPairFiber eta b).upper cap)
    (singletonPairWindowScreen eta b cap)
    (singletonPairObservableAway eta b cap q)

/-- The exact pair source predicate factors through the observable singleton
carrier. -/
theorem positiveInterfaceExternalPairSourcePredicate_forward_observableSingleton
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap))
    (hq : positiveInterfaceExternalPairSourcePredicate eta cap threshold bound q ∧
      PrefixedTilingStoppingAccepted
        (truncatedLevelTime m k
          (externalCoordinateCutoff eta.1.1
            ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) eta.1.1.tail.1) :
    singletonPairObservableSelected eta b cap threshold bound
        (singletonPairObservableDistinguished eta b cap q) ∧
      singletonPairObservableSourceScreen eta b cap q := by
  classical
  have hforward := positiveInterfaceExternalPairSourcePredicate_forward_singleton
    eta b cap threshold bound q hq
  refine ⟨⟨hforward.1, ?_⟩, ?_⟩
  refine ⟨q, hq.1, ?_⟩
  rfl
  exact hforward.2

/-- Observable singleton selections retain the generic replacement
acceptance theorem. -/
theorem singletonPairObservable_actualDeltaAccepted
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (delta : SourceActualDeltaIndex (singletonPairFiber eta b))
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((singletonPairFiber eta b).coordinateCap cap))
    (hselected : singletonPairObservableSelected eta b cap threshold bound
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point)) q).1))
    (hscreen : TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        ({b.1.1} : Finset Point)) ((singletonPairFiber eta b).upper cap)
      (sourceActualDeltaScreen (singletonPairFiber eta b) cap delta)
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          ({b.1.1} : Finset Point)) q).2)) :
    PrefixedTilingStoppingAccepted
      (sourceActualDeltaStoppingTime (singletonPairFiber eta b) cap delta)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 :=
  singletonPair_actualDeltaAccepted eta b hm hk hfixedPos cap delta q
    hselected.1 hscreen

/-- The exact pair source mass is bounded by the bad singleton screen times
the observable distinguished carrier. -/
theorem positiveInterfaceExternalPairSourceStoppedGeometricMass_le_observableSingleton
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ) :
    let pairData := PositiveInterfaceExternalPairFiber eta
    let data := singletonPairFiber eta b
    prefixedTilingStoppedAcceptedGeometricMass
        (truncatedLevelTime m k
          (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (pairData.coordinateCap cap) eta.1.1.tail.1
        (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound) ≤
      singletonPairWindowScreenMass eta b cap *
        externalAcceptedThetaCarrier
          (withSelected data
            (fun cap ↦ singletonPairObservableSelected eta b cap
              threshold bound)) cap := by
  classical
  dsimp only
  let pairData := PositiveInterfaceExternalPairFiber eta
  let data := singletonPairFiber eta b
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained ({b.1.1} : Finset Point)
  let : Fintype (TilingAwayDomino t eta.1.1.start eta.1.1.retained D) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
  let : Fintype (TilingDistinguishedDomino t eta.1.1.start
      eta.1.1.retained D) :=
    instFintypeTilingDistinguishedDomino t eta.1.1.start eta.1.1.retained D
  have hforward : ∀ q : TilingCappedCoordinates eta.1.1.retainedCount
      (data.coordinateCap cap),
      positiveInterfaceExternalPairSourcePredicate eta cap threshold bound q ∧
          PrefixedTilingStoppingAccepted
            (truncatedLevelTime m k
              (externalCoordinateCutoff eta.1.1
                (pairData.coordinateCap cap)))
            eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
              (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 →
        singletonPairObservableSelected eta b cap threshold bound
            ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
              D q).1) ∧
          TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained D
            (data.upper cap) (singletonPairWindowScreen eta b cap)
            ((splitTilingCoordinatesEquiv t eta.1.1.start
              eta.1.1.retained D q).2) := by
    intro q hq
    have hf :=
      positiveInterfaceExternalPairSourcePredicate_forward_observableSingleton
        eta b cap threshold bound q hq
    refine ⟨hf.1, ?_⟩
    unfold singletonPairObservableSourceScreen at hf
    unfold singletonPairObservableAway at hf
    convert hf.2 using 1
    rfl
  have h :=
    @prefixedTilingStoppedAcceptedGeometricMass_le_screenMass_mul_distinguishedBase
      (truncatedLevelTime m k
        (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
      eta.1.1.initial.1 eta.1.1.retainedCount (data.coordinateCap cap) t
      eta.1.1.start eta.1.1.retained eta.1.1.tail.1
      (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound)
      (Classical.decPred _) D
      (singletonPairObservableSelected eta b cap threshold bound)
      (Classical.decPred _) (data.upper cap)
      (singletonPairWindowScreen eta b cap) (Classical.decPred _)
      hforward
      (tilingAwayPointMass_normalization_ne_zero_of_upper_pos
        t eta.1.1.start eta.1.1.retained D (data.upper cap)
          (data.upper_pos cap))
  unfold singletonPairWindowScreenMass externalAcceptedThetaCarrier
  convert h using 1
  · simp only [pairData, data, PositiveInterfaceExternalPairFiber,
      singletonPairFiber, singletonFiber, pairCoarseIndex,
      singletonSupportedIndex,
      TilingOrientedExternalAllCreationStoppedCoordinate.concreteFiber]
  · simp only [D, data, singletonPairFiber, singletonFiber,
      pairCoarseIndex, singletonSupportedIndex, withSelected,
      TilingOrientedExternalAllCreationStoppedCoordinate.concreteFiber,
      tilingDistinguishedAssignmentMass]
    unfold singletonPairWindowScreen screenMass
    apply congrArg₂ (· * ·)
    · apply Finset.sum_congr rfl
      intro ell _hell
      by_cases hs : (ell (singletonPairCoordinate eta b) : ℕ) ∈
          positiveInterfacePairWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell
      · simp only [hs, if_true]
      · simp only [hs, if_false]
    · rfl

/-- One honest actual-rank predicate over the observable singleton carrier. -/
def singletonPairObservableActualDeltaPredicate
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (delta : SourceActualDeltaIndex (singletonPairFiber eta b)) :=
  actualDeltaSelectedPredicate (singletonPairFiber eta b)
    (fun cap ↦ singletonPairObservableSelected eta b cap threshold bound)
    cap delta

/-- Observable singleton carriers still partition exactly over the three
honest endpoint increments. -/
theorem positiveInterfaceExternalPairSourceStoppedGeometricMass_le_exp_mul_observableSum
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hthick : m / 2 ≤ Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
    (him : Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) ≤ m)
    (hfit : (shell + 2) * shellWidth48 m ≤ m)
    (hwidthDeviation :
      24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (hbad : ¬ SmallWindow.windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (HLOZPositiveInterfacePhysicalWindowRatio.acceptedPhysicalDeficitFailureWindow
            m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            (shell + 1)) ≤
        positiveInterfaceRatioConstant * SmallWindow.windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (HLOZPositiveInterfacePhysicalWindowRatio.acceptedPhysicalDeficitFailureWindow
            m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            shell)) :
    let pairData := PositiveInterfaceExternalPairFiber eta
    let data := singletonPairFiber eta b
    prefixedTilingStoppedAcceptedGeometricMass
        (truncatedLevelTime m k
          (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (pairData.coordinateCap cap) eta.1.1.tail.1
        (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound) ≤
      (2 * Real.exp (-17 * balanceRateScale m)) *
        ∑ delta : SourceActualDeltaIndex data,
          prefixedTilingStoppedAcceptedGeometricMass
            (sourceActualDeltaStoppingTime data cap delta)
            eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (data.coordinateCap cap) eta.1.1.tail.1
            (singletonPairObservableActualDeltaPredicate eta b cap
              threshold bound delta) := by
  classical
  dsimp only
  let pairData := PositiveInterfaceExternalPairFiber eta
  let data := singletonPairFiber eta b
  let selected := fun cap ↦
    singletonPairObservableSelected eta b cap threshold bound
  let carrier := externalAcceptedThetaCarrier (withSelected data selected) cap
  let sourceMass := prefixedTilingStoppedAcceptedGeometricMass
    (truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (pairData.coordinateCap cap) eta.1.1.tail.1
    (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound)
  let rankMass := fun delta : SourceActualDeltaIndex data ↦
    prefixedTilingStoppedAcceptedGeometricMass
      (sourceActualDeltaStoppingTime data cap delta)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (data.coordinateCap cap) eta.1.1.tail.1
      (singletonPairObservableActualDeltaPredicate eta b cap threshold bound
        delta)
  have hsource :=
    positiveInterfaceExternalPairSourceStoppedGeometricMass_le_observableSingleton
      eta b cap threshold bound
  have hranks := sum_actualDeltaSelectedStoppedGeometricMass_eq_carrier data
    selected cap
    (singletonPairObservable_actualDeltaAccepted eta b hm hk hfixedPos cap
      threshold bound)
  have hscreen := singletonPairWindowScreenMass_le_of_not_windowRatio
    eta cap b harithmetic hwidthFour hthick him hfit hwidthDeviation
      hdeviationLevel hbad
  have hcarrier : 0 ≤ carrier :=
    externalAcceptedThetaCarrier_nonneg (withSelected data selected) cap
  change sourceMass ≤ singletonPairWindowScreenMass eta b cap * carrier at hsource
  change (∑ delta, rankMass delta) = carrier at hranks
  calc
    sourceMass ≤ singletonPairWindowScreenMass eta b cap * carrier := hsource
    _ ≤ (2 * Real.exp (-17 * balanceRateScale m)) * carrier :=
      mul_le_mul_of_nonneg_right hscreen hcarrier
    _ = (2 * Real.exp (-17 * balanceRateScale m)) *
        ∑ delta, rankMass delta := by rw [hranks]

/-- Generic observable-carrier comparison: any upper bound for the
normalized singleton window screen propagates through the three honest
endpoint-increment fibres. -/
theorem
    positiveInterfaceExternalPairSourceStoppedGeometricMass_le_mul_observableSum_of_screenMass_le
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ) (q : ℝ)
    (hscreen : singletonPairWindowScreenMass eta b cap ≤ q) :
    let pairData := PositiveInterfaceExternalPairFiber eta
    let data := singletonPairFiber eta b
    prefixedTilingStoppedAcceptedGeometricMass
        (truncatedLevelTime m k
          (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (pairData.coordinateCap cap) eta.1.1.tail.1
        (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound) ≤
      q * ∑ delta : SourceActualDeltaIndex data,
          prefixedTilingStoppedAcceptedGeometricMass
            (sourceActualDeltaStoppingTime data cap delta)
            eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (data.coordinateCap cap) eta.1.1.tail.1
            (singletonPairObservableActualDeltaPredicate eta b cap
              threshold bound delta) := by
  classical
  dsimp only
  let pairData := PositiveInterfaceExternalPairFiber eta
  let data := singletonPairFiber eta b
  let selected := fun cap ↦
    singletonPairObservableSelected eta b cap threshold bound
  let carrier := externalAcceptedThetaCarrier (withSelected data selected) cap
  let sourceMass := prefixedTilingStoppedAcceptedGeometricMass
    (truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (pairData.coordinateCap cap) eta.1.1.tail.1
    (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound)
  let rankMass := fun delta : SourceActualDeltaIndex data ↦
    prefixedTilingStoppedAcceptedGeometricMass
      (sourceActualDeltaStoppingTime data cap delta)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (data.coordinateCap cap) eta.1.1.tail.1
      (singletonPairObservableActualDeltaPredicate eta b cap threshold bound
        delta)
  have hsource :=
    positiveInterfaceExternalPairSourceStoppedGeometricMass_le_observableSingleton
      eta b cap threshold bound
  have hranks := sum_actualDeltaSelectedStoppedGeometricMass_eq_carrier data
    selected cap
    (singletonPairObservable_actualDeltaAccepted eta b hm hk hfixedPos cap
      threshold bound)
  have hcarrier : 0 ≤ carrier :=
    externalAcceptedThetaCarrier_nonneg (withSelected data selected) cap
  change sourceMass ≤ singletonPairWindowScreenMass eta b cap * carrier at hsource
  change (∑ delta, rankMass delta) = carrier at hranks
  calc
    sourceMass ≤ singletonPairWindowScreenMass eta b cap * carrier := hsource
    _ ≤ q * carrier := mul_le_mul_of_nonneg_right hscreen hcarrier
    _ = q * ∑ delta, rankMass delta := by rw [hranks]

/-- One capped observable singleton actual-rank fibre in path space. -/
def singletonPairObservableActualDeltaCap
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (delta : SourceActualDeltaIndex (singletonPairFiber eta b)) : Set WalkPath :=
  let data := singletonPairFiber eta b
  walkLift (prefixedTilingPreStoppingFiberEvent
    (sourceActualDeltaStoppingTime data cap delta)
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (data.coordinateCap cap) eta.1.1.tail.1
    (singletonPairObservableActualDeltaPredicate eta b cap threshold bound
      delta))

theorem measurableSet_singletonPairObservableActualDeltaCap
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (delta : SourceActualDeltaIndex (singletonPairFiber eta b)) :
    MeasurableSet (singletonPairObservableActualDeltaCap eta b cap
      threshold bound delta) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    (isFiniteStoppingTime_truncatedLevelTime m (k + (delta : ℕ))
      (externalCoordinateCutoff eta.1.1
        ((singletonPairFiber eta b).coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    ((singletonPairFiber eta b).coordinateCap cap) eta.1.1.tail.1
    (singletonPairObservableActualDeltaPredicate eta b cap threshold bound
      delta)

/-- Path-measure form of the observable three-rank singleton payment. -/
theorem simpleRandomWalk_sourceCap_le_exp_mul_observableSingletonSum
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hthick : m / 2 ≤ Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
    (him : Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) ≤ m)
    (hfit : (shell + 2) * shellWidth48 m ≤ m)
    (hwidthDeviation :
      24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (hbad : ¬ SmallWindow.windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (HLOZPositiveInterfacePhysicalWindowRatio.acceptedPhysicalDeficitFailureWindow
            m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            (shell + 1)) ≤
        positiveInterfaceRatioConstant * SmallWindow.windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (HLOZPositiveInterfacePhysicalWindowRatio.acceptedPhysicalDeficitFailureWindow
            m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            shell)) :
    simpleRandomWalk
        (positiveInterfaceExternalPairSourceCap eta cap threshold bound) ≤
      ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)) *
        ∑' delta : SourceActualDeltaIndex (singletonPairFiber eta b),
          simpleRandomWalk (singletonPairObservableActualDeltaCap eta b cap
            threshold bound delta) := by
  classical
  let pairData := PositiveInterfaceExternalPairFiber eta
  let data := singletonPairFiber eta b
  let common := prefixedPrefixFiberConstant eta.1.1.initial.1
    eta.1.1.retainedCount eta.1.1.tail.1
  let sourceMass := prefixedTilingStoppedAcceptedGeometricMass
    (truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (pairData.coordinateCap cap) eta.1.1.tail.1
    (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound)
  let rankMass := fun delta : SourceActualDeltaIndex data ↦
    prefixedTilingStoppedAcceptedGeometricMass
      (sourceActualDeltaStoppingTime data cap delta)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (data.coordinateCap cap) eta.1.1.tail.1
      (singletonPairObservableActualDeltaPredicate eta b cap threshold bound
        delta)
  have hcommon : 0 ≤ common := prefixedPrefixFiberConstant_nonneg _ _ _
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
        (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
      _ _ _ _ _ _ _
  have hrankMeasure (delta : SourceActualDeltaIndex data) :
      simpleRandomWalk (singletonPairObservableActualDeltaCap eta b cap
          threshold bound delta) =
        ENNReal.ofReal (common * rankMass delta) := by
    unfold singletonPairObservableActualDeltaCap
    dsimp only
    simp only [OrientedTilingTypedExternalWordCode.start]
    exact simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
      (isFiniteStoppingTime_truncatedLevelTime m (k + (delta : ℕ))
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      _ _ _ _ _ _ _
  have hreal :=
    positiveInterfaceExternalPairSourceStoppedGeometricMass_le_exp_mul_observableSum
      eta b hm hk hfixedPos cap threshold bound harithmetic hwidthFour hthick
        him hfit hwidthDeviation hdeviationLevel hbad
  let q : ℝ := 2 * Real.exp (-17 * balanceRateScale m)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  change sourceMass ≤ q * ∑ delta, rankMass delta at hreal
  rw [hsourceMeasure]
  simp_rw [hrankMeasure]
  calc
    ENNReal.ofReal (common * sourceMass) ≤
        ENNReal.ofReal (common * (q * ∑ delta, rankMass delta)) :=
      ENNReal.ofReal_mono (mul_le_mul_of_nonneg_left hreal hcommon)
    _ = ENNReal.ofReal q *
        ∑' delta : SourceActualDeltaIndex data,
          ENNReal.ofReal (common * rankMass delta) := by
      rw [ENNReal.ofReal_mul hcommon, ENNReal.ofReal_mul hq]
      simp_rw [ENNReal.ofReal_mul hcommon]
      rw [ENNReal.tsum_mul_left, tsum_fintype]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · ac_rfl
      · intro delta _hdelta
        exact hrank delta
    _ = _ := by rfl

/-- Path-measure form of the generic singleton-screen comparison. -/
theorem simpleRandomWalk_sourceCap_le_mul_observableSingletonSum_of_screenMass_le
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ) (q : ℝ)
    (hq : 0 ≤ q)
    (hscreen : singletonPairWindowScreenMass eta b cap ≤ q) :
    simpleRandomWalk
        (positiveInterfaceExternalPairSourceCap eta cap threshold bound) ≤
      ENNReal.ofReal q *
        ∑' delta : SourceActualDeltaIndex (singletonPairFiber eta b),
          simpleRandomWalk (singletonPairObservableActualDeltaCap eta b cap
            threshold bound delta) := by
  classical
  let pairData := PositiveInterfaceExternalPairFiber eta
  let data := singletonPairFiber eta b
  let common := prefixedPrefixFiberConstant eta.1.1.initial.1
    eta.1.1.retainedCount eta.1.1.tail.1
  let sourceMass := prefixedTilingStoppedAcceptedGeometricMass
    (truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (pairData.coordinateCap cap) eta.1.1.tail.1
    (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound)
  let rankMass := fun delta : SourceActualDeltaIndex data ↦
    prefixedTilingStoppedAcceptedGeometricMass
      (sourceActualDeltaStoppingTime data cap delta)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (data.coordinateCap cap) eta.1.1.tail.1
      (singletonPairObservableActualDeltaPredicate eta b cap threshold bound
        delta)
  have hcommon : 0 ≤ common := prefixedPrefixFiberConstant_nonneg _ _ _
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
        (externalCoordinateCutoff eta.1.1 (pairData.coordinateCap cap)))
      _ _ _ _ _ _ _
  have hrankMeasure (delta : SourceActualDeltaIndex data) :
      simpleRandomWalk (singletonPairObservableActualDeltaCap eta b cap
          threshold bound delta) =
        ENNReal.ofReal (common * rankMass delta) := by
    unfold singletonPairObservableActualDeltaCap
    dsimp only
    simp only [OrientedTilingTypedExternalWordCode.start]
    exact simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
      (isFiniteStoppingTime_truncatedLevelTime m (k + (delta : ℕ))
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      _ _ _ _ _ _ _
  have hreal :=
    positiveInterfaceExternalPairSourceStoppedGeometricMass_le_mul_observableSum_of_screenMass_le
      eta b hm hk hfixedPos cap threshold bound q hscreen
  change sourceMass ≤ q * ∑ delta, rankMass delta at hreal
  rw [hsourceMeasure]
  simp_rw [hrankMeasure]
  calc
    ENNReal.ofReal (common * sourceMass) ≤
        ENNReal.ofReal (common * (q * ∑ delta, rankMass delta)) :=
      ENNReal.ofReal_mono (mul_le_mul_of_nonneg_left hreal hcommon)
    _ = ENNReal.ofReal q *
        ∑' delta : SourceActualDeltaIndex data,
          ENNReal.ofReal (common * rankMass delta) := by
      rw [ENNReal.ofReal_mul hcommon, ENNReal.ofReal_mul hq]
      simp_rw [ENNReal.ofReal_mul hcommon]
      rw [ENNReal.tsum_mul_left, tsum_fintype]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · ac_rfl
      · intro delta _hdelta
        exact hrank delta
    _ = _ := by rfl

end

end Erdos1165.HLOZPositiveInterfacePairWindowTailObservableCap
