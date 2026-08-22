/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairWindowTailProduct
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairActualDeltaWalkCap
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaCapBound

/-!
# Walk-cap payment for a failed positive-interface window ratio
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPositiveInterfacePairWindowTailWalkCap

open HLOZActualDeltaSelectedProduct
open HLOZPositiveInterfacePairActualDeltaCapBound
open HLOZPositiveInterfacePairActualDeltaSelected
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWeightedScreen
open HLOZPositiveInterfacePairWindowTailProduct
open HLOZPathEvents
open HLOZSourceOrientedThetaAcceptedCreationPath
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaSourceActualDeltaCapBound
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PathInsertion PreStoppingFiber StoppedInsertion
open ScreeningInstantiation
open TilingCappedMarginalization
open TilingDistinguishedTraceInvariant
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedExternalStaticDStoppedCoordinate
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A bad-ratio source cap is paid by its complete collection of honest
actual-endpoint-increment caps. -/
theorem simpleRandomWalk_sourceCap_le_exp_mul_actualDelta_sum
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (HLOZProposition48Candidates.shellWidth48 m) shell)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ HLOZProposition48Candidates.shellWidth48 m)
    (hthick : m / 2 ≤ Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
    (him : Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) ≤ m)
    (hfit : (shell + 2) * HLOZProposition48Candidates.shellWidth48 m ≤ m)
    (hwidthDeviation :
      24 * (HLOZProposition48Candidates.shellWidth48 m : ℝ) ≤
        geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (hbad : ¬ SmallWindow.windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (HLOZPositiveInterfacePhysicalWindowRatio.acceptedPhysicalDeficitFailureWindow
            m (HLOZProposition48Candidates.shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            (shell + 1)) ≤
        HLOZProposition48Candidates.positiveInterfaceRatioConstant *
          SmallWindow.windowMass
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            (HLOZPositiveInterfacePhysicalWindowRatio.acceptedPhysicalDeficitFailureWindow
              m (HLOZProposition48Candidates.shellWidth48 m)
              (Fintype.card
                (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
              shell)) :
    simpleRandomWalk
        (positiveInterfaceExternalPairSourceCap eta cap threshold bound) ≤
      ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)) *
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
  have hsourceEq := positiveInterfaceExternalPairSourceStoppedGeometricMass_eq
    eta hm hk hfixedPos cap threshold bound
  have hranks := sum_actualDeltaSelectedStoppedGeometricMass_eq_carrier data
    (positiveInterfaceExternalPairSelected eta) cap
    (positiveInterfaceExternalPair_actualDeltaAccepted eta hm hk hfixedPos cap)
  have hscreen :=
    positiveInterfaceExternalPairSourceScreenMass_le_of_not_windowRatio
      eta cap threshold bound b harithmetic hwidthFour hthick him hfit
      hwidthDeviation hdeviationLevel hbad
  let q : ℝ := 2 * Real.exp (-17 * balanceRateScale m)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hcarrier : 0 ≤ externalAcceptedThetaCarrier
      (withSelected data (positiveInterfaceExternalPairSelected eta)) cap :=
    externalAcceptedThetaCarrier_nonneg
      (withSelected data (positiveInterfaceExternalPairSelected eta)) cap
  have hreal : sourceMass ≤ q * ∑ delta, rankMass delta := by
    change sourceMass = _ at hsourceEq
    change (∑ delta, rankMass delta) = _ at hranks
    calc
      sourceMass = positiveInterfaceExternalPairSourceScreenMass eta cap
          threshold bound * externalAcceptedThetaCarrier
            (withSelected data (positiveInterfaceExternalPairSelected eta))
            cap := hsourceEq
      _ ≤ q * externalAcceptedThetaCarrier
          (withSelected data (positiveInterfaceExternalPairSelected eta))
          cap := mul_le_mul_of_nonneg_right (by simpa only [q] using hscreen)
            hcarrier
      _ = q * ∑ delta, rankMass delta := by rw [hranks]
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

/-- Every unrestricted actual-increment cap is carried by its coarse fixed
external-word creation atom at the honest raised rank. -/
theorem positiveInterfaceExternalPairActualDeltaCap_subset_externalOnlyCreationTraceAtom
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 1 < m) (hk : 0 < k) (cap : ℕ)
    (delta : SourceActualDeltaIndex
      (PositiveInterfaceExternalPairFiber eta)) :
    positiveInterfaceExternalPairActualDeltaCap eta cap delta ⊆
      orientedExternalOnlyCreationTraceAtom t o m (k + (delta : ℕ))
        eta.1.1 := by
  classical
  intro s hs
  rcases hs with ⟨hvalid, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨q, hq⟩
  let data := PositiveInterfaceExternalPairFiber eta
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  have hlt : v.length <
      externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
    let dummy : TilingCreationFavoriteData :=
      ((∅, ∅), (eta.1.1.start, eta.1.1.start))
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) (data.coordinateCap cap) q.1
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hcreationQ : ThresholdCreation sq m (k + (delta : ℕ)) v.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m (k + (delta : ℕ))
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap))
      v.length _ hlt).mp
    exact q.2.2
  have hp : pathPrefix s v.length = pathPrefix sq v.length := by
    have hp' := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
      eta.1.1.initial.1 eta.1.1.start eta.1.1.retained
      (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1 (stepsOfWalk s) hq
    change trajectory (stepsOfWalk s) = s at hvalid
    rw [hvalid] at hp'
    simpa only [sq, v] using hp'
  have hcreationS : ThresholdCreation s m (k + (delta : ℕ)) v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp (Nat.le_refl v.length)).mpr
      hcreationQ
  have htime : creationTimeNat m (k + (delta : ℕ)) s = v.length :=
    creationTimeNat_eq_of_creation hcreationS
  have heta_nonempty :
      (allRepresentedExternalCreationTraceAtom t o m k eta.1.1).Nonempty := by
    rcases eta.2 with ⟨s₀, hs₀⟩
    rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs₀
    exact ⟨s₀, hs₀.1, hs₀.2.1, hs₀.2.2.1⟩
  let etaAll : TilingOrientedAllRepresentedExternalFiber.SupportedIndex
      t o m k := ⟨eta.1.1, heta_nonempty⟩
  have hcodeQ : fixedOrientedTypedExternalWordCode t o v.length sq =
      eta.1.1 := by
    simpa only [etaAll, sq, v] using
      (fixedCode_prefixedInsertion etaAll hm hk (fun j ↦ (q.1 j : ℕ)))
  have hcodeS : fixedOrientedTypedExternalWordCode t o v.length s =
      eta.1.1 :=
    (fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp).trans
      hcodeQ
  refine ⟨hvalid, ⟨v.length, hcreationS.1⟩, ?_⟩
  rw [htime]
  exact hcodeS

end

end Erdos1165.HLOZPositiveInterfacePairWindowTailWalkCap
