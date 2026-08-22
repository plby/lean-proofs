/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairWeightedBound

set_option linter.style.haveILetI false

/-!
# Cap-level actual-rank bound for the physical interface pair

The source predicate uses the full physical adjacent-row tail and the honest
prefix-safe selected carrier.  Its normalized away mass is paid by the
rank-multiplicity-weighted product bound, while the same distinguished
carrier is partitioned exactly over the unrestricted actual endpoint ranks.
-/

namespace Erdos1165.HLOZPositiveInterfacePairActualDeltaCapBound

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZActualDeltaSelectedProduct
open HLOZPositiveInterfacePairActualDeltaSelected
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWeightedBound
open HLOZPositiveInterfacePairWeightedScreen
open HLOZShellZeroEndpointIncrementPartition
open HLOZSharpProductNumerics
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PreStoppingFiber StoppedInsertion
open TilingBroadSourceSlotActualDeltaAcceptedCreation
open TilingCappedMarginalization
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedConditionalCappedMarginalization
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The physical source screen on the selected distinguished carrier. -/
def positiveInterfaceExternalPairSourcePredicate
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)) : Prop :=
  positiveInterfaceExternalPairSelected eta cap
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) q).1) ∧
    TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2) ((PositiveInterfaceExternalPairFiber eta).upper cap)
      (positiveInterfaceExternalPairSourceScreen eta cap threshold bound)
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) q).2)

/-- A prefix-safe source total creates no new level-`m` endpoint. -/
theorem sourceActualDeltaValue_eq_zero_of_pairBaseProp
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (ell : TruncatedTotals
      ((PositiveInterfaceExternalPairFiber eta).upper cap))
    (hbase : positiveInterfaceExternalPairBaseProp eta cap ell) :
    sourceActualDeltaValue (PositiveInterfaceExternalPairFiber eta) cap ell =
      0 := by
  classical
  let data := PositiveInterfaceExternalPairFiber eta
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  unfold sourceActualDeltaValue endpointIncrementOfVector
  apply Finset.sum_eq_zero
  intro c _hc
  unfold sourceActualDeltaContribution
  have hc := hbase c
  unfold positiveInterfaceExternalPairBaseWindow at hc
  rw [Finset.mem_range] at hc
  have hterminal : sourceActualDeltaTerminal eta.1.1 =
      positiveInterfaceExternalPairTerminal eta := rfl
  rw [hterminal]
  apply prefixedShellZeroEndpointContribution_eq_zero_of_both_below
  · unfold prefixedTilingFixedBoundaryDominoMax at hc
    omega
  · unfold prefixedTilingFixedBoundaryDominoMax at hc
    omega

/-- The source predicate is honestly stopped at the original rank. -/
theorem positiveInterfaceExternalPairSourcePredicate_factorization
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)) :
    let data := PositiveInterfaceExternalPairFiber eta
    positiveInterfaceExternalPairSourcePredicate eta cap threshold bound q ∧
        PrefixedTilingStoppingAccepted
          (truncatedLevelTime m k
            (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 ↔
      positiveInterfaceExternalPairSelected eta cap
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2) q).1) ∧
        TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2) (data.upper cap)
          (positiveInterfaceExternalPairSourceScreen eta cap threshold bound)
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2) q).2) := by
  classical
  dsimp only
  let data := PositiveInterfaceExternalPairFiber eta
  constructor
  · exact fun h ↦ h.1
  · rintro ⟨hselected, ell, hscreen, htotal⟩
    refine ⟨⟨hselected, ell, hscreen, htotal⟩, ?_⟩
    have haccepted := positiveInterfaceExternalPairSelected_replacement_accepted
      eta hm hk hfixedPos cap q hselected ell htotal
    dsimp only at haccepted
    have hzero : sourceActualDeltaValue data cap ell = 0 :=
      sourceActualDeltaValue_eq_zero_of_pairBaseProp eta cap ell hscreen.1
    rw [hzero, Nat.add_zero] at haccepted
    exact haccepted

/-- Exact source-screen factorization into normalized away mass and the
selected distinguished carrier. -/
theorem positiveInterfaceExternalPairSourceStoppedGeometricMass_eq
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ) :
    let data := PositiveInterfaceExternalPairFiber eta
    prefixedTilingStoppedAcceptedGeometricMass
        (truncatedLevelTime m k
          (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (data.coordinateCap cap) eta.1.1.tail.1
        (positiveInterfaceExternalPairSourcePredicate eta cap threshold
          bound) =
      positiveInterfaceExternalPairSourceScreenMass eta cap threshold bound *
        externalAcceptedThetaCarrier
          (withSelected data
            (positiveInterfaceExternalPairSelected eta)) cap := by
  classical
  dsimp only
  let data := PositiveInterfaceExternalPairFiber eta
  let selectedData := withSelected data
    (positiveInterfaceExternalPairSelected eta)
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  letI : Fintype (TilingAwayDomino t eta.1.1.start eta.1.1.retained D) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
  letI : Fintype (TilingDistinguishedDomino t eta.1.1.start
      eta.1.1.retained D) :=
    instFintypeTilingDistinguishedDomino t eta.1.1.start eta.1.1.retained D
  have h :=
    @prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
      (truncatedLevelTime m k
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      eta.1.1.initial.1 eta.1.1.retainedCount (data.coordinateCap cap) t
      eta.1.1.start eta.1.1.retained eta.1.1.tail.1
      (positiveInterfaceExternalPairSourcePredicate eta cap threshold bound)
      (Classical.decPred _) D
      (positiveInterfaceExternalPairSelected eta cap) (Classical.decPred _)
      (data.upper cap)
      (positiveInterfaceExternalPairSourceScreen eta cap threshold bound)
      (Classical.decPred _)
      (positiveInterfaceExternalPairSourcePredicate_factorization eta hm hk
        hfixedPos cap threshold bound)
      (by
        apply ne_of_gt
        apply Finset.sum_pos'
        · intro ell _hell
          exact Finset.prod_nonneg fun c _ ↦
            tilingAwayExactTotalMass_nonneg t eta.1.1.start eta.1.1.retained D
              c (ell c)
        · let zero : TruncatedTotals (data.upper cap) :=
            fun c ↦ ⟨0, data.upper_pos cap c⟩
          refine ⟨zero, Finset.mem_univ _, ?_⟩
          unfold jointMass
          apply Finset.prod_pos
          intro c _hc
          exact tilingAwayExactTotalMass_zero_pos t eta.1.1.start
            eta.1.1.retained D c)
  unfold positiveInterfaceExternalPairSourceScreenMass
  unfold externalAcceptedThetaCarrier
  convert h using 1
  simp only [D, tilingDistinguishedAssignmentMass]
  congr 1

/-- The rank-weighted source stopped mass is paid by the full collection of
honest actual-rank replacement fibres. -/
theorem pairRankMultiplicity_mul_sourceStoppedGeometricMass_le_actualDeltaSum
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
            (actualDeltaSelectedPredicate data
              (positiveInterfaceExternalPairSelected eta) cap delta) := by
  classical
  dsimp only
  let data := PositiveInterfaceExternalPairFiber eta
  let carrier := externalAcceptedThetaCarrier
    (withSelected data (positiveInterfaceExternalPairSelected eta)) cap
  have hsource := positiveInterfaceExternalPairSourceStoppedGeometricMass_eq
    eta hm hk hfixedPos cap threshold bound
  have hranks := sum_actualDeltaSelectedStoppedGeometricMass_eq_carrier data
    (positiveInterfaceExternalPairSelected eta) cap
    (positiveInterfaceExternalPair_actualDeltaAccepted eta hm hk hfixedPos cap)
  have hcarrier : 0 ≤ carrier := externalAcceptedThetaCarrier_nonneg
    (withSelected data (positiveInterfaceExternalPairSelected eta)) cap
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
    _ ≤ (sharpRankConstant * sharpInterfaceCost threshold shell) * carrier :=
      mul_le_mul_of_nonneg_right
        (pairRankMultiplicity_mul_positiveInterfaceExternalPairSourceScreenMass_le
          eta cap threshold bound arith) hcarrier
    _ = (sharpRankConstant * sharpInterfaceCost threshold shell) *
        ∑ delta : SourceActualDeltaIndex data,
          prefixedTilingStoppedAcceptedGeometricMass
            (sourceActualDeltaStoppingTime data cap delta)
            eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (data.coordinateCap cap) eta.1.1.tail.1
            (actualDeltaSelectedPredicate data
              (positiveInterfaceExternalPairSelected eta) cap delta) := by
      rw [hranks]

end

end Erdos1165.HLOZPositiveInterfacePairActualDeltaCapBound
