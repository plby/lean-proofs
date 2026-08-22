/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaSelected

set_option linter.style.haveILetI false

/-!
# Actual-rank finite product for the broad one-sided Theta slot

The accepted distinguished carrier is retained.  The away law is partitioned
by its literal endpoint increment, and every slice is evaluated at its honest
creation rank.  Thus the final finite sum is a stopped-atom identity, not an
unconditional retained-word normalization.
-/

namespace Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaProduct

open FiniteDominoProductLaw
open HLOZCandidateLocalBroadThetaActualDeltaSelected
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open HLOZShellZeroEndpointIncrementPartition
open HLOZSourceSlotEndpointIncrementPartition
open LazyDecomposition TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedConditionalCappedMarginalization
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- One actual endpoint-increment slice with the accepted broad source
selector kept in the distinguished coordinates. -/
def broadSourceActualDeltaPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ)
    (delta : SourceActualDeltaIndex data)
    (q : TilingCappedCoordinates z.retainedCount (data.coordinateCap cap)) :
    Prop :=
  let broadData := withExternalBroadSourceSelected data width externalThreshold
  broadData.selected cap
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).1) ∧
    TilingAwayTotalsScreen t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
      (data.upper cap) (sourceActualDeltaScreen data cap delta)
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).2)

/-- Exact factorization of one honest actual-increment stopped rank piece. -/
theorem broadSourceActualDeltaPredicate_factorization
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap width externalThreshold : ℕ)
    (delta : SourceActualDeltaIndex
      (concreteFiber o m k supportAt supportData eta))
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((concreteFiber o m k supportAt supportData eta).coordinateCap cap)) :
    let data := concreteFiber o m k supportAt supportData eta
    broadSourceActualDeltaPredicate data width externalThreshold cap delta q ∧
        PrefixedTilingStoppingAccepted
          (sourceActualDeltaStoppingTime data cap delta)
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 ↔
      (withExternalBroadSourceSelected data width externalThreshold).selected cap
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2) q).1) ∧
        TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2) (data.upper cap)
          (sourceActualDeltaScreen data cap delta)
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2) q).2) := by
  classical
  dsimp only
  let data := concreteFiber o m k supportAt supportData eta
  constructor
  · exact fun h ↦ h.1
  · rintro ⟨hselected, ell, hdelta, htotal⟩
    refine ⟨⟨hselected, ⟨ell, hdelta, htotal⟩⟩, ?_⟩
    have haccepted := externalBroadSourceSelected_replacement_accepted
      supportData eta hm hk hfixedPos cap width externalThreshold q hselected
        ell htotal
    dsimp only at haccepted
    change sourceActualDeltaValue data cap ell = (delta : ℕ) at hdelta
    unfold sourceActualDeltaStoppingTime
    rw [hdelta] at haccepted
    exact haccepted

/-- The geometric mass of one honest rank slice is the normalized endpoint
increment mass times the exact accepted broad distinguished carrier. -/
theorem broadSourceActualDeltaStoppedGeometricMass_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap width externalThreshold : ℕ)
    (delta : SourceActualDeltaIndex
      (concreteFiber o m k supportAt supportData eta)) :
    let data := concreteFiber o m k supportAt supportData eta
    prefixedTilingStoppedAcceptedGeometricMass
        (sourceActualDeltaStoppingTime data cap delta)
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (data.coordinateCap cap) eta.1.1.tail.1
        (broadSourceActualDeltaPredicate data width externalThreshold cap
          delta) =
      sourceActualDeltaScreenMass data cap delta *
        externalAcceptedThetaCarrier
          (withExternalBroadSourceSelected data width externalThreshold) cap := by
  classical
  dsimp only
  let data := concreteFiber o m k supportAt supportData eta
  let broadData := withExternalBroadSourceSelected data width externalThreshold
  let D := supportComplementDistinguished t eta.1.1.start eta.1.1.retained
    eta.1.2
  letI : Fintype (TilingAwayDomino t eta.1.1.start eta.1.1.retained D) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
  letI : Fintype (TilingDistinguishedDomino t eta.1.1.start
      eta.1.1.retained D) :=
    instFintypeTilingDistinguishedDomino t eta.1.1.start eta.1.1.retained D
  have h :=
    @prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
    (sourceActualDeltaStoppingTime data cap delta) eta.1.1.initial.1
    eta.1.1.retainedCount (data.coordinateCap cap) t eta.1.1.start
    eta.1.1.retained eta.1.1.tail.1
    (broadSourceActualDeltaPredicate data width externalThreshold cap delta)
    (Classical.decPred _) D (broadData.selected cap) (Classical.decPred _)
    (data.upper cap) (sourceActualDeltaScreen data cap delta)
    (Classical.decPred _)
    (broadSourceActualDeltaPredicate_factorization supportData eta hm hk
      hfixedPos cap width externalThreshold delta)
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
  unfold sourceActualDeltaScreenMass externalAcceptedThetaCarrier
  convert h using 1
  · simp only [data, broadData, D, tilingDistinguishedAssignmentMass]
    congr 1

/-- The accepted broad carrier is exactly the finite sum of its honest
actual-rank pieces. -/
theorem sum_broadSourceActualDeltaStoppedGeometricMass_eq_carrier
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap width externalThreshold : ℕ) :
    let data := concreteFiber o m k supportAt supportData eta
    (∑ delta : SourceActualDeltaIndex data,
      prefixedTilingStoppedAcceptedGeometricMass
        (sourceActualDeltaStoppingTime data cap delta)
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (data.coordinateCap cap) eta.1.1.tail.1
        (broadSourceActualDeltaPredicate data width externalThreshold cap
          delta)) =
      externalAcceptedThetaCarrier
        (withExternalBroadSourceSelected data width externalThreshold) cap := by
  classical
  dsimp only
  let data := concreteFiber o m k supportAt supportData eta
  let broadData := withExternalBroadSourceSelected data width externalThreshold
  let D := supportComplementDistinguished t eta.1.1.start eta.1.1.retained
    eta.1.2
  have hpiece : ∀ delta : SourceActualDeltaIndex data,
      prefixedTilingStoppedAcceptedGeometricMass
          (sourceActualDeltaStoppingTime data cap delta)
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (data.coordinateCap cap) eta.1.1.tail.1
          (broadSourceActualDeltaPredicate data width externalThreshold cap
            delta) =
        sourceActualDeltaScreenMass data cap delta *
          externalAcceptedThetaCarrier broadData cap := by
    intro delta
    exact broadSourceActualDeltaStoppedGeometricMass_eq supportData eta hm hk
      hfixedPos cap width externalThreshold delta
  have hscreen : (∑ delta : SourceActualDeltaIndex data,
      sourceActualDeltaScreenMass data cap delta) = 1 := by
    have hpartition := @sum_screenMass_vectorAtEndpointIncrement_eq_one
        (TilingAwayDomino t eta.1.1.start eta.1.1.retained D)
        (instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D)
        (fun a b ↦ Subtype.instDecidableEq a b)
        (data.upper cap)
        (tilingAwayPointMass (cap := data.coordinateCap cap) t
          eta.1.1.start eta.1.1.retained D)
        (sourceActualDeltaContribution data cap)
        (sourceActualDeltaContribution_le_two data cap)
        (externalTheta_coordinate_sum_eq_one data cap)
    rw [← hpartition]
    apply Finset.sum_congr rfl
    intro delta _hdelta
    unfold sourceActualDeltaScreenMass screenMass
    apply Finset.sum_congr rfl
    intro ell _hell
    apply if_congr <;> rfl
  change (∑ delta : SourceActualDeltaIndex data,
      prefixedTilingStoppedAcceptedGeometricMass
        (sourceActualDeltaStoppingTime data cap delta)
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (data.coordinateCap cap) eta.1.1.tail.1
        (broadSourceActualDeltaPredicate data width externalThreshold cap
          delta)) = externalAcceptedThetaCarrier broadData cap
  calc
    _ = ∑ delta : SourceActualDeltaIndex data,
        sourceActualDeltaScreenMass data cap delta *
          externalAcceptedThetaCarrier broadData cap := by
      apply Finset.sum_congr rfl
      intro delta _hdelta
      exact hpiece delta
    _ = externalAcceptedThetaCarrier broadData cap := by
      rw [← Finset.sum_mul, hscreen, one_mul]

end

end Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaProduct
