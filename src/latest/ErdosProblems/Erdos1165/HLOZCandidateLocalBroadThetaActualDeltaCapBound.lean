/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaProduct

set_option linter.style.haveILetI false

/-!
# Cap-level broad Theta bound by honest actual-rank fibres

The numerator is the accepted distinguished carrier with an away vector
which is both broad-bad and has actual endpoint increment zero.  It is thus
an honest rank-`k` stopped event.  Its normalized away mass is bounded by the
unconditional broad screen, while its carrier is exactly the finite sum of
the honest actual-increment rank pieces.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaCapBound

open FiniteDominoProductLaw HLOZFiniteProductCoordinateUnion
open HLOZCandidateLocalBroadThetaActualDeltaProduct
open HLOZCandidateLocalBroadThetaActualDeltaSelected
open HLOZCandidateLocalBroadThetaExternalProduct
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PreStoppingFiber SpatialInsertionFiber
open StoppedInsertion TilingCappedMarginalization TilingLazyDecomposition
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

/-- The broad bad screen restricted to vectors which create no new level-`m`
endpoint. -/
def broadSourceZeroDeltaBadScreen
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ)
    (ell : TruncatedTotals (data.upper cap)) : Prop :=
  sourceActualDeltaValue data cap ell = 0 ∧
    externalBroadSourceThetaAccepts data width externalThreshold cap ell = true

noncomputable def broadSourceZeroDeltaBadScreenMass
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ) : ℝ :=
  @screenMass
    (TilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (instFintypeTilingAwayDomino t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S))
    (data.upper cap)
    (broadSourceZeroDeltaBadScreen data width externalThreshold cap)
    (Classical.decPred _)

/-- Original-rank stopped predicate for the broad bad screen. -/
def broadSourceZeroDeltaBadPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ)
    (q : TilingCappedCoordinates z.retainedCount (data.coordinateCap cap)) :
    Prop :=
  let broadData := withExternalBroadSourceSelected data width externalThreshold
  broadData.selected cap
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).1) ∧
    TilingAwayTotalsScreen t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
      (data.upper cap)
      (broadSourceZeroDeltaBadScreen data width externalThreshold cap)
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).2)

theorem broadSourceZeroDeltaBadPredicate_factorization
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap width externalThreshold : ℕ)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((concreteFiber o m k supportAt supportData eta).coordinateCap cap)) :
    let data := concreteFiber o m k supportAt supportData eta
    broadSourceZeroDeltaBadPredicate data width externalThreshold cap q ∧
        PrefixedTilingStoppingAccepted
          (truncatedLevelTime m k
            (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 ↔
      (withExternalBroadSourceSelected data width externalThreshold).selected cap
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2) q).1) ∧
        TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2) (data.upper cap)
          (broadSourceZeroDeltaBadScreen data width externalThreshold cap)
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2) q).2) := by
  classical
  dsimp only
  let data := concreteFiber o m k supportAt supportData eta
  constructor
  · exact fun h ↦ h.1
  · rintro ⟨hselected, ell, hscreen, htotal⟩
    refine ⟨⟨hselected, ⟨ell, hscreen, htotal⟩⟩, ?_⟩
    have haccepted := externalBroadSourceSelected_replacement_accepted
      supportData eta hm hk hfixedPos cap width externalThreshold q hselected
        ell htotal
    dsimp only at haccepted
    rw [hscreen.1, Nat.add_zero] at haccepted
    exact haccepted

/-- Exact carrier factorization for the original-rank broad bad piece. -/
theorem broadSourceZeroDeltaBadStoppedGeometricMass_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap width externalThreshold : ℕ) :
    let data := concreteFiber o m k supportAt supportData eta
    prefixedTilingStoppedAcceptedGeometricMass
        (truncatedLevelTime m k
          (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (data.coordinateCap cap) eta.1.1.tail.1
        (broadSourceZeroDeltaBadPredicate data width externalThreshold cap) =
      broadSourceZeroDeltaBadScreenMass data width externalThreshold cap *
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
    (truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
    eta.1.1.initial.1 eta.1.1.retainedCount (data.coordinateCap cap) t
    eta.1.1.start eta.1.1.retained eta.1.1.tail.1
    (broadSourceZeroDeltaBadPredicate data width externalThreshold cap)
    (Classical.decPred _) D (broadData.selected cap) (Classical.decPred _)
    (data.upper cap)
    (broadSourceZeroDeltaBadScreen data width externalThreshold cap)
    (Classical.decPred _)
    (broadSourceZeroDeltaBadPredicate_factorization supportData eta hm hk
      hfixedPos cap width externalThreshold)
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
  unfold broadSourceZeroDeltaBadScreenMass externalAcceptedThetaCarrier
  convert h using 1
  · simp only [data, broadData, D, tilingDistinguishedAssignmentMass]
    congr 1

private theorem screenMass_mono
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (pointMass : Coordinate → ℕ → ℝ) (upper : Coordinate → ℕ)
    (large small : TruncatedTotals upper → Prop)
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (hsub : ∀ ell, small ell → large ell) :
    @screenMass Coordinate _ _ pointMass upper small (Classical.decPred _) ≤
      @screenMass Coordinate _ _ pointMass upper large
        (Classical.decPred _) := by
  unfold screenMass
  apply Finset.sum_le_sum
  intro ell _hell
  by_cases hs : small ell
  · rw [if_pos hs, if_pos (hsub ell hs)]
  · rw [if_neg hs]
    by_cases hl : large ell
    · rw [if_pos hl]
      exact normalizedJointMass_nonneg_of_pointMass_nonneg
        pointMass upper hpoint ell
    · rw [if_neg hl]

theorem broadSourceZeroDeltaBadScreenMass_le
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ) :
    broadSourceZeroDeltaBadScreenMass data width externalThreshold cap ≤
      externalBroadSourceThetaScreenMass data width externalThreshold cap := by
  classical
  unfold broadSourceZeroDeltaBadScreenMass
  unfold externalBroadSourceThetaScreenMass
  unfold screenMass
  apply Finset.sum_le_sum
  intro ell _hell
  by_cases hs : broadSourceZeroDeltaBadScreen data width externalThreshold
      cap ell
  · rw [if_pos hs, if_pos hs.2]
  · rw [if_neg hs]
    by_cases hl : externalBroadSourceThetaAccepts data width
        externalThreshold cap ell = true
    · rw [if_pos hl]
      exact @normalizedJointMass_nonneg_of_pointMass_nonneg
        (TilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (instFintypeTilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S))
        (fun a b ↦ Subtype.instDecidableEq a b)
        (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
          z.retained (supportComplementDistinguished t z.start z.retained S))
        (data.upper cap) (externalTheta_pointMass_nonneg data cap) ell
    · rw [if_neg hl]

/-- Literal stopped-product comparison at one cap. -/
theorem broadSourceZeroDeltaBadStoppedGeometricMass_le_actualDelta_sum
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
    let data := concreteFiber o m k supportAt supportData eta
    prefixedTilingStoppedAcceptedGeometricMass
        (truncatedLevelTime m k
          (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (data.coordinateCap cap) eta.1.1.tail.1
        (broadSourceZeroDeltaBadPredicate data width externalThreshold cap) ≤
      (2 * ∑ c, externalThetaCost data cap c) *
        ∑ delta : SourceActualDeltaIndex data,
          prefixedTilingStoppedAcceptedGeometricMass
            (sourceActualDeltaStoppingTime data cap delta)
            eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (data.coordinateCap cap) eta.1.1.tail.1
            (broadSourceActualDeltaPredicate data width externalThreshold cap
              delta) := by
  dsimp only
  let data := concreteFiber o m k supportAt supportData eta
  let broadData := withExternalBroadSourceSelected data width externalThreshold
  rw [broadSourceZeroDeltaBadStoppedGeometricMass_eq supportData eta hm hk
    hfixedPos cap width externalThreshold]
  rw [sum_broadSourceActualDeltaStoppedGeometricMass_eq_carrier supportData eta
    hm hk hfixedPos cap width externalThreshold]
  exact mul_le_mul_of_nonneg_right
    ((broadSourceZeroDeltaBadScreenMass_le data width externalThreshold cap).trans
      (externalBroadSourceThetaScreenMass_le data width externalThreshold cap
        arith))
    (externalAcceptedThetaCarrier_nonneg broadData cap)

end

end Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaCapBound
