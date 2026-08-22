/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZActualDeltaSelectedProduct

/-!
# Screened accepted carriers split by actual endpoint increment

This refines the generic actual-increment product by retaining an arbitrary
observable screen on the replacement totals.  Summing the honest-rank
slices gives exactly that screened away mass times the distinguished
carrier.
-/

namespace Erdos1165.HLOZActualDeltaSelectedScreenedProduct

open FiniteDominoProductLaw
open HLOZActualDeltaSelectedProduct
open HLOZShellZeroEndpointIncrementPartition
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open HLOZSourceSlotEndpointIncrementPartition
open LazyDecomposition TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedConditionalCappedMarginalization
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- One actual-increment slice intersected with a caller-supplied screen on
the away totals. -/
def actualDeltaSelectedScreenedPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (selected : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) → Prop)
    (cap : ℕ) (screen : TruncatedTotals (data.upper cap) → Prop)
    (delta : SourceActualDeltaIndex data)
    (q : TilingCappedCoordinates z.retainedCount (data.coordinateCap cap)) :
    Prop :=
  selected cap
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).1) ∧
    TilingAwayTotalsScreen t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
      (data.upper cap)
      (fun ell ↦ sourceActualDeltaScreen data cap delta ell ∧ screen ell)
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).2)

/-- Normalized mass of a screened actual-increment slice. -/
noncomputable def sourceActualDeltaScreenedMass
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ)
    (screen : TruncatedTotals (data.upper cap) → Prop)
    [DecidablePred screen] (delta : SourceActualDeltaIndex data) : ℝ :=
  let D := supportComplementDistinguished t z.start z.retained S
  @screenMass
    (TilingAwayDomino t z.start z.retained D)
    (instFintypeTilingAwayDomino t z.start z.retained D)
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start z.retained D)
    (data.upper cap)
    (fun ell ↦ sourceActualDeltaScreen data cap delta ell ∧ screen ell)
    (Classical.decPred _)

/-- Exact accepted factorization for a screened actual-increment slice. -/
theorem actualDeltaSelectedScreenedPredicate_factorization
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (selected : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) → Prop)
    (cap : ℕ) (screen : TruncatedTotals (data.upper cap) → Prop)
    (delta : SourceActualDeltaIndex data)
    (haccepted : ∀ q : TilingCappedCoordinates z.retainedCount
        (data.coordinateCap cap),
      selected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).1) →
      TilingAwayTotalsScreen t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S)
          (data.upper cap) (sourceActualDeltaScreen data cap delta)
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).2) →
        PrefixedTilingStoppingAccepted
          (sourceActualDeltaStoppingTime data cap delta) z.initial.1 t
            z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1)
    (q : TilingCappedCoordinates z.retainedCount (data.coordinateCap cap)) :
    actualDeltaSelectedScreenedPredicate data selected cap screen delta q ∧
        PrefixedTilingStoppingAccepted
          (sourceActualDeltaStoppingTime data cap delta) z.initial.1 t
            z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1 ↔
      selected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).1) ∧
        TilingAwayTotalsScreen t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S)
          (data.upper cap)
          (fun ell ↦ sourceActualDeltaScreen data cap delta ell ∧ screen ell)
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).2) := by
  constructor
  · exact fun h ↦ h.1
  · rintro ⟨hselected, ell, hscreen, htotal⟩
    refine ⟨⟨hselected, ell, hscreen, htotal⟩, ?_⟩
    exact haccepted q hselected ⟨ell, hscreen.1, htotal⟩

/-- A screened stopped slice factors into its normalized away mass and the
same distinguished carrier. -/
theorem actualDeltaSelectedScreenedStoppedGeometricMass_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (selected : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) → Prop)
    (cap : ℕ) (screen : TruncatedTotals (data.upper cap) → Prop)
    [DecidablePred screen] (delta : SourceActualDeltaIndex data)
    (haccepted : ∀ q : TilingCappedCoordinates z.retainedCount
        (data.coordinateCap cap),
      selected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).1) →
      TilingAwayTotalsScreen t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S)
          (data.upper cap) (sourceActualDeltaScreen data cap delta)
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).2) →
        PrefixedTilingStoppingAccepted
          (sourceActualDeltaStoppingTime data cap delta) z.initial.1 t
            z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1) :
    prefixedTilingStoppedAcceptedGeometricMass
        (sourceActualDeltaStoppingTime data cap delta) z.initial.1 t z.start
        z.retained (data.coordinateCap cap) z.tail.1
        (actualDeltaSelectedScreenedPredicate data selected cap screen delta) =
      sourceActualDeltaScreenedMass data cap screen delta *
        externalAcceptedThetaCarrier (withSelected data selected) cap := by
  classical
  let selectedData := withSelected data selected
  let D := supportComplementDistinguished t z.start z.retained S
  letI : Fintype (TilingAwayDomino t z.start z.retained D) :=
    instFintypeTilingAwayDomino t z.start z.retained D
  letI : Fintype (TilingDistinguishedDomino t z.start z.retained D) :=
    instFintypeTilingDistinguishedDomino t z.start z.retained D
  have h :=
    @prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
      (sourceActualDeltaStoppingTime data cap delta) z.initial.1
      z.retainedCount (data.coordinateCap cap) t z.start z.retained z.tail.1
      (actualDeltaSelectedScreenedPredicate data selected cap screen delta)
      (Classical.decPred _) D (selected cap) (Classical.decPred _)
      (data.upper cap)
      (fun ell ↦ sourceActualDeltaScreen data cap delta ell ∧ screen ell)
      (Classical.decPred _)
      (actualDeltaSelectedScreenedPredicate_factorization data selected cap
        screen delta haccepted)
      (by
        apply ne_of_gt
        apply Finset.sum_pos'
        · intro ell _hell
          exact Finset.prod_nonneg fun c _ ↦
            tilingAwayExactTotalMass_nonneg t z.start z.retained D c (ell c)
        · let zero : TruncatedTotals (data.upper cap) :=
            fun c ↦ ⟨0, data.upper_pos cap c⟩
          refine ⟨zero, Finset.mem_univ _, ?_⟩
          unfold jointMass
          apply Finset.prod_pos
          intro c _hc
          exact tilingAwayExactTotalMass_zero_pos t z.start z.retained D c)
  unfold sourceActualDeltaScreenedMass externalAcceptedThetaCarrier
  convert h using 1
  simp only [D, tilingDistinguishedAssignmentMass]
  congr 1

/-- The actual-increment slices partition any retained screen exactly. -/
theorem sum_sourceActualDeltaScreenedMass_eq_screenMass
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z) (cap : ℕ)
    (screen : TruncatedTotals (data.upper cap) → Prop)
    [DecidablePred screen] :
    (∑ delta : SourceActualDeltaIndex data,
      sourceActualDeltaScreenedMass data cap screen delta) =
      let D := supportComplementDistinguished t z.start z.retained S
      @screenMass
        (TilingAwayDomino t z.start z.retained D)
        (instFintypeTilingAwayDomino t z.start z.retained D)
        (fun a b ↦ Subtype.instDecidableEq a b)
        (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
          z.retained D) (data.upper cap) screen (Classical.decPred _) := by
  classical
  dsimp only
  let D := supportComplementDistinguished t z.start z.retained S
  letI : Fintype (TilingAwayDomino t z.start z.retained D) :=
    instFintypeTilingAwayDomino t z.start z.retained D
  unfold sourceActualDeltaScreenedMass screenMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ell _hell
  obtain ⟨delta, hdelta, hunique⟩ :=
    existsUnique_vectorAtEndpointIncrement
      (sourceActualDeltaContribution data cap)
      (sourceActualDeltaContribution_le_two data cap) ell
  rw [Finset.sum_eq_single delta]
  · have hdelta' : sourceActualDeltaScreen data cap delta ell := by
      exact hdelta
    by_cases hs : screen ell
    · rw [if_pos ⟨hdelta', hs⟩, if_pos hs]
    · rw [if_neg (fun h ↦ hs h.2), if_neg hs]
  · intro delta' _hdelta' hne
    rw [if_neg]
    intro h
    exact hne (hunique delta' (by exact h.1))
  · intro hnot
    exact (hnot (Finset.mem_univ delta)).elim

/-- Summing the honest stopped slices retains precisely the supplied away
screen rather than replacing it by the whole product law. -/
theorem sum_actualDeltaSelectedScreenedStoppedGeometricMass_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (selected : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) → Prop)
    (cap : ℕ) (screen : TruncatedTotals (data.upper cap) → Prop)
    [DecidablePred screen]
    (haccepted : ∀ (delta : SourceActualDeltaIndex data)
      (q : TilingCappedCoordinates z.retainedCount (data.coordinateCap cap)),
      selected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).1) →
      TilingAwayTotalsScreen t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S)
          (data.upper cap) (sourceActualDeltaScreen data cap delta)
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).2) →
        PrefixedTilingStoppingAccepted
          (sourceActualDeltaStoppingTime data cap delta) z.initial.1 t
            z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1) :
    (∑ delta : SourceActualDeltaIndex data,
      prefixedTilingStoppedAcceptedGeometricMass
        (sourceActualDeltaStoppingTime data cap delta) z.initial.1 t z.start
        z.retained (data.coordinateCap cap) z.tail.1
        (actualDeltaSelectedScreenedPredicate data selected cap screen delta)) =
      (let D := supportComplementDistinguished t z.start z.retained S
       @screenMass
          (TilingAwayDomino t z.start z.retained D)
          (instFintypeTilingAwayDomino t z.start z.retained D)
          (fun a b ↦ Subtype.instDecidableEq a b)
          (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
            z.retained D) (data.upper cap) screen (Classical.decPred _)) *
        externalAcceptedThetaCarrier (withSelected data selected) cap := by
  classical
  let carrier := externalAcceptedThetaCarrier (withSelected data selected) cap
  calc
    _ = ∑ delta : SourceActualDeltaIndex data,
        sourceActualDeltaScreenedMass data cap screen delta * carrier := by
      apply Finset.sum_congr rfl
      intro delta _hdelta
      exact actualDeltaSelectedScreenedStoppedGeometricMass_eq data selected
        cap screen delta (haccepted delta)
    _ = (∑ delta : SourceActualDeltaIndex data,
        sourceActualDeltaScreenedMass data cap screen delta) * carrier := by
      rw [Finset.sum_mul]
    _ = _ := by
      rw [sum_sourceActualDeltaScreenedMass_eq_screenMass data cap screen]

end

end Erdos1165.HLOZActualDeltaSelectedScreenedProduct
