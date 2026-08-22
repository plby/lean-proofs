/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaProduct

set_option linter.style.haveILetI false

/-!
# Generic accepted carriers split by the actual endpoint increment

This is the support-generic algebra behind the source-Theta actual-rank
products.  A caller supplies a predicate on the distinguished coordinates
and proves that every exact endpoint-increment away screen is accepted at
its honest rank.  The normalized away law is then partitioned into those
honest stopped pieces while the distinguished carrier is retained exactly.
-/

namespace Erdos1165.HLOZActualDeltaSelectedProduct

open FiniteDominoProductLaw
open HLOZShellZeroEndpointIncrementPartition
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open HLOZSourceSlotEndpointIncrementPartition
open LazyDecomposition TilingCappedMarginalization
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedConditionalCappedMarginalization
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Replace only the distinguished-coordinate selector of a stopped fibre. -/
noncomputable def withSelected
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (selected : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) → Prop) :
    Spec t o m k supportAt S z where
  coordinateCap := data.coordinateCap
  capStart := data.capStart
  coordinateCap_eq := data.coordinateCap_eq
  totalCap := data.totalCap
  totalCap_le_capStart := data.totalCap_le_capStart
  retainedCount_le_totalCap := data.retainedCount_le_totalCap
  stoppingTime := data.stoppingTime
  isStoppingTime := data.isStoppingTime
  atomPredicate := data.atomPredicate
  support_represented := data.support_represented
  selected := selected
  upper := data.upper
  upper_pos := data.upper_pos
  totalCap_lt_upper := data.totalCap_lt_upper
  atom_measurable := data.atom_measurable
  atom_sound := data.atom_sound
  atom_complete := data.atom_complete
  atom_monotone := data.atom_monotone

@[simp] theorem withSelected_coordinateCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (selected : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) → Prop)
    (cap : ℕ) :
    (withSelected data selected).coordinateCap cap = data.coordinateCap cap :=
  rfl

@[simp] theorem withSelected_upper
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (selected : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) → Prop)
    (cap : ℕ) (b) :
    (withSelected data selected).upper cap b = data.upper cap b := rfl

/-- One actual endpoint-increment slice with an arbitrary accepted
distinguished selector. -/
def actualDeltaSelectedPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (selected : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) → Prop)
    (cap : ℕ) (delta : SourceActualDeltaIndex data)
    (q : TilingCappedCoordinates z.retainedCount (data.coordinateCap cap)) :
    Prop :=
  selected cap
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).1) ∧
    TilingAwayTotalsScreen t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)
      (data.upper cap) (sourceActualDeltaScreen data cap delta)
      ((splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) q).2)

/-- Exact logical factorization, assuming only the caller's honest-rank
acceptance theorem for this slice. -/
theorem actualDeltaSelectedPredicate_factorization
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (selected : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) → Prop)
    (cap : ℕ) (delta : SourceActualDeltaIndex data)
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
    actualDeltaSelectedPredicate data selected cap delta q ∧
        PrefixedTilingStoppingAccepted
          (sourceActualDeltaStoppingTime data cap delta) z.initial.1 t
            z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1 ↔
      selected cap
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).1) ∧
        TilingAwayTotalsScreen t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S)
          (data.upper cap) (sourceActualDeltaScreen data cap delta)
          ((splitTilingCoordinatesEquiv t z.start z.retained
            (supportComplementDistinguished t z.start z.retained S) q).2) := by
  constructor
  · exact fun h ↦ h.1
  · rintro ⟨hselected, hscreen⟩
    exact ⟨⟨hselected, hscreen⟩, haccepted q hselected hscreen⟩

/-- One honest actual-rank stopped slice equals its normalized away mass
times the exact distinguished carrier. -/
theorem actualDeltaSelectedStoppedGeometricMass_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (selected : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) → Prop)
    (cap : ℕ) (delta : SourceActualDeltaIndex data)
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
        (actualDeltaSelectedPredicate data selected cap delta) =
      sourceActualDeltaScreenMass data cap delta *
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
      (actualDeltaSelectedPredicate data selected cap delta)
      (Classical.decPred _) D (selected cap) (Classical.decPred _)
      (data.upper cap) (sourceActualDeltaScreen data cap delta)
      (Classical.decPred _)
      (actualDeltaSelectedPredicate_factorization data selected cap delta
        haccepted)
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
  unfold sourceActualDeltaScreenMass externalAcceptedThetaCarrier
  convert h using 1
  simp only [D, tilingDistinguishedAssignmentMass]
  congr 1

/-- The exact accepted carrier is the finite sum of all honest actual-rank
slices. -/
theorem sum_actualDeltaSelectedStoppedGeometricMass_eq_carrier
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (selected : ∀ cap, TilingDistinguishedCoordinates
      (cap := data.coordinateCap cap) t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) → Prop)
    (cap : ℕ)
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
        (actualDeltaSelectedPredicate data selected cap delta)) =
      externalAcceptedThetaCarrier (withSelected data selected) cap := by
  classical
  let selectedData := withSelected data selected
  let D := supportComplementDistinguished t z.start z.retained S
  have hpiece : ∀ delta : SourceActualDeltaIndex data,
      prefixedTilingStoppedAcceptedGeometricMass
          (sourceActualDeltaStoppingTime data cap delta) z.initial.1 t z.start
          z.retained (data.coordinateCap cap) z.tail.1
          (actualDeltaSelectedPredicate data selected cap delta) =
        sourceActualDeltaScreenMass data cap delta *
          externalAcceptedThetaCarrier selectedData cap := by
    intro delta
    exact actualDeltaSelectedStoppedGeometricMass_eq data selected cap delta
      (haccepted delta)
  have hscreen :
      (∑ delta : SourceActualDeltaIndex data,
        sourceActualDeltaScreenMass data cap delta) = 1 := by
    have hpartition := @sum_screenMass_vectorAtEndpointIncrement_eq_one
      (TilingAwayDomino t z.start z.retained D)
      (instFintypeTilingAwayDomino t z.start z.retained D)
      (fun a b ↦ Subtype.instDecidableEq a b)
      (data.upper cap)
      (tilingAwayPointMass (cap := data.coordinateCap cap) t z.start
        z.retained D)
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
  calc
    (∑ delta : SourceActualDeltaIndex data,
      prefixedTilingStoppedAcceptedGeometricMass
        (sourceActualDeltaStoppingTime data cap delta) z.initial.1 t z.start
        z.retained (data.coordinateCap cap) z.tail.1
        (actualDeltaSelectedPredicate data selected cap delta)) =
        ∑ delta : SourceActualDeltaIndex data,
          sourceActualDeltaScreenMass data cap delta *
            externalAcceptedThetaCarrier selectedData cap := by
      apply Finset.sum_congr rfl
      intro delta _hdelta
      exact hpiece delta
    _ = externalAcceptedThetaCarrier selectedData cap := by
      rw [← Finset.sum_mul, hscreen, one_mul]

end

end Erdos1165.HLOZActualDeltaSelectedProduct
