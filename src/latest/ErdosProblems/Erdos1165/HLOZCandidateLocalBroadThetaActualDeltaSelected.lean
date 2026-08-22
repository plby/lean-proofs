/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaExternalProduct
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaProduct
import ErdosProblems.Erdos1165.TilingBroadSourceSlotActualDeltaAcceptedCreation

/-!
# Selected carriers for the broad one-sided Theta slot

The low-external candidate slot is not a `V₂` slot: its selected endpoint
need not dominate its mate.  The stopped carrier therefore records the
literal symmetric fact needed by the actual-rank replacement argument: at
the selected source vector, both endpoints of every exposed domino are
strictly below level `m`.

This module stops at the deterministic actual-`delta` accepted-creation
transfer.  It does not sum projected external cylinders and hence does not
make the invalid unconditional-carrier normalization.
-/

namespace Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaSelected

open FiniteDominoProductLaw
open HLOZCandidateLocalBroadThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PreStoppingSpatialLaw StoppedInsertion
open TilingCappedMarginalization
open TilingBroadSourceSlotActualDeltaAcceptedCreation
open TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber TilingVariableStoppedTracePartition
open TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A distinguished assignment carrying an accepted broad source witness.
The last field is the non-dominant replacement invariant: both physical
endpoints of every exposed source domino are below level. -/
def externalBroadSourceSelected
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ)
    (d : TilingDistinguishedCoordinates (cap := data.coordinateCap cap)
      t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S)) : Prop :=
  ∃ a ell,
    let q := (splitTilingCoordinatesEquiv t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)).symm (d, a)
    data.atomPredicate cap q ∧
      PrefixedTilingStoppingAccepted (data.stoppingTime cap) z.initial.1 t
        z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1 ∧
      externalBroadSourceThetaAccepts data width externalThreshold cap ell =
        true ∧
      (∀ b, tilingAwayTotal t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S) a b = ell b) ∧
      ∀ b : TilingAwayDomino t z.start z.retained
          (supportComplementDistinguished t z.start z.retained S),
        prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained
            (prefixedTilingInsertionTerminal z.initial t z.start z.retained
              (fun j ↦ (q j : ℕ)) z.tail) b.1.1 + (ell b : ℕ) < m ∧
        prefixedTilingFixedBoundaryLocalTime z.initial.1 z.start z.retained
            (prefixedTilingInsertionTerminal z.initial t z.start z.retained
              (fun j ↦ (q j : ℕ)) z.tail)
            (tilingPartner t b.1.1) + (ell b : ℕ) < m

/-- Strengthen only the distinguished selector of an external stopped
fibre; all clocks, atom predicates, caps, and away bounds are unchanged. -/
noncomputable def withExternalBroadSourceSelected
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold : ℕ) : Spec t o m k supportAt S z where
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
  selected := fun cap ↦
    externalBroadSourceSelected data width externalThreshold cap
  upper := data.upper
  upper_pos := data.upper_pos
  totalCap_lt_upper := data.totalCap_lt_upper
  atom_measurable := data.atom_measurable
  atom_sound := data.atom_sound
  atom_complete := data.atom_complete
  atom_monotone := data.atom_monotone

@[simp] theorem withExternalBroadSourceSelected_coordinateCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ) :
    (withExternalBroadSourceSelected data width externalThreshold).coordinateCap
        cap = data.coordinateCap cap := rfl

@[simp] theorem withExternalBroadSourceSelected_stoppingTime
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ) :
    (withExternalBroadSourceSelected data width externalThreshold).stoppingTime
        cap = data.stoppingTime cap := rfl

@[simp] theorem withExternalBroadSourceSelected_upper
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t}
    (data : Spec t o m k supportAt S z)
    (width externalThreshold cap : ℕ) (b) :
    (withExternalBroadSourceSelected data width externalThreshold).upper cap b =
      data.upper cap b := rfl

/-- An accepted broad source witness transports every unrestricted away
total to the creation clock indexed by its literal endpoint increment. -/
theorem externalBroadSourceSelected_replacement_accepted
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap width externalThreshold : ℕ)
    (qReplacement : TilingCappedCoordinates eta.1.1.retainedCount
      ((concreteFiber o m k supportAt supportData eta).coordinateCap cap))
    (hselected :
      let data := concreteFiber o m k supportAt supportData eta
      let broadData :=
        withExternalBroadSourceSelected data width externalThreshold
      broadData.selected cap
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2) qReplacement).1))
    (ellReplacement : TruncatedTotals
      ((concreteFiber o m k supportAt supportData eta).upper cap))
    (htotalReplacement : ∀ c,
      tilingAwayTotal t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2)
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2) qReplacement).2) c = ellReplacement c) :
    let data := concreteFiber o m k supportAt supportData eta
    let delta := sourceActualDeltaValue data cap ellReplacement
    PrefixedTilingStoppingAccepted
      (truncatedLevelTime m (k + delta)
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qReplacement j : ℕ)) eta.1.1.tail.1 := by
  classical
  dsimp only
  let data := concreteFiber o m k supportAt supportData eta
  let broadData := withExternalBroadSourceSelected data width externalThreshold
  change externalBroadSourceSelected data width externalThreshold cap
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2) qReplacement).1) at hselected
  rcases hselected with ⟨aSource, ellSource, hatomSource, hacceptedSource,
    _hbadSource, htotalSourceAway, hsourceBelow⟩
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  let qSource := (splitTilingCoordinatesEquiv t eta.1.1.start
      eta.1.1.retained D).symm
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
      qReplacement).1, aSource)
  have hdist :
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
        qSource).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
        qReplacement).1 := by
    simp only [qSource, Equiv.apply_symm_apply]
  have hterminal : prefixedTilingInsertionTerminal eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
        eta.1.1.tail = sourceActualDeltaTerminal eta.1.1 := by
    apply prefixedTilingInsertionTerminal_eq_of_coordinates
      eta.1.1.initial t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qSource j : ℕ)) (fun _ ↦ 0) eta.1.1.tail rfl
  have hsourceBelow' : ∀ c : TilingAwayDomino t eta.1.1.start
      eta.1.1.retained D,
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained
          (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
            eta.1.1.retained (fun j ↦ (qSource j : ℕ)) eta.1.1.tail)
          c.1.1 + (ellSource c : ℕ) < m ∧
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained
          (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
            eta.1.1.retained (fun j ↦ (qSource j : ℕ)) eta.1.1.tail)
          (tilingPartner t c.1.1) + (ellSource c : ℕ) < m := by
    intro c
    simpa only [D, qSource, Equiv.apply_symm_apply] using hsourceBelow c
  have htotalSource : ∀ c : TilingAwayDomino t eta.1.1.start
      eta.1.1.retained D,
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qSource j : ℕ)) c.1 = (ellSource c : ℕ) := by
    intro c
    calc
      _ = tilingAwayTotal t eta.1.1.start eta.1.1.retained D
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
            qSource).2) c :=
        (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
          eta.1.1.retained D qSource c).symm
      _ = _ := by
        simpa only [qSource, Equiv.apply_symm_apply] using htotalSourceAway c
  have htotalReplacement' : ∀ c : TilingAwayDomino t eta.1.1.start
      eta.1.1.retained D,
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qReplacement j : ℕ)) c.1 = (ellReplacement c : ℕ) := by
    intro c
    exact (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
      eta.1.1.retained D qReplacement c).symm.trans (htotalReplacement c)
  have hposSource : 0 < (prefixedTilingInsertionPrefixList
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qSource j : ℕ)) eta.1.1.tail.1).length := by
    unfold OrientedTilingTypedExternalWordCode.start
    rw [prefixedTilingInsertionPrefixList_length]
    omega
  have hposReplacement : 0 < (prefixedTilingInsertionPrefixList
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qReplacement j : ℕ)) eta.1.1.tail.1).length := by
    unfold OrientedTilingTypedExternalWordCode.start
    rw [prefixedTilingInsertionPrefixList_length]
    omega
  let dummy : TilingCreationFavoriteData := ((∅, ∅),
    (eta.1.1.start, eta.1.1.start))
  have hltSource : (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
      eta.1.1.tail.1).length <
        externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) (data.coordinateCap cap) qSource
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hltReplacement : (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (qReplacement j : ℕ))
      eta.1.1.tail.1).length <
        externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) (data.coordinateCap cap) qReplacement
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hresult := prefixedTilingStoppingAccepted_at_broadEndpointIncrement
    eta.1.1.initial t eta.1.1.start eta.1.1.retained eta.1.1.tail D
    (data.upper cap) k
    (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)) hm hk
    qSource qReplacement ellSource ellReplacement rfl hdist hsourceBelow'
    htotalSource htotalReplacement' hposSource hposReplacement hltSource
    hltReplacement hacceptedSource
  unfold sourceActualDeltaValue sourceActualDeltaContribution
  simpa only [D, data, hterminal] using hresult

end

end Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaSelected
