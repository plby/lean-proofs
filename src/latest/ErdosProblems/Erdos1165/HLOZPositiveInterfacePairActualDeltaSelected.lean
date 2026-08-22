/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZActualDeltaSelectedProduct
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSupportFiber
import ErdosProblems.Erdos1165.TilingBroadSourceSlotActualDeltaAcceptedCreation

/-!
# Accepted source carriers on an adjacent positive-interface pair

Only the two physical rows participating in one positive-interface
comparison are exposed.  The selected distinguished carrier remembers an
honest rank-`k` source vector whose two endpoints are below level `m` at
every exposed domino.  Every unrestricted replacement vector is therefore
accepted at rank `k + delta`, where `delta` is its literal endpoint count.
-/

namespace Erdos1165.HLOZPositiveInterfacePairActualDeltaSelected

open FiniteDominoProductLaw
open HLOZActualDeltaSelectedProduct
open HLOZPositiveInterfacePairSupportFiber
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open LazyDecomposition PreStoppingSpatialLaw StoppedInsertion
open TilingBroadSourceSlotActualDeltaAcceptedCreation
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingLazyDecomposition
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Prefix-correct safe totals for one exposed adjacent-pair coordinate. -/
noncomputable def positiveInterfaceExternalPairBaseWindow
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (_cap : ℕ)
    (b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2)) : Finset ℕ :=
  Finset.range (m - prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1
    eta.1.1.start eta.1.1.retained
    (positiveInterfaceExternalPairTerminal eta) b.1)

/-- All exposed source totals are in their prefix-correct safe windows. -/
def positiveInterfaceExternalPairBaseProp
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (ell : TruncatedTotals
      ((PositiveInterfaceExternalPairFiber eta).upper cap)) : Prop :=
  ∀ b, (ell b : ℕ) ∈ positiveInterfaceExternalPairBaseWindow eta cap b

/-- Distinguished assignments which possess one honest accepted source
completion with every exposed endpoint below level `m`. -/
def positiveInterfaceExternalPairSelected
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (d : TilingDistinguishedCoordinates
      (cap := (PositiveInterfaceExternalPairFiber eta).coordinateCap cap)
      t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2)) : Prop :=
  ∃ a ell,
    let data := PositiveInterfaceExternalPairFiber eta
    let q := (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2)).symm (d, a)
    data.atomPredicate cap q ∧
      PrefixedTilingStoppingAccepted (data.stoppingTime cap)
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 ∧
      positiveInterfaceExternalPairBaseProp eta cap ell ∧
      ∀ b, tilingAwayTotal t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) a b = ell b

/-- A selected safe source vector transports every unrestricted replacement
vector to its honest actual-increment creation clock. -/
theorem positiveInterfaceExternalPairSelected_replacement_accepted
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ)
    (qReplacement : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap))
    (hselected : positiveInterfaceExternalPairSelected eta cap
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) qReplacement).1))
    (ellReplacement : TruncatedTotals
      ((PositiveInterfaceExternalPairFiber eta).upper cap))
    (htotalReplacement : ∀ c,
      tilingAwayTotal t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2)
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2) qReplacement).2) c = ellReplacement c) :
    let data := PositiveInterfaceExternalPairFiber eta
    let delta := sourceActualDeltaValue data cap ellReplacement
    PrefixedTilingStoppingAccepted
      (truncatedLevelTime m (k + delta)
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qReplacement j : ℕ)) eta.1.1.tail.1 := by
  classical
  dsimp only
  let data := PositiveInterfaceExternalPairFiber eta
  change positiveInterfaceExternalPairSelected eta cap
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2) qReplacement).1) at hselected
  rcases hselected with ⟨aSource, ellSource, hatomSource, hacceptedSource,
    hbaseSource, htotalSourceAway⟩
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
        eta.1.1.tail = positiveInterfaceExternalPairTerminal eta := by
    exact positiveInterfaceExternalPairTerminal_eq_coordinates eta
      (fun j ↦ (qSource j : ℕ))
  have hsourceBelow : ∀ c : TilingAwayDomino t eta.1.1.start
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
    have hc := hbaseSource c
    unfold positiveInterfaceExternalPairBaseWindow at hc
    rw [Finset.mem_range] at hc
    rw [hterminal]
    unfold prefixedTilingFixedBoundaryDominoMax at hc
    constructor <;> omega
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
    qSource qReplacement ellSource ellReplacement rfl hdist hsourceBelow
    htotalSource htotalReplacement' hposSource hposReplacement hltSource
    hltReplacement hacceptedSource
  have hterminalSource : positiveInterfaceExternalPairTerminal eta =
      sourceActualDeltaTerminal eta.1.1 := rfl
  unfold sourceActualDeltaValue sourceActualDeltaContribution
  simpa only [D, data, hterminal, hterminalSource] using hresult

/-- The generic actual-`delta` factorization hypothesis for the pair
selector. -/
theorem positiveInterfaceExternalPair_actualDeltaAccepted
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 0 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap : ℕ)
    (delta : SourceActualDeltaIndex
      (PositiveInterfaceExternalPairFiber eta))
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap))
    (hselected : positiveInterfaceExternalPairSelected eta cap
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) q).1))
    (hscreen : TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2) ((PositiveInterfaceExternalPairFiber eta).upper cap)
      (sourceActualDeltaScreen (PositiveInterfaceExternalPairFiber eta) cap
        delta)
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) q).2)) :
    PrefixedTilingStoppingAccepted
      (sourceActualDeltaStoppingTime (PositiveInterfaceExternalPairFiber eta)
        cap delta) eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 := by
  rcases hscreen with ⟨ell, hdelta, htotal⟩
  have h := positiveInterfaceExternalPairSelected_replacement_accepted eta hm
    hk hfixedPos cap q hselected ell htotal
  dsimp only at h
  unfold sourceActualDeltaStoppingTime
  rw [hdelta] at h
  exact h

end

end Erdos1165.HLOZPositiveInterfacePairActualDeltaSelected
