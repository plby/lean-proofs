/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadSourceStrongRoute
import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaActualDeltaHistoryCap
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceSlotCapCover
import ErdosProblems.Erdos1165.TilingOrientedPrefixedBoundarySourceLocalTime

/-!
# Singleton reconstruction for the strong broad source slot

A physical singleton base in the broad source strip, with both domino
endpoints below level and low oriented external count, reconstructs the
literal zero-increment bad predicate used by the actual-rank product.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZCandidateLocalBroadThetaStrongSingletonAccepted

open FiniteDominoProductLaw
open HLOZCandidateLocalBroadSourceStrongRoute
open HLOZCandidateLocalBroadThetaActualDeltaCapBound
open HLOZCandidateLocalBroadThetaActualDeltaSelected
open HLOZCandidateLocalBroadThetaExternalProduct
open HLOZCandidateLocalBroadThetaProduct
open HLOZPathEvents HLOZShellZeroReplacementWindows
open HLOZShellZeroEndpointIncrementPartition
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open HLOZSourceOrientedThetaSourceSlotAcceptedPath
open HLOZSourceOrientedThetaSourceSlotCapCover
open LazyDecomposition PathInsertion PreStoppingFiber SpatialInsertionFiber
open PreStoppingSpatialLaw StoppedInsertion
open TilingBroadSourceSlotActualDeltaAcceptedCreation
open TilingCappedMarginalization TilingLazyDecomposition
open TilingInsertedLocalTime
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedPrefixedBoundarySourceLocalTime
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroEndpointIncrementScreen
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem away_point_eq_of_singleton
    {t : DominoTiling} {i : ℕ} {x : Point}
    {r : TilingRetainedWord t x i} {S : Finset Point} {b : Point}
    (hS : S = {b})
    (c : TilingAwayDomino t x r
      (supportComplementDistinguished t x r S)) : c.1.1 = b := by
  have hc := (away_mem_support_iff t x r S c.1).1 c.2
  have hc' : c.1.1 ∈ ({b} : Finset Point) := by
    simpa only [hS] using hc
  exact Finset.mem_singleton.mp hc'

/-- Reconstructed singleton source data give the exact zero-increment broad
bad predicate. -/
theorem broadSourceZeroDeltaBadPredicate_of_singleton_strong
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 1 < m) (hk : 0 < k)
    (cap width externalThreshold : ℕ)
    (b : Point) (hS : eta.1.2 = {b})
    (hb : b ∈ tilingExternalDominoBases t eta.1.1.start eta.1.1.retained)
    (hcompat : OrientationCompatible o b)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      ((concreteFiber o m k supportAt supportData eta).coordinateCap cap))
    (hatom : (concreteFiber o m k supportAt supportData eta).atomPredicate
      cap q)
    (haccepted : PrefixedTilingStoppingAccepted
      ((concreteFiber o m k supportAt supportData eta).stoppingTime cap)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.tail.1)
    (hsource :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
      let sq := trajectory (extendPrefix (directionVectorOfList v))
      localTime sq v.length b ∈ shellZeroSourceTotalWindow m width)
    (hpartner :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
      let sq := trajectory (extendPrefix (directionVectorOfList v))
      localTime sq v.length (tilingPartner t b) < m)
    (hexternal : Fintype.card (TilingCoordinatesAt t eta.1.1.start
      eta.1.1.retained ⟨b, hb⟩) < externalThreshold) :
    broadSourceZeroDeltaBadPredicate
      (concreteFiber o m k supportAt supportData eta)
      width externalThreshold cap q := by
  classical
  let data := concreteFiber o m k supportAt supportData eta
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  let bext : TilingExternalDomino t eta.1.1.start eta.1.1.retained := ⟨b, hb⟩
  have hbS : b ∈ eta.1.2 := by rw [hS]; simp
  have hbaway : bext.1 ∉ D :=
    (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 bext).2 hbS
  let ba : TilingAwayDomino t eta.1.1.start eta.1.1.retained D :=
    ⟨bext, hbaway⟩
  let a := (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).2
  let terminal := prefixedTilingInsertionTerminal eta.1.1.initial t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  have hpath : finitePathList (pathPrefix sq v.length) =
      prefixedTilingPrefixPointPath eta.1.1.initial.1 eta.1.1.start
        (tilingInsertGapVector t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ))) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail rfl
  have hbaseLocal : localTime sq v.length b =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained terminal b +
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) bext := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) terminal bext b]
    exact tilingExternalDomino_isBase t eta.1.1.start eta.1.1.retained bext
  have hpartnerLocal : localTime sq v.length (tilingPartner t b) =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained terminal (tilingPartner t b) +
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) bext := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) terminal bext (tilingPartner t b)]
    simp only [tilingBase_partner]
    exact tilingExternalDomino_isBase t eta.1.1.start eta.1.1.retained bext
  have hboundary : prefixedTilingFixedBoundaryLocalTime
      eta.1.1.initial.1 eta.1.1.start eta.1.1.retained terminal b =
        Fintype.card (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained
          bext) := by
    exact prefixedBoundaryLocalTime_eq_coordinateCard_external eta hm hk
      (fun j ↦ (q j : ℕ)) bext hcompat
  have hbaseBelow : prefixedTilingFixedBoundaryLocalTime
      eta.1.1.initial.1 eta.1.1.start eta.1.1.retained terminal b +
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) bext < m := by
    rw [← hbaseLocal]
    exact (mem_shellZeroSourceTotalWindow.mp hsource).2
  have hpartnerBelow : prefixedTilingFixedBoundaryLocalTime
      eta.1.1.initial.1 eta.1.1.start eta.1.1.retained terminal
          (tilingPartner t b) +
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) bext < m := by
    rw [← hpartnerLocal]
    exact hpartner
  have htotalBa : tilingAwayTotal t eta.1.1.start eta.1.1.retained D a ba =
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) bext := by
    exact tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
      eta.1.1.retained D q ba
  have htotalLt (c : TilingAwayDomino t eta.1.1.start
      eta.1.1.retained D) : tilingAwayTotal t eta.1.1.start
      eta.1.1.retained D a c < data.upper cap c := by
    have hcPoint := away_point_eq_of_singleton hS c
    have hcExt : c.1 = bext := by
      apply Subtype.ext
      exact hcPoint
    have hcBa : c = ba := by
      apply Subtype.ext
      exact hcExt
    subst c
    rw [htotalBa]
    dsimp only [data, concreteFiber]
    omega
  let ell : TruncatedTotals (data.upper cap) := fun c ↦
    ⟨tilingAwayTotal t eta.1.1.start eta.1.1.retained D a c, htotalLt c⟩
  have hbad : externalBroadSourceThetaAccepts data width externalThreshold
      cap ell = true := by
    rw [externalBroadSourceThetaAccepts, decide_eq_true_eq]
    refine ⟨ba, ?_⟩
    rw [broadSourceThetaCoordinateBad]
    have hell : (ell ba : ℕ) = tilingDominoTotal t eta.1.1.start
        eta.1.1.retained (fun j ↦ (q j : ℕ)) bext := htotalBa
    change Fintype.card (TilingCoordinatesAt t eta.1.1.start
      eta.1.1.retained bext) < externalThreshold at hexternal
    refine ⟨?_, hexternal⟩
    rw [hell]
    change tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) bext ∈
      shellZeroSourceFailureWindow m width
        (Fintype.card (TilingCoordinatesAt t eta.1.1.start
          eta.1.1.retained bext))
    have hsourceTotal : Fintype.card (TilingCoordinatesAt t eta.1.1.start
        eta.1.1.retained bext) +
          tilingDominoTotal t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) bext ∈
        shellZeroSourceTotalWindow m width := by
      rw [← hboundary, ← hbaseLocal]
      exact hsource
    simp only [mem_shellZeroSourceFailureWindow,
      mem_shellZeroSourceTotalWindow] at hsourceTotal ⊢
    omega
  have htotal : ∀ c, tilingAwayTotal t eta.1.1.start eta.1.1.retained
      D a c = ell c := fun _ ↦ rfl
  have hbelow : ∀ c : TilingAwayDomino t eta.1.1.start
      eta.1.1.retained D,
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained terminal c.1.1 + (ell c : ℕ) < m ∧
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained terminal (tilingPartner t c.1.1) +
            (ell c : ℕ) < m := by
    intro c
    have hcPoint := away_point_eq_of_singleton hS c
    have hcExt : c.1 = bext := by
      apply Subtype.ext
      exact hcPoint
    have hcBa : c = ba := by
      apply Subtype.ext
      exact hcExt
    subst c
    change _ + tilingAwayTotal t eta.1.1.start eta.1.1.retained D a ba < m ∧
      _ + tilingAwayTotal t eta.1.1.start eta.1.1.retained D a ba < m
    rw [htotalBa]
    exact ⟨hbaseBelow, hpartnerBelow⟩
  have hselected : externalBroadSourceSelected data width externalThreshold cap
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).1) := by
    change ∃ a' ell',
      let q' := (splitTilingCoordinatesEquiv t eta.1.1.start
        eta.1.1.retained D).symm
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).1,
            a')
      data.atomPredicate cap q' ∧
        PrefixedTilingStoppingAccepted (data.stoppingTime cap)
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q' j : ℕ)) eta.1.1.tail.1 ∧
        externalBroadSourceThetaAccepts data width externalThreshold cap ell' =
          true ∧
        (∀ c, tilingAwayTotal t eta.1.1.start eta.1.1.retained D a' c =
          ell' c) ∧ _
    refine ⟨a, ell, ?_⟩
    dsimp only
    have hq' : (splitTilingCoordinatesEquiv t eta.1.1.start
        eta.1.1.retained D).symm
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).1,
            a) = q := by
      change (splitTilingCoordinatesEquiv t eta.1.1.start
        eta.1.1.retained D).symm
          (splitTilingCoordinatesEquiv t eta.1.1.start
            eta.1.1.retained D q) = q
      exact Equiv.symm_apply_apply _ q
    rw [hq']
    exact ⟨hatom, haccepted, hbad, htotal, hbelow⟩
  have hterminal : terminal = sourceActualDeltaTerminal eta.1.1 := by
    apply prefixedTilingInsertionTerminal_eq_of_coordinates
      eta.1.1.initial t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q j : ℕ)) (fun _ ↦ 0) eta.1.1.tail rfl
  have hzero : sourceActualDeltaValue data cap ell = 0 := by
    unfold sourceActualDeltaValue endpointIncrementOfVector
    apply Finset.sum_eq_zero
    intro c _hc
    unfold sourceActualDeltaContribution
    rw [← hterminal]
    exact prefixedShellZeroEndpointContribution_eq_zero_of_both_below
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      terminal D (data.upper cap) c (ell c) (hbelow c).1 (hbelow c).2
  refine ⟨hselected, ell, ⟨hzero, hbad⟩, htotal⟩

end

end Erdos1165.HLOZCandidateLocalBroadThetaStrongSingletonAccepted
