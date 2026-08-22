/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroStaticReplacementCardRecovery
import ErdosProblems.Erdos1165.TilingShellZeroDeltaAcceptedCreationEndpoint

/-!
# Honest actual-delta replacement atom recovery

This module bundles the prefix-correct deterministic replacement lemmas.
Starting from one literal source reconstruction and one fixed-increment
replacement vector with the same static distinguished projection, it proves
membership in the actual-rank replacement atom.  There is no probability or
fixed guessed-rank premise.
-/

namespace Erdos1165.TilingShellZeroActualDeltaReplacementAtomRecovery

open Set
open FiniteDominoProductLaw HLOZPathEvents
open HLOZShellZeroEndpointIncrementPartition
open HLOZShellZeroReplacementWindows LazyDecomposition
open PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingLazyDecomposition
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroActualDeltaPartition
open TilingShellZeroDeltaAcceptedCreationEndpoint
open TilingShellZeroEndpointIncrementScreen
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroStaticReplacementCardRecovery
open TilingShellZeroStaticReplacementPathRecovery
open TilingShellZeroStaticReplacementSupportRecovery
open TilingShellZeroStaticSupportEndpointLocal
open TilingShellZeroStaticSupportLocalTimeTransport
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem thresholdCreation_of_prefixedAccepted
    (initial : List Direction) {i m rank cutoff : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (tail : List Direction)
    (hlt : (prefixedTilingInsertionPrefixList initial t x r q tail).length <
      cutoff)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m rank cutoff) initial t x r q tail) :
    ThresholdCreation
      (trajectory (extendPrefix (directionVectorOfList
        (prefixedTilingInsertionPrefixList initial t x r q tail))))
      m rank (prefixedTilingInsertionPrefixList initial t x r q tail).length := by
  apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
    m rank cutoff
      (prefixedTilingInsertionPrefixList initial t x r q tail).length
      (extendPrefix (directionVectorOfList
        (prefixedTilingInsertionPrefixList initial t x r q tail))) hlt).mp
  exact haccepted

/-- A fixed-increment replacement vector reconstructs the complete literal
replacement atom at rank `k + delta`.  All endpoint counts are read at the
physical prefixed path, and the static support is recovered rather than
assumed at the replacement clock. -/
theorem prefixedReplacement_mem_actualDeltaStaticSupportAtom
    (initial : BoundaryTail) {i cap m k w low externalLow externalHigh total : ℕ}
    (t : DominoTiling) (o : Orientation) (x : Point)
    (r : TilingRetainedWord t x i) (tail : BoundaryTail)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point)
    (hSrepresented : S ⊆ tilingExternalDominoBases t x r)
    (upper : TilingAwayDomino t x r
      (tilingExternalDominoBases t x r \ S) → ℕ)
    (central : ℕ)
    (delta : ReplacementEndpointIncrement total central)
    (cutoff : ℕ) (hm : 1 < m) (hk : 0 < k) (hlow : low < m)
    (qSource qReplacement : TilingCappedCoordinates i cap)
    (ellSource ellReplacement : TruncatedTotals upper)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hdist : (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) qSource).1 =
      (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) qReplacement).1)
    (hbase : ∀ b : TilingAwayDomino t x r
        (tilingExternalDominoBases t x r \ S),
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1 =
        Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : ∀ b : TilingAwayDomino t x r
        (tilingExternalDominoBases t x r \ S),
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail)
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1)
    (htranslate : ∀ b : TilingAwayDomino t x r
        (tilingExternalDominoBases t x r \ S),
      Fintype.card (TilingCoordinatesAt t x r b.1) ≤ m - w + 1)
    (hsourceCoordinate : ∀ b, tilingShellZeroSourceCoordinate
      (cap := cap) (m := m) (w := w) t x r
        (tilingExternalDominoBases t x r \ S) upper b (ellSource b))
    (hreplacementScreen : prefixedShellZeroReplacementScreenAtIncrement
      (cap := cap) (m := m) (w := w) initial.1 t x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (qSource j : ℕ)) tail)
        (tilingExternalDominoBases t x r \ S) upper central delta
          ellReplacement)
    (htotalSource : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qSource j : ℕ)) b.1 =
        (ellSource b : ℕ))
    (htotalReplacement : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qReplacement j : ℕ)) b.1 =
        (ellReplacement b : ℕ))
    (hsourceD :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (qSource j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingDEtaAt t m k w low s v.length)
    (hsourceSupport :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (qSource j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w)
        s v.length = S)
    (hcompat : ∀ b ∈ S, OrientationCompatible o b)
    (hcard : S.card = total)
    (hexternalWindow :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (qReplacement j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      ∀ b ∈ S,
        externalLow ≤
            HLOZSourceOrientedExternalLocalTime.tilingSourceExternalBaseLocalTime
              t o s v.length b ∧
          HLOZSourceOrientedExternalLocalTime.tilingSourceExternalBaseLocalTime
            t o s v.length b < externalHigh)
    (hsourceAccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k cutoff) initial.1 t x r
        (fun j ↦ (qSource j : ℕ)) tail.1)
    (hsourcePos : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1).length)
    (hreplacementPos : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1).length)
    (hsourceLt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1).length < cutoff)
    (hreplacementLt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1).length < cutoff)
    (hcodeReplacement :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (qReplacement j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      fixedOrientedTypedExternalWordCode t o v.length s = z) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    s ∈ orientedValidShellZeroActualDeltaReplacementStaticSupportAtom
      t o m k w low externalLow externalHigh total central delta z S := by
  classical
  let D := tilingExternalDominoBases t x r \ S
  let vSource := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (qSource j : ℕ)) tail.1
  let vReplacement := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (qReplacement j : ℕ)) tail.1
  let sSource := trajectory (extendPrefix (directionVectorOfList vSource))
  let sReplacement :=
    trajectory (extendPrefix (directionVectorOfList vReplacement))
  have hterminalEq : prefixedTilingInsertionTerminal initial t x r
      (fun j ↦ (qReplacement j : ℕ)) tail =
      prefixedTilingInsertionTerminal initial t x r
        (fun j ↦ (qSource j : ℕ)) tail :=
    prefixedTilingInsertionTerminal_eq_of_coordinates initial t x r
      (fun j ↦ (qReplacement j : ℕ)) (fun j ↦ (qSource j : ℕ)) tail hstart
  have hsourceS : ∀ b ∈ S,
      tilingVTwoAt t (shellZeroSourceTotalWindow m w)
        sSource vSource.length b := by
    intro b hb
    have horiented : b ∈ orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) sSource vSource.length := by
      rw [hsourceSupport]
      exact hb
    have hraw := (mem_orientedTilingVTwoBases_iff t o
      (shellZeroSourceTotalWindow m w) sSource vSource.length b).mp
        horiented |>.1
    change b ∈ (visitedTilingBases t sSource vSource.length).filter
      (tilingVTwoAt t (shellZeroSourceTotalWindow m w)
        sSource vSource.length) at hraw
    exact (Finset.mem_filter.mp hraw).2
  have hterminalVOne : tilingVOneAt t m sSource vSource.length
      (tilingBase t (sSource vSource.length)) :=
    TilingShellZeroDEtaTerminal.tilingVOneAt_terminalBase_of_tilingDEtaAt
      hlow hsourceD
  have hacceptedReplacement : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m (k + (delta : ℕ)) cutoff) initial.1 t x r
        (fun j ↦ (qReplacement j : ℕ)) tail.1 := by
    exact prefixedTilingStoppingAccepted_at_actualEndpointIncrement_staticSupport
      initial t x r tail S upper k delta cutoff central (by omega) hk
        qSource qReplacement ellSource ellReplacement hstart hdist hbase
        hdominance hsourceCoordinate hreplacementScreen htotalSource
        htotalReplacement hsourceS hterminalVOne hsourcePos hreplacementPos
        hsourceLt hreplacementLt hsourceAccepted
  have hcreationReplacement : ThresholdCreation sReplacement m
      (k + (delta : ℕ)) vReplacement.length := by
    exact thresholdCreation_of_prefixedAccepted initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1 hreplacementLt
        hacceptedReplacement
  have htime : creationTimeNat m (k + (delta : ℕ)) sReplacement =
      vReplacement.length := creationTimeNat_eq_of_creation hcreationReplacement
  have hreaches : ReachesThreshold sReplacement m (k + (delta : ℕ)) :=
    ⟨vReplacement.length, hcreationReplacement.1⟩
  have hDtilde : tilingDtildeEtaAt t m k w low sReplacement
      vReplacement.length := by
    exact tilingDtildeEtaAt_prefixedReplacement_of_actualIncrement
      initial t o x r tail S hSrepresented upper qSource qReplacement
        ellReplacement central delta (by omega) hlow hstart hdist hbase
        hdominance htranslate hreplacementScreen htotalReplacement hsourceD
        hsourceSupport
  have hreplacementS : ∀ b ∈ S,
      tilingVTwoAt t (shellZeroSourceTotalWindow m w)
          sReplacement vReplacement.length b ∨
        tilingVTwoAt t (shellZeroReplacementTotalWindow m w)
          sReplacement vReplacement.length b := by
    intro b hbS
    let bext : TilingExternalDomino t x r := ⟨b, hSrepresented hbS⟩
    let baway : TilingAwayDomino t x r D :=
      ⟨bext, by
        intro hbD
        exact (Finset.mem_sdiff.mp hbD).2 hbS⟩
    rcases hreplacementScreen.1 with ⟨A, hA, hclass⟩
    by_cases hbA : baway ∈ A
    · left
      exact tilingVTwoAt_source_of_prefixedSourceCoordinate
        initial t x r tail D upper qReplacement ellReplacement hstart baway
          (by simpa only [D, hterminalEq] using hbase baway)
          (by simpa only [D, hterminalEq] using hdominance baway)
          (by simpa only [D] using htranslate baway)
          ((hclass baway).1 hbA) (htotalReplacement baway)
    · right
      exact tilingVTwoAt_replacement_of_prefixedReplacementCoordinate
        initial t x r tail D upper qReplacement ellReplacement hstart baway
          (by simpa only [D, hterminalEq] using hbase baway)
          (by simpa only [D, hterminalEq] using hdominance baway)
          ((hclass baway).2 hbA) (htotalReplacement baway)
  have hbaseOutside : ∀ b, IsTilingBase t b → b ∉ S →
      localTime sReplacement vReplacement.length b =
        localTime sSource vSource.length b := by
    intro b hbBase hbNot
    exact prefixedTilingLocalTime_eq_of_base_not_staticSupport
      initial t x r tail S qSource qReplacement hstart hdist b
        (by simpa only [tilingBase, if_pos hbBase] using hbNot)
  have hpartnerOutside : ∀ b, IsTilingBase t b → b ∉ S →
      localTime sReplacement vReplacement.length (tilingPartner t b) =
        localTime sSource vSource.length (tilingPartner t b) := by
    intro b hbBase hbNot
    apply prefixedTilingLocalTime_eq_of_base_not_staticSupport
      initial t x r tail S qSource qReplacement hstart hdist
        (tilingPartner t b)
    rw [tilingBase_partner]
    simpa only [tilingBase, if_pos hbBase] using hbNot
  have hsupportReplacement : orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) sReplacement vReplacement.length ∪
      orientedTilingVTwoBases t o
        (shellZeroReplacementTotalWindow m w) sReplacement
          vReplacement.length = S := by
    exact orientedReplacementSupport_eq_staticSupport S hlow hsourceD
      hsourceSupport hreplacementS hbaseOutside hpartnerOutside
  have hvalidReplacement : sReplacement ∈ validStepWalk :=
    trajectory_mem_validStepWalk _
  have htheta : orientedTilingThetaBases t o m w externalLow externalHigh
      sReplacement vReplacement.length = ∅ :=
    orientedTilingThetaBases_eq_empty_of_staticSupport S hsupportReplacement
      hexternalWindow
  have hcards :
      (orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w)
          sReplacement vReplacement.length).card = central ∧
      (orientedTilingVTwoBases t o (shellZeroReplacementTotalWindow m w)
          sReplacement vReplacement.length).card = total - central := by
    have hreplacementScreen' : prefixedShellZeroReplacementScreenAtIncrement
        (cap := cap) (m := m) (w := w) initial.1 t x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qReplacement j : ℕ)) tail)
          (tilingExternalDominoBases t x r \ S) upper central delta
            ellReplacement := by
      simpa only [hterminalEq] using hreplacementScreen
    exact card_orientedVTwo_source_and_replacement_of_incrementScreen
      initial t o x r tail S hSrepresented upper qReplacement ellReplacement
        delta hstart
        (by intro b; simpa only [hterminalEq] using hbase b)
        (by intro b; simpa only [hterminalEq] using hdominance b)
        htranslate htotalReplacement
        hreplacementScreen' hsupportReplacement hcompat hcard
  change sReplacement ∈ _
  refine ⟨⟨⟨?_, ?_⟩, hvalidReplacement⟩, ?_⟩
  · refine ⟨hreaches, ?_⟩
    change let n := creationTimeNat m (k + (delta : ℕ)) sReplacement
      tilingDtildeEtaAt t m k w low sReplacement n ∧
        orientedTilingThetaBases t o m w externalLow externalHigh
          sReplacement n = ∅ ∧
        (orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w)
          sReplacement n).card = central ∧
        (orientedTilingVTwoBases t o (shellZeroReplacementTotalWindow m w)
          sReplacement n).card = total - central
    rw [htime]
    exact ⟨hDtilde, htheta, hcards⟩
  · change fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m (k + (delta : ℕ)) sReplacement) sReplacement = z
    rw [htime]
    exact hcodeReplacement
  · change actualDeltaReplacementStaticSupport t o m k w total central delta
        sReplacement = S
    simp only [actualDeltaReplacementStaticSupport, actualReplacementCreationRank,
      htime]
    exact hsupportReplacement

end

end Erdos1165.TilingShellZeroActualDeltaReplacementAtomRecovery
