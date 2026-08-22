/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroStaticReplacementDEta
import ErdosProblems.Erdos1165.TilingShellZeroStaticSupportLocalTimeTransport

/-!
# Pathwise `Dtilde_η` recovery from a fixed actual-delta screen

This module connects the finite away-coordinate screen to the literal walk
classification.  It proves the replacement `Dtilde_η` predicate directly;
there is no replacement-rank or probability premise.
-/

namespace Erdos1165.TilingShellZeroStaticReplacementPathRecovery

open FiniteDominoProductLaw HLOZShellZeroEndpointIncrementPartition
open HLOZShellZeroReplacementWindows LazyDecomposition
open PathInsertion PreStoppingFiber SpatialInsertionFiber StoppedInsertion
open VariableStoppedFiber
open TilingCappedMarginalization TilingLazyDecomposition
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroEndpointIncrementScreen
open TilingShellZeroStaticReplacementDEta
open TilingShellZeroStaticSupportEndpointLocal
open TilingShellZeroStaticSupportLocalTimeTransport
open TilingShellZeroSourcePartition TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A fixed-central, fixed-actual-increment away vector reconstructs the
literal replacement `Dtilde_η` predicate. -/
theorem tilingDtildeEtaAt_prefixedReplacement_of_actualIncrement
    (initial : BoundaryTail) {i cap m k w low : ℕ}
    (t : DominoTiling) (o : Orientation) (x : Point)
    (r : TilingRetainedWord t x i) (tail : BoundaryTail)
    (S : Finset Point)
    (hSrepresented : S ⊆ tilingExternalDominoBases t x r)
    (upper : TilingAwayDomino t x r
      (tilingExternalDominoBases t x r \ S) → ℕ)
    (qSource qReplacement : TilingCappedCoordinates i cap)
    (ellReplacement : TruncatedTotals upper)
    (central delta : ℕ) (hm : 0 < m) (hlow : low < m)
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
    (hreplacement : prefixedShellZeroReplacementScreenAtIncrement
      (cap := cap) (m := m) (w := w) initial.1 t x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (qSource j : ℕ)) tail)
        (tilingExternalDominoBases t x r \ S) upper central delta
          ellReplacement)
    (htotalReplacement : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qReplacement j : ℕ)) b.1 =
        (ellReplacement b : ℕ))
    (hsourceD :
      let vSource := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (qSource j : ℕ)) tail.1
      let sSource := trajectory
        (extendPrefix (directionVectorOfList vSource))
      tilingDEtaAt t m k w low sSource vSource.length)
    (hsourceSupport :
      let vSource := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (qSource j : ℕ)) tail.1
      let sSource := trajectory
        (extendPrefix (directionVectorOfList vSource))
      orientedTilingVTwoBases t o (shellZeroSourceTotalWindow m w)
        sSource vSource.length = S) :
    let vReplacement := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1
    let sReplacement := trajectory
      (extendPrefix (directionVectorOfList vReplacement))
    tilingDtildeEtaAt t m k w low sReplacement vReplacement.length := by
  classical
  let D := tilingExternalDominoBases t x r \ S
  let vSource := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (qSource j : ℕ)) tail.1
  let vReplacement := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (qReplacement j : ℕ)) tail.1
  let sSource := trajectory (extendPrefix (directionVectorOfList vSource))
  let sReplacement :=
    trajectory (extendPrefix (directionVectorOfList vReplacement))
  let terminalSource := prefixedTilingInsertionTerminal initial t x r
    (fun j ↦ (qSource j : ℕ)) tail
  let terminalReplacement := prefixedTilingInsertionTerminal initial t x r
    (fun j ↦ (qReplacement j : ℕ)) tail
  have hterminalEq : terminalReplacement = terminalSource := by
    exact prefixedTilingInsertionTerminal_eq_of_coordinates initial t x r
      (fun j ↦ (qReplacement j : ℕ)) (fun j ↦ (qSource j : ℕ)) tail
        hstart
  have hsourceS : ∀ b ∈ S,
      tilingVTwoAt t (shellZeroSourceTotalWindow m w)
        sSource vSource.length b := by
    intro b hbS
    have hbOriented : b ∈ orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) sSource vSource.length := by
      rw [hsourceSupport]
      exact hbS
    have hbRaw := (mem_orientedTilingVTwoBases_iff t o
      (shellZeroSourceTotalWindow m w) sSource vSource.length b).mp
        hbOriented |>.1
    change b ∈ (visitedTilingBases t sSource vSource.length).filter
      (tilingVTwoAt t (shellZeroSourceTotalWindow m w)
        sSource vSource.length) at hbRaw
    exact (Finset.mem_filter.mp hbRaw).2
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
    rcases hreplacement.1 with ⟨A, hA, hclass⟩
    by_cases hbA : baway ∈ A
    · left
      apply tilingVTwoAt_source_of_prefixedSourceCoordinate
        initial t x r tail D upper qReplacement ellReplacement hstart baway
      · simpa only [terminalReplacement, hterminalEq, D] using hbase baway
      · simpa only [terminalReplacement, hterminalEq, D] using
          hdominance baway
      · simpa only [D] using htranslate baway
      · exact (hclass baway).1 hbA
      · exact htotalReplacement baway
    · right
      apply tilingVTwoAt_replacement_of_prefixedReplacementCoordinate
        initial t x r tail D upper qReplacement ellReplacement hstart baway
      · simpa only [terminalReplacement, hterminalEq, D] using hbase baway
      · simpa only [terminalReplacement, hterminalEq, D] using
          hdominance baway
      · exact (hclass baway).2 hbA
      · exact htotalReplacement baway
  have hbaseOutside : ∀ b, IsTilingBase t b → b ∉ S →
      localTime sReplacement vReplacement.length b =
        localTime sSource vSource.length b := by
    intro b hbIsBase hbNotS
    apply prefixedTilingLocalTime_eq_of_base_not_staticSupport
      initial t x r tail S qSource qReplacement hstart hdist b
    simpa only [tilingBase, if_pos hbIsBase] using hbNotS
  have hpartnerOutside : ∀ b, IsTilingBase t b → b ∉ S →
      localTime sReplacement vReplacement.length (tilingPartner t b) =
        localTime sSource vSource.length (tilingPartner t b) := by
    intro b hbIsBase hbNotS
    apply prefixedTilingLocalTime_eq_of_base_not_staticSupport
      initial t x r tail S qSource qReplacement hstart hdist
        (tilingPartner t b)
    rw [tilingBase_partner]
    simpa only [tilingBase, if_pos hbIsBase] using hbNotS
  have hsourceTerminalVOne : tilingVOneAt t m sSource vSource.length
      (tilingBase t (sSource vSource.length)) :=
    TilingShellZeroDEtaTerminal.tilingVOneAt_terminalBase_of_tilingDEtaAt
      hlow hsourceD
  have hendpointLocal :=
    prefixedTilingFinalLocalTime_eq_of_staticSourceSupport
        initial t x r tail S qSource qReplacement hstart hdist hsourceS
          hsourceTerminalVOne
  have hend : sSource vSource.length =
      sReplacement vReplacement.length :=
    prefixedTilingInsertionEndpoint_eq_of_coordinates initial t x r
      (fun j ↦ (qSource j : ℕ)) (fun j ↦ (qReplacement j : ℕ)) tail
        hstart
  have hreplacementTerminal : localTime sReplacement vReplacement.length
      (sReplacement vReplacement.length) = m := by
    exact hendpointLocal.symm.trans hsourceD.2.2
  have hterminalBaseNotS : tilingBase t (sSource vSource.length) ∉ S := by
    intro hbS
    have hbVTwo := hsourceS _ hbS
    have hbaseLt := (mem_shellZeroSourceTotalWindow.mp hbVTwo.2).2
    have hpartnerLt : localTime sSource vSource.length
        (tilingPartner t (tilingBase t (sSource vSource.length))) < m :=
      lt_of_le_of_lt hbVTwo.1 hbaseLt
    unfold tilingVOneAt at hsourceTerminalVOne
    omega
  have hreplacementTerminalVOne : tilingVOneAt t m sReplacement
      vReplacement.length
      (tilingBase t (sReplacement vReplacement.length)) := by
    have hbasePoint : tilingBase t (sReplacement vReplacement.length) =
        tilingBase t (sSource vSource.length) := by rw [← hend]
    have hbaseEq := hbaseOutside (tilingBase t (sSource vSource.length))
      (HLOZThetaSourceBalance.isTilingBase_tilingBase t
        (sSource vSource.length)) hterminalBaseNotS
    have hpartnerEq := hpartnerOutside
      (tilingBase t (sSource vSource.length))
      (HLOZThetaSourceBalance.isTilingBase_tilingBase t
        (sSource vSource.length)) hterminalBaseNotS
    unfold tilingVOneAt at hsourceTerminalVOne ⊢
    rw [hbasePoint, hbaseEq, hpartnerEq]
    exact hsourceTerminalVOne
  exact tilingDtildeEtaAt_of_staticReplacement S hm hsourceD hsourceS
    hreplacementS hbaseOutside hpartnerOutside hreplacementTerminal
      hreplacementTerminalVOne

end

end Erdos1165.TilingShellZeroStaticReplacementPathRecovery
