/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroThresholdCountAdd
import ErdosProblems.Erdos1165.TilingShellZeroStaticSupportEndpointLocal

/-!
# Actual-rank acceptance after changing source-window coordinates

The shell-zero replacement screen classifies every changed coordinate into
one of two prescribed windows.  Proposition 4.5 needs a slightly different
clock fact: after a source-window witness has fixed the old creation clock,
the exposed coordinates may be assigned *arbitrary* truncated totals.  The
new clock is then indexed by the literal number of newly thresholded
endpoints.

This file isolates that deterministic statement.  It does not assert any
probability comparison.  The unchanged distinguished projection controls
all sites outside the exposed support, the source window says that the
exposed endpoints were strictly below level, and the explicit endpoint sum
is therefore exactly the increase in threshold rank.
-/

open scoped BigOperators

namespace Erdos1165.TilingSourceSlotActualDeltaAcceptedCreation

open FiniteDominoProductLaw HLOZPathEvents
open HLOZShellZeroEndpointIncrementPartition HLOZShellZeroReplacementWindows
open LazyDecomposition PreStoppingFiber PreStoppingSpatialLaw
open StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingDistinguishedTraceInvariant
open TilingLazyDecomposition
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedRaisedRankAcceptedCreationEndpoint
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroEndpointIncrementCard TilingShellZeroEndpointIncrementScreen
open TilingShellZeroSourcePartition TilingShellZeroStaticSupportEndpointLocal
open TilingShellZeroThresholdCountAdd TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-! ## Threshold-count transfer with an unrestricted replacement vector -/

/-- If every exposed coordinate of the source vector is in the below-level
source window, changing those coordinates arbitrarily adds exactly the
endpoint count computed from the replacement totals. -/
theorem thresholdCount_prefixedTilingInsertion_add_of_arbitraryEndpointIncrement
    (initial : BoundaryTail) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : BoundaryTail) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (hm : 0 < m)
    (qSource qReplacement : TilingCappedCoordinates i cap)
    (ellSource ellReplacement : TruncatedTotals upper)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hdist : (splitTilingCoordinatesEquiv t x r D qSource).1 =
      (splitTilingCoordinatesEquiv t x r D qReplacement).1)
    (hbase : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1 =
        Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail)
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1)
    (hsource : ∀ b, tilingShellZeroSourceCoordinate
      (cap := cap) (m := m) (w := w) t x r D upper b (ellSource b))
    (htotalSource : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qSource j : ℕ)) b.1 =
        (ellSource b : ℕ))
    (htotalReplacement : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qReplacement j : ℕ)) b.1 =
        (ellReplacement b : ℕ)) :
    let vSource := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1
    let vReplacement := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1
    let sSource := trajectory
      (extendPrefix (directionVectorOfList vSource))
    let sReplacement := trajectory
      (extendPrefix (directionVectorOfList vReplacement))
    thresholdCount sReplacement vReplacement.length m =
      thresholdCount sSource vSource.length m +
        endpointIncrementOfVector
          (prefixedShellZeroEndpointContribution initial.1 t x r
            (prefixedTilingInsertionTerminal initial t x r
              (fun j ↦ (qSource j : ℕ)) tail)
            D upper m) ellReplacement := by
  classical
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (qSource j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (qReplacement j : ℕ)
  let terminal := prefixedTilingInsertionTerminal initial t x r qNat tail
  let vSource := prefixedTilingInsertionPrefixList initial.1 t x r qNat tail.1
  let vReplacement := prefixedTilingInsertionPrefixList initial.1 t x r qNat' tail.1
  let sSource := trajectory (extendPrefix (directionVectorOfList vSource))
  let sReplacement := trajectory
    (extendPrefix (directionVectorOfList vReplacement))
  let sourceSites := listThresholdSites
    (prefixedTilingPrefixPointPath initial.1 x
      (tilingInsertGapVector t x r qNat) terminal) m
  let replacementSites := listThresholdSites
    (prefixedTilingPrefixPointPath initial.1 x
      (tilingInsertGapVector t x r qNat') terminal) m
  let away : Point → Prop := fun y ↦
    tilingBase t y ∈ tilingExternalDominoBases t x r ∧ tilingBase t y ∉ D
  have hterminal' :
      prefixedTilingInsertionTerminal initial t x r qNat' tail = terminal :=
    (prefixedTilingInsertionTerminal_eq_of_coordinates
      initial t x r qNat qNat' tail hstart).symm
  have hpathSource : finitePathList (pathPrefix sSource vSource.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r qNat) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r qNat tail hstart
  have hpathReplacement :
      finitePathList (pathPrefix sReplacement vReplacement.length) =
        prefixedTilingPrefixPointPath initial.1 x
          (tilingInsertGapVector t x r qNat') terminal := by
    rw [← hterminal']
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r qNat' tail hstart
  have hsourceFilter :=
    filter_listThresholdSites_eq_prefixedShellZeroThresholdedAwayEndpoints
      initial.1 t x r terminal D upper m hm qSource ellSource htotalSource
  have hreplacementFilter :=
    filter_listThresholdSites_eq_prefixedShellZeroThresholdedAwayEndpoints
      initial.1 t x r terminal D upper m hm qReplacement ellReplacement
        htotalReplacement
  have hsourceIncrement : endpointIncrementOfVector
      (prefixedShellZeroEndpointContribution initial.1 t x r terminal D upper m)
      ellSource = 0 := by
    unfold endpointIncrementOfVector
    apply Finset.sum_eq_zero
    intro b _
    exact prefixedShellZeroEndpointContribution_eq_zero_of_source
      initial.1 t x r terminal D upper hbase hdominance b (ellSource b)
        (hsource b)
  have hsourceAway : (sourceSites.filter away).card = 0 := by
    rw [show sourceSites.filter away =
        prefixedShellZeroThresholdedAwayEndpoints initial.1 t x r terminal D
          upper m ellSource by exact hsourceFilter,
      card_prefixedShellZeroThresholdedAwayEndpoints, hsourceIncrement]
  have hreplacementAway : (replacementSites.filter away).card =
      endpointIncrementOfVector
        (prefixedShellZeroEndpointContribution initial.1 t x r terminal D
          upper m) ellReplacement := by
    rw [show replacementSites.filter away =
        prefixedShellZeroThresholdedAwayEndpoints initial.1 t x r terminal D
          upper m ellReplacement by exact hreplacementFilter,
      card_prefixedShellZeroThresholdedAwayEndpoints]
  have hother := filter_not_away_listThresholdSites_eq_of_distinguished_eq
    initial.1 t x r terminal D m hm qSource qReplacement hdist
  have hotherCard : (sourceSites.filter fun y ↦ ¬away y).card =
      (replacementSites.filter fun y ↦ ¬away y).card := by
    exact congrArg Finset.card hother
  have hsourceSplit := Finset.card_filter_add_card_filter_not
    (s := sourceSites) away
  have hreplacementSplit := Finset.card_filter_add_card_filter_not
    (s := replacementSites) away
  change thresholdCount sReplacement vReplacement.length m =
    thresholdCount sSource vSource.length m + _
  unfold thresholdCount
  rw [← listThresholdSites_finitePathList sReplacement
      vReplacement.length m hm,
    ← listThresholdSites_finitePathList sSource vSource.length m hm,
    hpathReplacement, hpathSource]
  change replacementSites.card = sourceSites.card + _
  calc
    replacementSites.card =
        (replacementSites.filter away).card +
          (replacementSites.filter fun y ↦ ¬away y).card :=
      hreplacementSplit.symm
    _ = endpointIncrementOfVector
          (prefixedShellZeroEndpointContribution initial.1 t x r terminal D
            upper m) ellReplacement +
        (sourceSites.filter fun y ↦ ¬away y).card := by
      rw [hreplacementAway, ← hotherCard]
    _ = sourceSites.card + endpointIncrementOfVector
          (prefixedShellZeroEndpointContribution initial.1 t x r terminal D
            upper m) ellReplacement := by
      rw [← hsourceSplit, hsourceAway]
      omega

/-! ## Honest stopped-clock transfer -/

/-- The final-site local time is invariant under arbitrary exposed-coordinate
changes once the source exposed coordinates are all strictly below level.
Indeed the accepted source endpoint is at level `m`, so its domino cannot be
one of the exposed dominoes.  It is therefore either distinguished or absent
from the retained external word, and both cases are insertion-invariant. -/
theorem prefixedTilingFinalLocalTime_eq_of_sourceCoordinates
    (initial : BoundaryTail) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : BoundaryTail) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (hk : 0 < k) (cutoff : ℕ)
    (qSource qReplacement : TilingCappedCoordinates i cap)
    (ellSource : TruncatedTotals upper)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hdist : (splitTilingCoordinatesEquiv t x r D qSource).1 =
      (splitTilingCoordinatesEquiv t x r D qReplacement).1)
    (hbase : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1 =
        Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail)
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1)
    (hsource : ∀ b, tilingShellZeroSourceCoordinate
      (cap := cap) (m := m) (w := w) t x r D upper b (ellSource b))
    (htotalSource : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qSource j : ℕ)) b.1 =
        (ellSource b : ℕ))
    (hlt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1).length < cutoff)
    (haccepted : PrefixedTilingStoppingAccepted (truncatedLevelTime m k cutoff)
      initial.1 t x r (fun j ↦ (qSource j : ℕ)) tail.1) :
    let vSource := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1
    let vReplacement := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1
    let sSource := trajectory (extendPrefix (directionVectorOfList vSource))
    let sReplacement := trajectory
      (extendPrefix (directionVectorOfList vReplacement))
    localTime sSource vSource.length (sSource vSource.length) =
      localTime sReplacement vReplacement.length
        (sReplacement vReplacement.length) := by
  classical
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (qSource j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (qReplacement j : ℕ)
  let terminal := prefixedTilingInsertionTerminal initial t x r qNat tail
  let vSource := prefixedTilingInsertionPrefixList initial.1 t x r qNat tail.1
  let vReplacement := prefixedTilingInsertionPrefixList initial.1 t x r qNat' tail.1
  let sSource := trajectory (extendPrefix (directionVectorOfList vSource))
  let sReplacement := trajectory
    (extendPrefix (directionVectorOfList vReplacement))
  have hterminal' :
      prefixedTilingInsertionTerminal initial t x r qNat' tail = terminal :=
    (prefixedTilingInsertionTerminal_eq_of_coordinates
      initial t x r qNat qNat' tail hstart).symm
  have hpathSource : finitePathList (pathPrefix sSource vSource.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r qNat) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r qNat tail hstart
  have hpathReplacement :
      finitePathList (pathPrefix sReplacement vReplacement.length) =
        prefixedTilingPrefixPointPath initial.1 x
          (tilingInsertGapVector t x r qNat') terminal := by
    rw [← hterminal']
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r qNat' tail hstart
  have hend : sSource vSource.length = sReplacement vReplacement.length :=
    prefixedTilingInsertionEndpoint_eq_of_coordinates
      initial t x r qNat qNat' tail hstart
  have hcreation : ThresholdCreation sSource m k vSource.length := by
    exact (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff vSource.length _ hlt).mp haccepted
  have hterminalHigh : m ≤
      localTime sSource vSource.length (sSource vSource.length) :=
    (mem_thresholdSites sSource vSource.length m
      (sSource vSource.length)).mp
        (position_mem_thresholdSites_of_creation hk hcreation) |>.2
  let b := tilingBase t (sSource vSource.length)
  have hbNotAway : ¬(b ∈ tilingExternalDominoBases t x r ∧ b ∉ D) := by
    rintro ⟨hbExternal, hbD⟩
    let bext : TilingExternalDomino t x r := ⟨b, hbExternal⟩
    let ba : TilingAwayDomino t x r D := ⟨bext, hbD⟩
    have hsourceLt :
        Fintype.card (TilingCoordinatesAt t x r bext) +
            (ellSource ba : ℕ) < m := by
      have hs := hsource ba
      simp only [tilingShellZeroSourceCoordinate,
        mem_shellZeroSourceFailureWindow] at hs
      have hsupper : (ellSource ba : ℕ) <
          m - Fintype.card (TilingCoordinatesAt t x r bext) := by
        simpa only [ba, bext] using hs.2
      have hi : Fintype.card (TilingCoordinatesAt t x r bext) < m :=
        (Nat.sub_pos_iff_lt).mp (Nat.zero_lt_of_lt hsupper)
      omega
    have hbaseLt :
        prefixedTilingFixedBoundaryLocalTime initial.1 x r terminal b +
            tilingDominoTotal t x r qNat bext < m := by
      rw [hbase ba, htotalSource ba]
      exact hsourceLt
    have hpartnerLt :
        prefixedTilingFixedBoundaryLocalTime initial.1 x r terminal
              (tilingPartner t b) +
            tilingDominoTotal t x r qNat bext < m := by
      exact lt_of_le_of_lt
        (Nat.add_le_add_right (hdominance ba)
          (tilingDominoTotal t x r qNat bext)) hbaseLt
    have hlocal := prefixedTilingInsertedPrefix_localTime_at_dominoPoint
      initial.1 t x r qNat terminal bext (sSource vSource.length) rfl
    have hendpointCase := point_eq_tilingBase_or_partner_base
      t (sSource vSource.length)
    rcases hendpointCase with hbasePoint | hpartnerPoint
    · have hlt : listLocalTime
          (prefixedTilingPrefixPointPath initial.1 x
            (tilingInsertGapVector t x r qNat) terminal)
          (sSource vSource.length) < m := by
        rw [hlocal, hbasePoint]
        exact hbaseLt
      have hlt' : localTime sSource vSource.length
          (sSource vSource.length) < m := by
        simpa only [localTime_eq_listLocalTime, hpathSource] using hlt
      omega
    · have hlt : listLocalTime
          (prefixedTilingPrefixPointPath initial.1 x
            (tilingInsertGapVector t x r qNat) terminal)
          (sSource vSource.length) < m := by
        rw [hlocal, hpartnerPoint]
        exact hpartnerLt
      have hlt' : localTime sSource vSource.length
          (sSource vSource.length) < m := by
        simpa only [localTime_eq_listLocalTime, hpathSource] using hlt
      omega
  have hlist : listLocalTime
        (prefixedTilingPrefixPointPath initial.1 x
          (tilingInsertGapVector t x r qNat) terminal)
        (sSource vSource.length) =
      listLocalTime
        (prefixedTilingPrefixPointPath initial.1 x
          (tilingInsertGapVector t x r qNat') terminal)
        (sSource vSource.length) := by
    by_cases hbExternal : b ∈ tilingExternalDominoBases t x r
    · have hbD : b ∈ D := by
        by_contra hbD
        exact hbNotAway ⟨hbExternal, hbD⟩
      exact prefixedTilingPrefixLocalTime_eq_of_distinguished_eq
        initial.1 t x r terminal D qSource qReplacement hdist
          (sSource vSource.length) hbD
    · rw [prefixedTilingInsertedPrefix_localTime_of_base_not_mem
          initial.1 t x r qNat terminal (sSource vSource.length),
        prefixedTilingInsertedPrefix_localTime_of_base_not_mem
          initial.1 t x r qNat' terminal (sSource vSource.length)]
      · exact hbExternal
      · exact hbExternal
  change localTime sSource vSource.length (sSource vSource.length) =
    localTime sReplacement vReplacement.length
      (sReplacement vReplacement.length)
  rw [← hend, localTime_eq_listLocalTime, localTime_eq_listLocalTime,
    hpathSource, hpathReplacement]
  exact hlist

/-- Stopped-clock transfer requiring only the literal source-coordinate
screen.  No `Dη`, terminal `V₁`, or replacement-window hypothesis is
needed. -/
theorem prefixedTilingStoppingAccepted_at_arbitraryEndpointIncrement
    (initial : BoundaryTail) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : BoundaryTail) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (k cutoff : ℕ) (hm : 0 < m) (hk : 0 < k)
    (qSource qReplacement : TilingCappedCoordinates i cap)
    (ellSource ellReplacement : TruncatedTotals upper)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hdist : (splitTilingCoordinatesEquiv t x r D qSource).1 =
      (splitTilingCoordinatesEquiv t x r D qReplacement).1)
    (hbase : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1 =
        Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail)
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1)
    (hsource : ∀ b, tilingShellZeroSourceCoordinate
      (cap := cap) (m := m) (w := w) t x r D upper b (ellSource b))
    (htotalSource : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qSource j : ℕ)) b.1 =
        (ellSource b : ℕ))
    (htotalReplacement : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qReplacement j : ℕ)) b.1 =
        (ellReplacement b : ℕ))
    (hpos : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1).length)
    (hpos' : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1).length)
    (hlt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1).length < cutoff)
    (hlt' : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1).length < cutoff)
    (haccepted : PrefixedTilingStoppingAccepted (truncatedLevelTime m k cutoff)
      initial.1 t x r (fun j ↦ (qSource j : ℕ)) tail.1) :
    let delta := endpointIncrementOfVector
      (prefixedShellZeroEndpointContribution initial.1 t x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (qSource j : ℕ)) tail) D upper m) ellReplacement
    PrefixedTilingStoppingAccepted
      (truncatedLevelTime m (k + delta) cutoff)
        initial.1 t x r (fun j ↦ (qReplacement j : ℕ)) tail.1 := by
  let delta := endpointIncrementOfVector
    (prefixedShellZeroEndpointContribution initial.1 t x r
      (prefixedTilingInsertionTerminal initial t x r
        (fun j ↦ (qSource j : ℕ)) tail) D upper m) ellReplacement
  have hcount :=
    thresholdCount_prefixedTilingInsertion_add_of_arbitraryEndpointIncrement
      initial t x r tail D upper hm qSource qReplacement ellSource
        ellReplacement hstart hdist hbase hdominance hsource htotalSource
        htotalReplacement
  have hendpoint := prefixedTilingFinalLocalTime_eq_of_sourceCoordinates
    initial t x r tail D upper hk cutoff qSource qReplacement ellSource
      hstart hdist hbase hdominance hsource htotalSource hlt haccepted
  exact prefixedTilingStoppingAccepted_of_thresholdCount_add_of_endpointLocal
    initial t x m k delta cutoff hm hk r tail qSource qReplacement
      hcount hendpoint hpos hpos' hlt hlt' haccepted

/-- An accepted source creation remains an accepted creation after arbitrary
changes of the exposed coordinates.  Its new rank is the actual number of
newly thresholded endpoints.  The source `V₂` support and terminal `V₁`
condition ensure that the physical final-site local time is unchanged. -/
theorem prefixedTilingStoppingAccepted_at_arbitraryEndpointIncrement_staticSupport
    (initial : BoundaryTail) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : BoundaryTail) (S : Finset Point)
    (upper : TilingAwayDomino t x r
      (tilingExternalDominoBases t x r \ S) → ℕ)
    (k cutoff : ℕ) (hm : 0 < m) (hk : 0 < k)
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
    (hsource : ∀ b, tilingShellZeroSourceCoordinate
      (cap := cap) (m := m) (w := w) t x r
        (tilingExternalDominoBases t x r \ S) upper b (ellSource b))
    (htotalSource : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qSource j : ℕ)) b.1 =
        (ellSource b : ℕ))
    (htotalReplacement : ∀ b,
      tilingDominoTotal t x r (fun j ↦ (qReplacement j : ℕ)) b.1 =
        (ellReplacement b : ℕ))
    (hsourceVTwo :
      let vSource := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (qSource j : ℕ)) tail.1
      let sSource := trajectory
        (extendPrefix (directionVectorOfList vSource))
      ∀ b ∈ S, tilingVTwoAt t (shellZeroSourceTotalWindow m w)
        sSource vSource.length b)
    (hterminalVOne :
      let vSource := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (qSource j : ℕ)) tail.1
      let sSource := trajectory
        (extendPrefix (directionVectorOfList vSource))
      tilingVOneAt t m sSource vSource.length
        (tilingBase t (sSource vSource.length)))
    (hpos : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1).length)
    (hpos' : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1).length)
    (hlt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qSource j : ℕ)) tail.1).length < cutoff)
    (hlt' : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (qReplacement j : ℕ)) tail.1).length < cutoff)
    (haccepted : PrefixedTilingStoppingAccepted (truncatedLevelTime m k cutoff)
      initial.1 t x r (fun j ↦ (qSource j : ℕ)) tail.1) :
    let delta := endpointIncrementOfVector
      (prefixedShellZeroEndpointContribution initial.1 t x r
        (prefixedTilingInsertionTerminal initial t x r
          (fun j ↦ (qSource j : ℕ)) tail)
        (tilingExternalDominoBases t x r \ S) upper m) ellReplacement
    PrefixedTilingStoppingAccepted
      (truncatedLevelTime m (k + delta) cutoff)
        initial.1 t x r (fun j ↦ (qReplacement j : ℕ)) tail.1 := by
  let delta := endpointIncrementOfVector
    (prefixedShellZeroEndpointContribution initial.1 t x r
      (prefixedTilingInsertionTerminal initial t x r
        (fun j ↦ (qSource j : ℕ)) tail)
      (tilingExternalDominoBases t x r \ S) upper m) ellReplacement
  have hcount :=
    thresholdCount_prefixedTilingInsertion_add_of_arbitraryEndpointIncrement
      initial t x r tail (tilingExternalDominoBases t x r \ S) upper hm
      qSource qReplacement ellSource ellReplacement hstart hdist hbase
      hdominance hsource htotalSource htotalReplacement
  have hendpoint :=
    prefixedTilingFinalLocalTime_eq_of_staticSourceSupport
      initial t x r tail S qSource qReplacement hstart hdist hsourceVTwo
        hterminalVOne
  exact prefixedTilingStoppingAccepted_of_thresholdCount_add_of_endpointLocal
    initial t x m k delta cutoff hm hk r tail qSource qReplacement
      hcount hendpoint hpos hpos' hlt hlt' haccepted

end

end Erdos1165.TilingSourceSlotActualDeltaAcceptedCreation
