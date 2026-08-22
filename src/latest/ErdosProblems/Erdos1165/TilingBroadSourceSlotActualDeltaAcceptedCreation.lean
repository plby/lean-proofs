/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingSourceSlotActualDeltaAcceptedCreation

/-!
# Actual-rank transfer for a broad, non-dominant source slot

The first-strip source carrier uses a `V₂` base and can therefore put the
partner boundary below the base boundary.  The broad candidate-local
Proposition 4.5 slot has no dominance condition.  What its rank transfer
actually needs is weaker and symmetric: before the selected coordinate is
changed, both endpoints of every exposed domino are below level `m`.

This file records that literal version of the actual-`δ` threshold-count
identity.  It deliberately has neither a `V₂` nor a source-window premise.
-/

open scoped BigOperators

namespace Erdos1165.TilingBroadSourceSlotActualDeltaAcceptedCreation

open FiniteDominoProductLaw HLOZPathEvents
open HLOZShellZeroEndpointIncrementPartition
open LazyDecomposition PreStoppingFiber PreStoppingSpatialLaw
open StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization TilingDistinguishedTraceInvariant
open TilingLazyDecomposition
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedRaisedRankAcceptedCreationEndpoint
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroEndpointIncrementCard TilingShellZeroEndpointIncrementScreen
open TilingShellZeroThresholdCountAdd TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- If the old total at both endpoints is below level `m`, the explicit
endpoint contribution of that coordinate is zero. -/
theorem prefixedShellZeroEndpointContribution_eq_zero_of_both_below
    (initial : List Direction) {i m : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D) (v : Fin (upper b))
    (hbase : prefixedTilingFixedBoundaryLocalTime initial x r terminal
        b.1.1 + (v : ℕ) < m)
    (hpartner : prefixedTilingFixedBoundaryLocalTime initial x r terminal
        (tilingPartner t b.1.1) + (v : ℕ) < m) :
    prefixedShellZeroEndpointContribution initial t x r terminal D upper
      m b v = 0 := by
  unfold prefixedShellZeroEndpointContribution
  rw [if_neg (Nat.not_le.mpr hbase),
    if_neg (Nat.not_le.mpr hpartner)]

/-- Broad actual-rank transfer.  The distinguished projection fixes every
unexposed site.  On exposed dominoes the old vector is below level at both
endpoints, while the new vector contributes its literal number (zero, one,
or two) of newly thresholded endpoints. -/
theorem thresholdCount_prefixedTilingInsertion_add_of_broadEndpointIncrement
    (initial : BoundaryTail) {i cap m : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : BoundaryTail) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (hm : 0 < m)
    (qSource qReplacement : TilingCappedCoordinates i cap)
    (ellSource ellReplacement : TruncatedTotals upper)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hdist : (splitTilingCoordinatesEquiv t x r D qSource).1 =
      (splitTilingCoordinatesEquiv t x r D qReplacement).1)
    (hsourceBelow : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1 +
            (ellSource b : ℕ) < m ∧
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail)
          (tilingPartner t b.1.1) + (ellSource b : ℕ) < m)
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
    exact prefixedShellZeroEndpointContribution_eq_zero_of_both_below
      initial.1 t x r terminal D upper b (ellSource b)
        (hsourceBelow b).1 (hsourceBelow b).2
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

/-- The final-site local time is unchanged when all exposed source dominoes
are strictly below level at both endpoints.  This is the symmetric,
non-dominant analogue of the source-`V₂` final-site lemma: the accepted
creation endpoint is at level `m`, so its domino cannot be exposed. -/
theorem prefixedTilingFinalLocalTime_eq_of_broadSourceCoordinates
    (initial : BoundaryTail) {i cap m : ℕ}
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
    (hsourceBelow : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1 +
            (ellSource b : ℕ) < m ∧
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail)
          (tilingPartner t b.1.1) + (ellSource b : ℕ) < m)
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
    have hbaseLt :
        prefixedTilingFixedBoundaryLocalTime initial.1 x r terminal b +
            tilingDominoTotal t x r qNat bext < m := by
      rw [htotalSource ba]
      exact (hsourceBelow ba).1
    have hpartnerLt :
        prefixedTilingFixedBoundaryLocalTime initial.1 x r terminal
              (tilingPartner t b) +
            tilingDominoTotal t x r qNat bext < m := by
      rw [htotalSource ba]
      exact (hsourceBelow ba).2
    have hlocal := prefixedTilingInsertedPrefix_localTime_at_dominoPoint
      initial.1 t x r qNat terminal bext (sSource vSource.length) rfl
    have hendpointCase := point_eq_tilingBase_or_partner_base
      t (sSource vSource.length)
    rcases hendpointCase with hbasePoint | hpartnerPoint
    · have hlt' : listLocalTime
          (prefixedTilingPrefixPointPath initial.1 x
            (tilingInsertGapVector t x r qNat) terminal)
          (sSource vSource.length) < m := by
        rw [hlocal, hbasePoint]
        exact hbaseLt
      have hlt'' : localTime sSource vSource.length
          (sSource vSource.length) < m := by
        simpa only [localTime_eq_listLocalTime, hpathSource] using hlt'
      omega
    · have hlt' : listLocalTime
          (prefixedTilingPrefixPointPath initial.1 x
            (tilingInsertGapVector t x r qNat) terminal)
          (sSource vSource.length) < m := by
        rw [hlocal, hpartnerPoint]
        exact hpartnerLt
      have hlt'' : localTime sSource vSource.length
          (sSource vSource.length) < m := by
        simpa only [localTime_eq_listLocalTime, hpathSource] using hlt'
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

/-- Broad stopped-clock transfer.  No dominance or source-`V₂` hypothesis
is used: it is enough that the source vector is below level at both endpoints
of every exposed domino. -/
theorem prefixedTilingStoppingAccepted_at_broadEndpointIncrement
    (initial : BoundaryTail) {i cap m : ℕ}
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
    (hsourceBelow : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail) b.1.1 +
            (ellSource b : ℕ) < m ∧
      prefixedTilingFixedBoundaryLocalTime initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (qSource j : ℕ)) tail)
          (tilingPartner t b.1.1) + (ellSource b : ℕ) < m)
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
    thresholdCount_prefixedTilingInsertion_add_of_broadEndpointIncrement
      initial t x r tail D upper hm qSource qReplacement ellSource
        ellReplacement hstart hdist hsourceBelow htotalSource
        htotalReplacement
  have hendpoint :=
    prefixedTilingFinalLocalTime_eq_of_broadSourceCoordinates
      initial t x r tail D upper hk cutoff qSource qReplacement ellSource
        hstart hdist hsourceBelow htotalSource hlt haccepted
  exact prefixedTilingStoppingAccepted_of_thresholdCount_add_of_endpointLocal
    initial t x m k delta cutoff hm hk r tail qSource qReplacement
      hcount hendpoint hpos hpos' hlt hlt' haccepted

end

end Erdos1165.TilingBroadSourceSlotActualDeltaAcceptedCreation
