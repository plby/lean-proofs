/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairExternalIndexRecovery
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairActualDeltaSelected
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalCoordinateRecovery
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceSlotAcceptedPath

/-!
# Physical coordinates on the exact external adjacent-pair fibre

The positive-interface pair selector changes which retained dominoes are
distinguished, but it does not change the represented external word.  This
file records the corresponding physical local-time identity directly on the
external pair fibre and transports physical shell cardinalities to its away
coordinates.  No probability estimate is used.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfaceExternalPairCoordinateRecovery

open HLOZDominantPositiveInterfaceSupportSelector
open HLOZPositiveInterfacePairExternalIndexRecovery
open HLOZPositiveInterfacePairActualDeltaSelected
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfacePhysicalCoordinateRecovery
open HLOZPositiveInterfacePhysicalWindows
open HLOZPositiveInterfaceSupportSelector
open HLOZSourceOrientedThetaSourceSlotAcceptedPath
open HLOZPathEvents
open LazyDecomposition NearFavoriteShells PathInsertion PreStoppingFiber
open PreStoppingSpatialLaw StoppedInsertion
open TilingCappedMarginalization
open TilingInsertedLocalTime
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedPrefixedBoundarySourceLocalTime
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open TilingLazyDecomposition
open TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- Retained multiplicity is bounded by the larger fixed endpoint boundary
local time on an external pair history. -/
theorem positiveInterfaceExternalPairCoordinateCount_le_fixedBoundaryDominoMax
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 1 < m) (hk : 0 < k)
    (b : TilingExternalDomino t eta.1.1.start eta.1.1.retained) :
    Fintype.card
        (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b) ≤
      prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained (positiveInterfaceExternalPairTerminal eta) b := by
  classical
  let etaExternal :
      TilingOrientedAllRepresentedExternalFiber.SupportedIndex t o m k :=
    ⟨eta.1.1, by
      rcases eta.2 with ⟨s, hs⟩
      rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
      exact ⟨s, hs.1, hs.2.1, hs.2.2.1⟩⟩
  have hcard := prefixedBoundaryLocalTime_orientedEndpoint_eq_coordinateCard
    etaExternal hm hk (fun _ ↦ 0) b
  have hcard' :
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
          (orientedDominoEndpoint t o b.1) =
        Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b) := by
    simpa only [etaExternal, positiveInterfaceExternalPairTerminal] using hcard
  rw [← hcard']
  unfold prefixedTilingFixedBoundaryDominoMax orientedDominoEndpoint
  split_ifs
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _

/-- If the orientation-selected physical endpoint is dominant on the fixed
external word, then the domino boundary is exactly the retained coordinate
multiplicity.  This is the prefix-level form of the reason HLOZ normalize
candidate sites to dominant endpoints before applying the insertion product. -/
theorem positiveInterfaceExternalPairFixedBoundaryDominoMax_eq_coordinateCount_of_orientedDominant
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 1 < m) (hk : 0 < k)
    (b : TilingExternalDomino t eta.1.1.start eta.1.1.retained)
    (hdominant :
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
          (tilingPartner t (orientedDominoEndpoint t o b.1)) ≤
        prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
          (orientedDominoEndpoint t o b.1)) :
    prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained (positiveInterfaceExternalPairTerminal eta) b =
      Fintype.card
        (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b) := by
  let etaExternal :
      TilingOrientedAllRepresentedExternalFiber.SupportedIndex t o m k :=
    ⟨eta.1.1, by
      rcases eta.2 with ⟨s, hs⟩
      rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
      exact ⟨s, hs.1, hs.2.1, hs.2.2.1⟩⟩
  have hcard :
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
          (orientedDominoEndpoint t o b.1) =
        Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b) := by
    simpa only [etaExternal, positiveInterfaceExternalPairTerminal] using
      (prefixedBoundaryLocalTime_orientedEndpoint_eq_coordinateCard
        etaExternal hm hk (fun _ ↦ 0) b)
  unfold prefixedTilingFixedBoundaryDominoMax
  by_cases hb : SpatialInsertionFiber.OrientationCompatible o b.1
  · rw [orientedDominoEndpoint, if_pos hb] at hdominant hcard
    exact (max_eq_left hdominant).trans hcard
  · rw [orientedDominoEndpoint, if_neg hb, tilingPartner_partner] at hdominant
    rw [orientedDominoEndpoint, if_neg hb] at hcard
    exact (max_eq_right hdominant).trans hcard

/-- Every exposed coordinate in the normalized pair support is already
oriented toward the dominant fixed-boundary endpoint. -/
theorem positiveInterfaceExternalPairCoordinate_dominant
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) :
    prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
          (tilingPartner t (orientedDominoEndpoint t o b.1.1)) ≤
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
          (orientedDominoEndpoint t o b.1.1) := by
  classical
  have hbS : b.1.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b.1).1 b.2
  rcases eta.2 with ⟨s, hs⟩
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
  let n := creationTimeNat m k s
  have hbPair : b.1.1 ∈ orientedDominantPositiveInterfacePairSupportAt
      t o m externalThreshold width shell s n := by
    change b.1.1 ∈ PositiveInterfacePairSupportAt t o m
      externalThreshold width shell s n
    dsimp only [n]
    rw [hs.2.2.2]
    exact hbS
  have hdominant := orientedEndpointDominantAt_of_mem_pairSupport hbPair
  unfold orientedEndpointDominantAt at hdominant
  rw [hs.2.2.1] at hdominant
  exact hdominant

/-- Dominant endpoint normalization makes the exact prefix-boundary margin
automatic in every positive shell (including shell zero). -/
theorem positiveInterfaceExternalPairBoundary_lt_of_orientedDominant
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 1 < m) (hk : 0 < k)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (hdominant :
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
          (tilingPartner t (orientedDominoEndpoint t o b.1.1)) ≤
        prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
          (orientedDominoEndpoint t o b.1.1)) :
    prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained (positiveInterfaceExternalPairTerminal eta) b.1 <
      Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) +
        max 1 (shell * width) := by
  rw [positiveInterfaceExternalPairFixedBoundaryDominoMax_eq_coordinateCount_of_orientedDominant
    eta hm hk b.1 hdominant]
  have hpos : 0 < max 1 (shell * width) :=
    Nat.zero_lt_one.trans_le (Nat.le_max_left _ _)
  omega

/-- On the normalized pair support the exact prefix-boundary margin is
automatic, with no residual structural obstruction. -/
theorem positiveInterfaceExternalPairBoundary_lt
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 1 < m) (hk : 0 < k)
    (b : PositiveInterfaceExternalPairCoordinate eta) :
    prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained (positiveInterfaceExternalPairTerminal eta) b.1 <
      Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) +
        max 1 (shell * width) :=
  positiveInterfaceExternalPairBoundary_lt_of_orientedDominant eta hm hk b
    (positiveInterfaceExternalPairCoordinate_dominant eta b)

/-- The honest pair base window is contained in the retained-count accepted
range. -/
theorem positiveInterfaceExternalPairBaseWindow_subset_coordinateRange
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 1 < m) (hk : 0 < k) (cap : ℕ)
    (b : PositiveInterfaceExternalPairCoordinate eta) :
    positiveInterfaceExternalPairBaseWindow eta cap b ⊆ Finset.range
      (m - Fintype.card
        (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) := by
  intro v hv
  unfold positiveInterfaceExternalPairBaseWindow at hv
  rw [Finset.mem_range] at hv ⊢
  exact hv.trans_le (Nat.sub_le_sub_left
    (positiveInterfaceExternalPairCoordinateCount_le_fixedBoundaryDominoMax
      eta hm hk b.1) m)

/-- The exact pair support excludes every retained domino already meeting
level `m`; hence both endpoints of each exposed domino remain strictly below
`m` on the canonical accepted source vector. -/
theorem positiveInterfaceExternalPairCanonical_strictAway
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell cap : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 1 < m)
    (q : TilingCappedCoordinates eta.1.1.retainedCount cap)
    (hcanonical : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t eta.1.1.start
        eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1))) ∈
      orientedExternalAllCreationSupportTraceAtom t o m k
        (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
        eta.1.1 eta.1.2)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (externalCoordinateCutoff eta.1.1 cap))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.tail.1) :
    ∀ b : TilingExternalDomino t eta.1.1.start eta.1.1.retained,
      b.1 ∉ supportComplementDistinguished t eta.1.1.start
          eta.1.1.retained eta.1.2 →
        prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1 eta.1.1.start
            eta.1.1.retained (positiveInterfaceExternalPairTerminal eta) b +
          tilingDominoTotal t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) b < m := by
  classical
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hcanonical
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  have hlt : v.length < externalCoordinateCutoff eta.1.1 cap := by
    let dummy : TilingCreationFavoriteData :=
      ((∅, ∅), (eta.1.1.start, eta.1.1.start))
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) cap q
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hcreation : ThresholdCreation s m k v.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff m k
      (externalCoordinateCutoff eta.1.1 cap) v.length _ hlt).mp haccepted
  have htime : creationTimeNat m k s = v.length :=
    creationTimeNat_eq_of_creation hcreation
  have hsupport : PositiveInterfacePairSupportAt t o m externalThreshold
      width shell s v.length = eta.1.2 := by
    rw [← htime]
    exact hcanonical.2.2.2
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath eta.1.1.initial.1 eta.1.1.start
        (tilingInsertGapVector t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)))
        (positiveInterfaceExternalPairTerminal eta) := by
    rw [← positiveInterfaceExternalPairTerminal_eq_coordinates eta
      (fun j ↦ (q j : ℕ))]
    exact finitePathList_prefixedTilingInsertionPrefix eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail rfl
  intro b hbAway
  have hbS : b.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b).1
      hbAway
  have hbPair : b.1 ∈ PositiveInterfacePairSupportAt t o m
      externalThreshold width shell s v.length := by
    rw [hsupport]
    exact hbS
  have hbRaw := orientedDominantPositiveInterfacePairSupportAt_subset_raw
    t o m externalThreshold width shell s v.length hbPair
  have hbSupport := orientedPositiveInterfacePairSupportAt_subset t o m
    externalThreshold width shell s v.length hbRaw
  have hbNotThreshold : b.1 ∉
      (thresholdSites s v.length m).image (tilingBase t) := by
    unfold orientedPositiveInterfaceSupportAt at hbSupport
    exact (Finset.mem_filter.mp hbSupport).2.2
  have hbaseLt : localTime s v.length b.1 < m := by
    by_contra hnot
    apply hbNotThreshold
    rw [Finset.mem_image]
    exact ⟨b.1, (mem_thresholdSites_iff s v.length m b.1 (by omega)).2
      (Nat.le_of_not_gt hnot),
      tilingExternalDomino_isBase t eta.1.1.start eta.1.1.retained b⟩
  have hpartnerLt : localTime s v.length (tilingPartner t b.1) < m := by
    by_contra hnot
    apply hbNotThreshold
    rw [Finset.mem_image]
    refine ⟨tilingPartner t b.1,
      (mem_thresholdSites_iff s v.length m (tilingPartner t b.1)
        (by omega)).2 (Nat.le_of_not_gt hnot), ?_⟩
    rw [tilingBase_partner]
    exact tilingExternalDomino_isBase t eta.1.1.start eta.1.1.retained b
  have hbase : localTime s v.length b.1 =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta) b.1 +
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) b := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) (positiveInterfaceExternalPairTerminal eta)
        b b.1]
    exact tilingExternalDomino_isBase t eta.1.1.start eta.1.1.retained b
  have hpartner : localTime s v.length (tilingPartner t b.1) =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
          (tilingPartner t b.1) +
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) b := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) (positiveInterfaceExternalPairTerminal eta)
        b (tilingPartner t b.1)]
    exact tilingPartner_ofExternalDomino_has_base t eta.1.1.start
      eta.1.1.retained b
  unfold prefixedTilingFixedBoundaryDominoMax
  rw [show max
      (prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained (positiveInterfaceExternalPairTerminal eta) b.1)
      (prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
          (tilingPartner t b.1)) +
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) b =
      max
        (prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta) b.1 +
          tilingDominoTotal t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) b)
        (prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
            (tilingPartner t b.1) +
          tilingDominoTotal t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) b) by omega,
    max_lt_iff]
  exact ⟨hbase ▸ hbaseLt, hpartner ▸ hpartnerLt⟩

/-- On the canonical prefixed insertion represented by an external pair
history, the physical oriented endpoint local time is the retained
multiplicity plus the away insertion total. -/
theorem positiveInterfaceExternalPairCanonical_orientedEndpointLocalTime_eq
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 1 < m) (hk : 0 < k) {cap : ℕ}
    (q : TilingCappedCoordinates eta.1.1.retainedCount cap)
    (b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2)) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    localTime s v.length (orientedDominoEndpoint t o b.1.1) =
      Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) +
        tilingAwayTotal t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2)
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2) q).2) b := by
  classical
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let terminal := prefixedTilingInsertionTerminal eta.1.1.initial t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath eta.1.1.initial.1 eta.1.1.start
        (tilingInsertGapVector t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ))) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail rfl
  have hbBase : IsTilingBase t b.1.1 :=
    isTilingBase_of_tilingBase_eq_self t b.1.1
      (tilingExternalDomino_is_base t eta.1.1.start eta.1.1.retained b.1)
  have hlocal : localTime s v.length
        (orientedDominoEndpoint t o b.1.1) =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained terminal (orientedDominoEndpoint t o b.1.1) +
        tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) b.1 := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) terminal b.1
        (orientedDominoEndpoint t o b.1.1)]
    exact tilingBase_orientedDominoEndpoint t o b.1.1 hbBase
  have hboundary : prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1
        eta.1.1.start eta.1.1.retained terminal
        (orientedDominoEndpoint t o b.1.1) =
      Fintype.card
        (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) := by
    let etaExternal :
        TilingOrientedAllRepresentedExternalFiber.SupportedIndex t o m k :=
      ⟨eta.1.1, by
        rcases eta.2 with ⟨s0, hs0⟩
        rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs0
        exact ⟨s0, hs0.1, hs0.2.1, hs0.2.2.1⟩⟩
    exact prefixedBoundaryLocalTime_orientedEndpoint_eq_coordinateCard
      etaExternal hm hk (fun j ↦ (q j : ℕ)) b.1
  change localTime s v.length (orientedDominoEndpoint t o b.1.1) = _
  rw [hlocal, hboundary,
    tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2) q b]

/-- The same identity on a physical path sharing the represented stopped
prefix. -/
theorem positiveInterfaceExternalPair_orientedEndpointLocalTime_eq_of_pathPrefix
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 1 < m) (hk : 0 < k) {cap : ℕ}
    (q : TilingCappedCoordinates eta.1.1.retainedCount cap)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (s : WalkPath)
    (hprefix :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
      let sq := trajectory (extendPrefix (directionVectorOfList v))
      pathPrefix s v.length = pathPrefix sq v.length) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
    localTime s v.length (orientedDominoEndpoint t o b.1.1) =
      Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) +
        tilingAwayTotal t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2)
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2) q).2) b := by
  classical
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  change localTime s v.length (orientedDominoEndpoint t o b.1.1) = _
  have hlocal : localTime s v.length (orientedDominoEndpoint t o b.1.1) =
      localTime sq v.length (orientedDominoEndpoint t o b.1.1) := by
    rw [localTime_eq_listLocalTime, localTime_eq_listLocalTime, hprefix]
  rw [hlocal]
  exact positiveInterfaceExternalPairCanonical_orientedEndpointLocalTime_eq
    eta hm hk q b

/-- A pair away total is in a physical failure window exactly when the
corresponding oriented endpoint has the displayed deficit-shell label. -/
theorem positiveInterfaceExternalPair_awayTotal_mem_physicalWindow_iff
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold pairWidth pairShell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold pairWidth pairShell)
    (hm : 1 < m) (hk : 0 < k) {cap : ℕ}
    (q : TilingCappedCoordinates eta.1.1.retainedCount cap)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (s : WalkPath)
    (hprefix :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
      let sq := trajectory (extendPrefix (directionVectorOfList v))
      pathPrefix s v.length = pathPrefix sq v.length)
    (hbelow :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
      localTime s v.length (orientedDominoEndpoint t o b.1.1) < m)
    (width shell : ℕ) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
    tilingAwayTotal t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2)
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start
            eta.1.1.retained eta.1.2) q).2) b ∈
      physicalDeficitFailureWindow m width
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell ↔
      (m - localTime s v.length (orientedDominoEndpoint t o b.1.1)) /
        width = shell := by
  classical
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
  have hlocal :=
    positiveInterfaceExternalPair_orientedEndpointLocalTime_eq_of_pathPrefix
      eta hm hk q b s hprefix
  rw [mem_physicalDeficitFailureWindow]
  let a := tilingAwayTotal t eta.1.1.start eta.1.1.retained
    (supportComplementDistinguished t eta.1.1.start eta.1.1.retained eta.1.2)
    ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2) q).2) b
  let i := Fintype.card
    (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)
  change localTime s v.length (orientedDominoEndpoint t o b.1.1) = i + a at hlocal
  change localTime s v.length (orientedDominoEndpoint t o b.1.1) < m at hbelow
  change (a < m + 1 ∧ (m - (i + a)) / width = shell) ↔
    (m - localTime s v.length (orientedDominoEndpoint t o b.1.1)) /
      width = shell
  rw [hlocal] at hbelow ⊢
  constructor
  · exact fun h ↦ h.2
  · intro hshell
    exact ⟨by omega, hshell⟩

/-- Physical shell occupancy is exactly the corresponding away-window
cardinality on an exact external pair history. -/
theorem card_positiveInterfaceExternalPairPhysicalShell_eq_awayWindow
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold pairWidth pairShell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold pairWidth pairShell)
    (hm : 1 < m) (hk : 0 < k) {cap : ℕ}
    (q : TilingCappedCoordinates eta.1.1.retainedCount cap)
    (s : WalkPath)
    (hprefix :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
      let sq := trajectory (extendPrefix (directionVectorOfList v))
      pathPrefix s v.length = pathPrefix sq v.length)
    (hvalid : s ∈ validStepWalk)
    (hpositive :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
      0 < v.length)
    (hfavorite :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
      thresholdSites s v.length m = favoriteSites s v.length)
    (hsupport :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
      PositiveInterfacePairSupportAt t o m externalThreshold pairWidth
        pairShell s v.length = eta.1.2)
    (hthreshold : 0 < externalThreshold)
    (hbelow :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
      ∀ b : PositiveInterfaceExternalPairCoordinate eta,
        localTime s v.length (orientedDominoEndpoint t o b.1.1) < m)
    (width shell : ℕ) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
    (shellCandidates
      (orientedDominantPositiveInterfacePhysicalPairSites t o m
        externalThreshold pairWidth pairShell s v.length)
      (fun x ↦ (m - localTime s v.length x) / width) shell).card =
    (Finset.univ.filter fun b : PositiveInterfaceExternalPairCoordinate eta ↦
      tilingAwayTotal t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2)
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start
            eta.1.1.retained eta.1.2) q).2) b ∈
      physicalDeficitFailureWindow m width
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell).card := by
  classical
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
  change _ = _
  have hsites :
      orientedDominantPositiveInterfacePhysicalPairSites t o m
          externalThreshold pairWidth pairShell s v.length =
        (PositiveInterfacePairSupportAt t o m externalThreshold pairWidth
          pairShell s v.length).image (orientedDominoEndpoint t o) := rfl
  rw [hsupport] at hsites
  symm
  apply Finset.card_bij
    (fun b _hb ↦ orientedDominoEndpoint t o b.1.1)
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [mem_shellCandidates, hsites]
    constructor
    · rw [Finset.mem_image]
      exact ⟨b.1.1, (away_mem_support_iff t eta.1.1.start
        eta.1.1.retained eta.1.2 b.1).1 b.2, rfl⟩
    · exact
        (positiveInterfaceExternalPair_awayTotal_mem_physicalWindow_iff
          eta hm hk q b s hprefix (hbelow b) width shell).mp hb.2
  · intro b _hb c _hc hbc
    have hbBase : IsTilingBase t b.1.1 :=
      isTilingBase_of_tilingBase_eq_self t b.1.1
        (tilingExternalDomino_is_base t eta.1.1.start eta.1.1.retained b.1)
    have hcBase : IsTilingBase t c.1.1 :=
      isTilingBase_of_tilingBase_eq_self t c.1.1
        (tilingExternalDomino_is_base t eta.1.1.start eta.1.1.retained c.1)
    apply Subtype.ext
    apply Subtype.ext
    rw [← tilingBase_orientedDominoEndpoint t o b.1.1 hbBase,
      ← tilingBase_orientedDominoEndpoint t o c.1.1 hcBase, hbc]
  · intro x hx
    rw [mem_shellCandidates, hsites] at hx
    rcases hx with ⟨hxSupport, hxShell⟩
    rw [Finset.mem_image] at hxSupport
    rcases hxSupport with ⟨b, hbS, hbx⟩
    let c := supportAwayChosen t eta.1.1.start eta.1.1.retained eta.1.2
      (PositiveInterfaceExternalPairFiber eta).support_represented b hbS
    refine ⟨c, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      apply (positiveInterfaceExternalPair_awayTotal_mem_physicalWindow_iff
        eta hm hk q c s hprefix (hbelow c) width shell).mpr
      simpa only [c, supportAwayChosen_base] using hbx ▸ hxShell
    · rw [show c.1.1 = b by
        exact supportAwayChosen_base t eta.1.1.start eta.1.1.retained eta.1.2
          (PositiveInterfaceExternalPairFiber eta).support_represented b hbS]
      exact hbx

end

end Erdos1165.HLOZPositiveInterfaceExternalPairCoordinateRecovery
