/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceExternalPairCoordinateRecovery
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairActualDeltaWalkCap
import ErdosProblems.Erdos1165.HLOZPositiveInterfaceRawPhysicalReconstruction

/-!
# Raw positive-interface growth inside an external pair source cap

An early raw adjacent-row growth path canonically determines its complete
external word and exact two-row support.  Cofinal stopped-coordinate
completeness then reconstructs the same physical path in one pair source
cap.  The proof keeps the full random-total tail and the honest prefix-safe
base; it does not enlarge the event to a bare bad-coordinate witness.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfacePairSourceCapCover

open HLOZDominantPositiveInterfaceSupportSelector
open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZAllSixBandProductClosure
open HLOZDynamicThresholdedScreening
open HLOZGapRandomClockScreen HLOZPathEvents
open HLOZPositiveInterfaceExternalPairCoordinateRecovery
open HLOZPositiveInterfacePairActualDeltaCapBound
open HLOZPositiveInterfacePairActualDeltaSelected
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairExternalIndexRecovery
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfacePairWeightedScreen
open HLOZPositiveInterfacePhysicalCoordinateRecovery
open HLOZPositiveInterfacePhysicalTailRecovery
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZPositiveInterfacePhysicalWindows
open HLOZPositiveInterfaceRawPhysicalReconstruction
open HLOZPositiveInterfaceSupportSelector
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZProposition48Candidates
open HLOZTilingGapBandExtraction
open LazyDecomposition NearFavoriteShells NearFavoriteThresholded
open PathInsertion PreStoppingFiber PreStoppingSpatialLaw SpatialInsertionFiber
open StoppedInsertion
open TilingCappedMarginalization TilingInsertedLocalTime TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev DominoTiling := Tilings.Tiling

/-- Shell occupancy of all thick, outside-favorite endpoints after the
canonical-base/dominant-endpoint normalization and the endpoint-orientation
split. -/
noncomputable def dominantPositiveInterfaceBandOccupancy
    (t : DominoTiling) (o : Orientation) (m cutoff : ℕ)
    (band : RandomClockBand) : WalkPath → ℕ → ℕ :=
  fun s shell ↦
    (shellCandidates
      (orientedDominantPositiveInterfacePhysicalSites t o m
        band.externalThreshold s
          (pathTruncatedLevelTime m band.oldRank cutoff s))
      (fun x ↦ (m - localTime s
        (pathTruncatedLevelTime m band.oldRank cutoff s) x) / shellWidth48 m)
      shell).card

private theorem shellCandidates_pairSites_eq
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell : ℕ) (s : WalkPath) (n : ℕ)
    (j : ℕ) (hj : j = shell ∨ j = shell + 1) :
    shellCandidates
        (orientedDominantPositiveInterfacePhysicalPairSites t o m
          externalThreshold width shell s n)
        (fun x ↦ (m - localTime s n x) / width) j =
      shellCandidates
        (orientedDominantPositiveInterfacePhysicalSites t o m
          externalThreshold s n)
        (fun x ↦ (m - localTime s n x) / width) j := by
  exact shellCandidates_dominantPairSites_eq t o m externalThreshold
    width shell s n j hj

/-- The canonical external-pair source cap attached to an early physical
adjacent-row growth path, retaining the equality of its external word with
the path's stopped external code. -/
theorem exists_positiveInterfaceExternalPairSourceCap_of_raw_growth
    {t : DominoTiling} {o : Orientation} {m cutoff n : ℕ}
    {band : RandomClockBand}
    {threshold : ℕ → ℕ} {shell : ℕ} {s : WalkPath}
    (hm : 1 < m)
    (hphase : band.vertexPhase = false)
    (hthreshold : 0 < band.externalThreshold)
    (hcreation : ThresholdCreation s m band.oldRank n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hclock : n ≤ cutoff)
    (hvalid : s ∈ validStepWalk)
    (hfailure : s ∈ thresholdedGrowthFailure
      (dominantPositiveInterfaceBandOccupancy t o m cutoff band)
        threshold shellGrowth48 shell) :
    ∃ eta : PositiveInterfaceExternalPairSupportedIndex t o m
        band.oldRank band.externalThreshold (shellWidth48 m) shell,
      ∃ cap : ℕ,
        eta.1.1 = fixedOrientedTypedExternalWordCode t o
            (creationTimeNat m band.oldRank s) s ∧
          s ∈ positiveInterfaceExternalPairSourceCap eta cap threshold
            cutoff := by
  classical
  have hn : 0 < n := by
    have hcreation' : ThresholdCreation (trajectory (stepsOfWalk s)) m
        band.oldRank n := by
      rw [show trajectory (stepsOfWalk s) = s from hvalid]
      exact hcreation
    exact HLOZThetaOneSourceShift.thresholdCreation_time_pos_of_two_le
      (stepsOfWalk s) (by omega) band.oldRank_pos hcreation'
  have hreach : ReachesThreshold s m band.oldRank := ⟨n, hcreation.1⟩
  let eta := positiveInterfaceExternalPairSupportedIndexOfPath t
    o m band.oldRank band.externalThreshold (shellWidth48 m)
      shell s hvalid hreach
  have hatom := mem_externalPairAtom_ofPath t o m
    band.oldRank band.externalThreshold (shellWidth48 m) shell s hvalid hreach
  have hcomplete := (PositiveInterfaceExternalPairFiber eta).atom_complete hatom
  rcases Set.mem_iUnion.mp hcomplete with ⟨cap, hcap⟩
  rcases hcap with ⟨hvalid', hfiber⟩
  rcases Set.mem_iUnion.mp hfiber with ⟨qacc, hqstop⟩
  rcases qacc with ⟨q, hpred, haccepted⟩
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail.1
  have hstopTime : (PositiveInterfaceExternalPairFiber eta).stoppingTime cap
      (stepsOfWalk s) = v.length := hqstop.1
  have hvlt : v.length < externalCoordinateCutoff eta.1.1
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap) := by
    let dummy : TilingCreationFavoriteData :=
      ((∅, ∅), (eta.1.1.start, eta.1.1.start))
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy)
        ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap) q
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hcreationV : ThresholdCreation s m band.oldRank v.length := by
    have hraw : ThresholdCreation (trajectory (stepsOfWalk s)) m
        band.oldRank v.length :=
      (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff m
        band.oldRank
        (externalCoordinateCutoff eta.1.1
          ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap))
        v.length (stepsOfWalk s) hvlt).mp hstopTime
    rw [show trajectory (stepsOfWalk s) = s from hvalid] at hraw
    exact hraw
  have hvn : v.length = n :=
    HLOZSpatialAdapter.thresholdCreation_time_unique hcreationV hcreation
  have hcreationNat : creationTimeNat m band.oldRank s = n :=
    creationTimeNat_eq_of_creation hcreation
  have hprefix : pathPrefix s v.length =
      pathPrefix (trajectory (extendPrefix (directionVectorOfList v)))
        v.length := by
    have hstep : stepPrefix v.length (stepsOfWalk s) =
        directionVectorOfList v :=
      (incrementPrefixList_eq_iff_stepPrefix_eq_directionVector
        (stepsOfWalk s) v).mp hqstop.2
    calc
      pathPrefix s v.length =
          trajectoryPrefix (stepPrefix v.length (stepsOfWalk s)) := by
        rw [trajectoryPrefix_stepPrefix, hvalid]
      _ = trajectoryPrefix (directionVectorOfList v) := congrArg _ hstep
      _ = trajectoryPrefix
          (stepPrefix v.length (extendPrefix (directionVectorOfList v))) := by
        rw [stepPrefix_extendPrefix]
      _ = pathPrefix
          (trajectory (extendPrefix (directionVectorOfList v))) v.length :=
        trajectoryPrefix_stepPrefix _ _
  have hfavorite : thresholdSites s v.length m = favoriteSites s v.length := by
    rw [hvn]
    exact thresholdSites_eq_favoriteSites_at_creation_of_terminal
      band.oldRank_pos hcreation le_rfl hnext
  have hsupport : PositiveInterfacePairSupportAt t o m
      band.externalThreshold (shellWidth48 m) shell s v.length = eta.1.2 := by
    simp only [eta,
      positiveInterfaceExternalPairSupportedIndexOfPath_support]
    rw [hvn, hcreationNat]
  have hpredExternal := hpred
  have hstrict : ∀ b : TilingExternalDomino t eta.1.1.start
      eta.1.1.retained,
      b.1 ∉ supportComplementDistinguished t eta.1.1.start
          eta.1.1.retained eta.1.2 →
        prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1 eta.1.1.start
            eta.1.1.retained (positiveInterfaceExternalPairTerminal eta) b +
          tilingDominoTotal t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) b < m := by
    have hpath : finitePathList (pathPrefix s v.length) =
        prefixedTilingPrefixPointPath eta.1.1.initial.1 eta.1.1.start
          (tilingInsertGapVector t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)))
          (positiveInterfaceExternalPairTerminal eta) := by
      calc
        finitePathList (pathPrefix s v.length) =
            finitePathList (pathPrefix
              (trajectory (extendPrefix (directionVectorOfList v)))
                v.length) := congrArg finitePathList hprefix
        _ = prefixedTilingPrefixPointPath eta.1.1.initial.1 eta.1.1.start
            (tilingInsertGapVector t eta.1.1.start eta.1.1.retained
              (fun j ↦ (q j : ℕ)))
            (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
              eta.1.1.retained (fun j ↦ (q j : ℕ)) eta.1.1.tail) :=
          finitePathList_prefixedTilingInsertionPrefix eta.1.1.initial t
            eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
              eta.1.1.tail rfl
        _ = _ := by
          rw [positiveInterfaceExternalPairTerminal_eq_coordinates eta]
    intro b hbAway
    have hbS : b.1 ∈ eta.1.2 :=
      (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b).1
        hbAway
    have hbPair : b.1 ∈ PositiveInterfacePairSupportAt t o m
        band.externalThreshold (shellWidth48 m) shell s v.length := by
      rw [hsupport]
      exact hbS
    have hbRaw := orientedDominantPositiveInterfacePairSupportAt_subset_raw
      t o m band.externalThreshold (shellWidth48 m) shell s v.length hbPair
    have hbSupport := orientedPositiveInterfacePairSupportAt_subset t
      o m band.externalThreshold (shellWidth48 m) shell s v.length hbRaw
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
  let D := supportComplementDistinguished t eta.1.1.start eta.1.1.retained
    eta.1.2
  let a := (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D
    q).2
  let ell : TruncatedTotals
      ((PositiveInterfaceExternalPairFiber eta).upper cap) :=
    fun b ↦ ⟨tilingAwayTotal t eta.1.1.start eta.1.1.retained D a b, by
      have hb := hstrict b.1 b.2
      have htotal : tilingDominoTotal t eta.1.1.start eta.1.1.retained
          (fun j ↦ (q j : ℕ)) b.1 =
        tilingAwayTotal t eta.1.1.start eta.1.1.retained D a b :=
        (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
          eta.1.1.retained D q b).symm
      rw [htotal] at hb
      change tilingAwayTotal t eta.1.1.start eta.1.1.retained D a b <
        max eta.1.1.retainedCount (m + shellWidth48 m) + 1
      omega⟩
  let : Fintype (PositiveInterfaceExternalPairCoordinate eta) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
  have huniv :
      (@Finset.univ (PositiveInterfaceExternalPairCoordinate eta) this) =
        (@Finset.univ (PositiveInterfaceExternalPairCoordinate eta)
          (Subtype.fintype _)) := by
    ext b
    simp only [Finset.mem_univ]
  have hbase : positiveInterfaceExternalPairBaseProp eta cap ell := by
    intro b
    unfold positiveInterfaceExternalPairBaseWindow ell
    rw [Finset.mem_range]
    have hb := hstrict b.1 b.2
    have htotal : tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) b.1 =
      tilingAwayTotal t eta.1.1.start eta.1.1.retained D a b :=
      (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
        eta.1.1.retained D q b).symm
    exact Nat.lt_sub_of_add_lt (by simpa only [htotal, Nat.add_comm] using hb)
  have hbelow : ∀ b : PositiveInterfaceExternalPairCoordinate eta,
      localTime s v.length
        (orientedDominoEndpoint t o b.1.1) < m := by
    intro b
    have hphysical :=
      positiveInterfaceExternalPair_orientedEndpointLocalTime_eq_of_pathPrefix
        eta hm band.oldRank_pos q b s hprefix
    have hb := hstrict b.1 b.2
    have hcard :=
      positiveInterfaceExternalPairCoordinateCount_le_fixedBoundaryDominoMax
        eta hm band.oldRank_pos b.1
    have htotal : tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) b.1 =
      tilingAwayTotal t eta.1.1.start eta.1.1.retained D a b :=
      (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
        eta.1.1.retained D q b).symm
    rw [hphysical]
    exact lt_of_le_of_lt (Nat.add_le_add_right hcard _)
      (by simpa only [htotal] using hb)
  have hclockEq : pathTruncatedLevelTime m band.oldRank cutoff s = n :=
    pathTruncatedLevelTime_eq_of_creation_le_cutoff hcreation hclock
  have hrawLower :
      dominantPositiveInterfaceBandOccupancy t o m cutoff band s shell =
        (shellCandidates
          (orientedDominantPositiveInterfacePhysicalSites t o m
            band.externalThreshold s n)
          (fun x ↦ (m - localTime s n x) / shellWidth48 m) shell).card := by
    unfold dominantPositiveInterfaceBandOccupancy
    rw [hclockEq]
  have hrawUpper :
      dominantPositiveInterfaceBandOccupancy t o m cutoff band s (shell + 1) =
        (shellCandidates
          (orientedDominantPositiveInterfacePhysicalSites t o m
            band.externalThreshold s n)
          (fun x ↦ (m - localTime s n x) / shellWidth48 m)
            (shell + 1)).card := by
    unfold dominantPositiveInterfaceBandOccupancy
    rw [hclockEq]
  have hpairLower := shellCandidates_pairSites_eq t o m
    band.externalThreshold (shellWidth48 m) shell s n shell (Or.inl rfl)
  have hpairUpper := shellCandidates_pairSites_eq t o m
    band.externalThreshold (shellWidth48 m) shell s n (shell + 1)
      (Or.inr rfl)
  have hvpos : 0 < v.length := by omega
  have hlowerPhysical :=
    card_positiveInterfaceExternalPairPhysicalShell_eq_awayWindow eta hm
      band.oldRank_pos q s hprefix hvalid hvpos hfavorite hsupport hthreshold
      hbelow (shellWidth48 m) shell
  have hupperPhysical :=
    card_positiveInterfaceExternalPairPhysicalShell_eq_awayWindow eta hm
      band.oldRank_pos q s hprefix hvalid hvpos hfavorite hsupport hthreshold
      hbelow (shellWidth48 m) (shell + 1)
  have hupperFilter :
      (Finset.univ.filter fun b : PositiveInterfaceExternalPairCoordinate eta ↦
        positiveInterfaceExternalPairUpper eta cap b (ell b)) =
      (Finset.univ.filter fun b : PositiveInterfaceExternalPairCoordinate eta ↦
        tilingAwayTotal t eta.1.1.start eta.1.1.retained D a b ∈
          physicalDeficitFailureWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            (shell + 1)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hsafe := positiveInterfaceExternalPairBaseWindow_subset_coordinateRange
      eta hm band.oldRank_pos cap b (hbase b)
    rw [Finset.mem_range] at hsafe
    dsimp only [ell] at hsafe ⊢
    unfold positiveInterfaceExternalPairUpper
    rw [mem_acceptedPhysicalDeficitFailureWindow,
      mem_physicalDeficitFailureWindow]
    constructor
    · rintro ⟨haccepted, _hbase⟩
      exact ⟨by omega, haccepted.2⟩
    · rintro ⟨_hupper, hshellLabel⟩
      have hacceptedLt : Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) +
          tilingAwayTotal t eta.1.1.start eta.1.1.retained D a b < m := by
        rw [Nat.add_comm]
        exact Nat.lt_sub_iff_add_lt.mp hsafe
      exact ⟨⟨hacceptedLt, hshellLabel⟩, hbase b⟩
  have hlowerFilter :
      (Finset.univ.filter fun b : PositiveInterfaceExternalPairCoordinate eta ↦
        positiveInterfaceExternalPairLower eta cap b (ell b)) =
      (Finset.univ.filter fun b : PositiveInterfaceExternalPairCoordinate eta ↦
        tilingAwayTotal t eta.1.1.start eta.1.1.retained D a b ∈
          physicalDeficitFailureWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            shell) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hsafe := positiveInterfaceExternalPairBaseWindow_subset_coordinateRange
      eta hm band.oldRank_pos cap b (hbase b)
    rw [Finset.mem_range] at hsafe
    dsimp only [ell] at hsafe ⊢
    unfold positiveInterfaceExternalPairLower
    rw [mem_acceptedPhysicalDeficitFailureWindow,
      mem_physicalDeficitFailureWindow]
    constructor
    · intro haccepted
      exact ⟨by omega, haccepted.2⟩
    · rintro ⟨_hupper, hshellLabel⟩
      have hacceptedLt : Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) +
          tilingAwayTotal t eta.1.1.start eta.1.1.retained D a b < m := by
        rw [Nat.add_comm]
        exact Nat.lt_sub_iff_add_lt.mp hsafe
      exact ⟨hacceptedLt, hshellLabel⟩
  have hupperCard :
      (Finset.univ.filter fun b : PositiveInterfaceExternalPairCoordinate eta ↦
        positiveInterfaceExternalPairUpper eta cap b (ell b)).card =
      dominantPositiveInterfaceBandOccupancy t o m cutoff band s
        (shell + 1) := by
    rw [hupperFilter]
    calc
      _ = (shellCandidates
          (orientedDominantPositiveInterfacePhysicalPairSites t o m
            band.externalThreshold (shellWidth48 m) shell s v.length)
          (fun x ↦ (m - localTime s v.length x) / shellWidth48 m)
          (shell + 1)).card := by
        symm
        rw [huniv]
        simpa only [D, a] using hupperPhysical
      _ = (shellCandidates
          (orientedDominantPositiveInterfacePhysicalPairSites t o m
            band.externalThreshold (shellWidth48 m) shell s n)
          (fun x ↦ (m - localTime s n x) / shellWidth48 m)
          (shell + 1)).card := by rw [hvn]
      _ = (shellCandidates
          (orientedDominantPositiveInterfacePhysicalSites t o m
            band.externalThreshold s n)
          (fun x ↦ (m - localTime s n x) / shellWidth48 m)
          (shell + 1)).card := congrArg Finset.card hpairUpper
      _ = dominantPositiveInterfaceBandOccupancy t o m cutoff band s
          (shell + 1) := hrawUpper.symm
  have hlowerCard :
      (Finset.univ.filter fun b : PositiveInterfaceExternalPairCoordinate eta ↦
        positiveInterfaceExternalPairLower eta cap b (ell b)).card =
      dominantPositiveInterfaceBandOccupancy t o m cutoff band s shell := by
    rw [hlowerFilter]
    calc
      _ = (shellCandidates
          (orientedDominantPositiveInterfacePhysicalPairSites t o m
            band.externalThreshold (shellWidth48 m) shell s v.length)
          (fun x ↦ (m - localTime s v.length x) / shellWidth48 m)
          shell).card := by
        symm
        rw [huniv]
        simpa only [D, a] using hlowerPhysical
      _ = (shellCandidates
          (orientedDominantPositiveInterfacePhysicalPairSites t o m
            band.externalThreshold (shellWidth48 m) shell s n)
          (fun x ↦ (m - localTime s n x) / shellWidth48 m)
          shell).card := by rw [hvn]
      _ = (shellCandidates
          (orientedDominantPositiveInterfacePhysicalSites t o m
            band.externalThreshold s n)
          (fun x ↦ (m - localTime s n x) / shellWidth48 m)
          shell).card := congrArg Finset.card hpairLower
      _ = dominantPositiveInterfaceBandOccupancy t o m cutoff band s shell :=
        hrawLower.symm
  have hpairs :
      dominantPositiveInterfaceBandOccupancy t o m cutoff band s shell +
          dominantPositiveInterfaceBandOccupancy t o m cutoff band s
            (shell + 1) ≤
        (orientedDominantPositiveInterfacePhysicalSites t o m
          band.externalThreshold s n).card := by
    rw [hrawLower, hrawUpper]
    have hdisjoint : Disjoint
        (shellCandidates
          (orientedDominantPositiveInterfacePhysicalSites t o m
            band.externalThreshold s n)
          (fun x ↦ (m - localTime s n x) / shellWidth48 m) shell)
        (shellCandidates
          (orientedDominantPositiveInterfacePhysicalSites t o m
            band.externalThreshold s n)
          (fun x ↦ (m - localTime s n x) / shellWidth48 m) (shell + 1)) := by
      rw [Finset.disjoint_left]
      intro x hx hxu
      rw [mem_shellCandidates] at hx hxu
      omega
    rw [← Finset.card_union_of_disjoint hdisjoint]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_union] at hx
    exact hx.elim (fun h ↦ (mem_shellCandidates.mp h).1)
      (fun h ↦ (mem_shellCandidates.mp h).1)
  have hsites :
      (orientedDominantPositiveInterfacePhysicalSites t o m
        band.externalThreshold s n).card ≤ n := by
    have hfavoriteN : thresholdSites s n m = favoriteSites s n := by
      simpa only [hvn] using hfavorite
    have hrawSites := positiveInterfacePhysicalSites_eq_support_image
      t o m band.externalThreshold s n hvalid hn hfavoriteN hthreshold
    have hsubset :
        orientedDominantPositiveInterfacePhysicalSites t o m
            band.externalThreshold s n ⊆
          positiveInterfacePhysicalSites t o band.externalThreshold s n := by
      rw [hrawSites]
      intro x hx
      rw [orientedDominantPositiveInterfacePhysicalSites,
        Finset.mem_image] at hx
      rcases hx with ⟨b, hb, rfl⟩
      rw [Finset.mem_image]
      exact ⟨b, orientedDominantPositiveInterfaceSupportAt_subset
        t o m band.externalThreshold s n hb, rfl⟩
    apply (Finset.card_le_card hsubset).trans
    unfold positiveInterfacePhysicalSites
    exact (Finset.card_filter_le _ _).trans
      (pathPhaseFilteredEndpointVisitedSites_card_le_clock t o s hn)
  have hbound :
      dominantPositiveInterfaceBandOccupancy t o m cutoff band s shell +
        dominantPositiveInterfaceBandOccupancy t o m cutoff band s
          (shell + 1) < cutoff + 1 :=
    Nat.lt_succ_of_le (hpairs.trans (hsites.trans hclock))
  have htail : randomTotalThresholdedUpperTail
      (positiveInterfaceExternalPairUpper eta cap)
      (positiveInterfaceExternalPairLower eta cap)
      threshold shellGrowth48 shell cutoff ell := by
    apply randomTotalThresholdedUpperTail_of_shell_cardinalities
      (positiveInterfaceExternalPairUpper eta cap)
      (positiveInterfaceExternalPairLower eta cap)
      threshold shellGrowth48 shell cutoff ell
      (dominantPositiveInterfaceBandOccupancy t o m cutoff band s shell)
      (dominantPositiveInterfaceBandOccupancy t o m cutoff band s (shell + 1))
    · intro b hboth
      exact positiveInterfaceExternalPairUpper_lower_disjoint eta cap b
        (ell b) hboth
    · exact hupperCard
    · exact hlowerCard
    · simpa only [thresholdedGrowthFailure, Set.mem_ofPred_eq] using hfailure
    · exact hbound
  have hpairSupport : pairSupport
      (positiveInterfaceExternalPairUpper eta cap)
      (positiveInterfaceExternalPairLower eta cap) ell = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro b
    simp only [pairSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    have hbS : b.1.1 ∈ eta.1.2 :=
      (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b.1).1
        b.2
    have hbPair : b.1.1 ∈ PositiveInterfacePairSupportAt t o m
        band.externalThreshold (shellWidth48 m) shell s v.length := by
      rw [hsupport]
      exact hbS
    change b.1.1 ∈ orientedDominantPositiveInterfacePairSupportAt t o m
      band.externalThreshold (shellWidth48 m) shell s v.length at hbPair
    rw [orientedDominantPositiveInterfacePairSupportAt,
      Finset.mem_filter] at hbPair
    have hwindow :=
      positiveInterfaceExternalPair_awayTotal_mem_physicalWindow_iff eta hm
        band.oldRank_pos q b s hprefix (hbelow b) (shellWidth48 m)
    rcases hbPair.2 with hbLower | hbUpper
    · apply Or.inr
      dsimp only [ell, D, a]
      unfold positiveInterfaceExternalPairLower
      rw [mem_acceptedPhysicalDeficitFailureWindow]
      have hlabel := (hwindow shell).mpr hbLower
      rw [mem_physicalDeficitFailureWindow] at hlabel
      have hsafe := positiveInterfaceExternalPairBaseWindow_subset_coordinateRange
        eta hm band.oldRank_pos cap b (hbase b)
      rw [Finset.mem_range] at hsafe
      dsimp only [ell, D, a] at hsafe
      have hacceptedLt : Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) +
          tilingAwayTotal t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2)
            ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
              (supportComplementDistinguished t eta.1.1.start
                eta.1.1.retained eta.1.2) q).2) b < m := by
        rw [Nat.add_comm]
        exact Nat.lt_sub_iff_add_lt.mp hsafe
      exact ⟨hacceptedLt, hlabel.2⟩
    · apply Or.inl
      dsimp only [ell, D, a]
      unfold positiveInterfaceExternalPairUpper
      refine ⟨?_, hbase b⟩
      rw [mem_acceptedPhysicalDeficitFailureWindow]
      have hlabel := (hwindow (shell + 1)).mpr hbUpper
      rw [mem_physicalDeficitFailureWindow] at hlabel
      have hsafe := positiveInterfaceExternalPairBaseWindow_subset_coordinateRange
        eta hm band.oldRank_pos cap b (hbase b)
      rw [Finset.mem_range] at hsafe
      dsimp only [ell, D, a] at hsafe
      have hacceptedLt : Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) +
          tilingAwayTotal t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2)
            ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
              (supportComplementDistinguished t eta.1.1.start
                eta.1.1.retained eta.1.2) q).2) b < m := by
        rw [Nat.add_comm]
        exact Nat.lt_sub_iff_add_lt.mp hsafe
      exact ⟨hacceptedLt, hlabel.2⟩
  have hscreen : positiveInterfaceExternalPairSourceScreen eta cap threshold
      cutoff ell := ⟨hbase, htail, hpairSupport⟩
  have hqReassemble :
      (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2)).symm
        ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
          (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
            eta.1.2) q).1, a) = q := by
    dsimp only [a, D]
    exact Equiv.symm_apply_apply _ q
  have hselected : positiveInterfaceExternalPairSelected eta cap
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained D q).1) := by
    unfold positiveInterfaceExternalPairSelected
    refine ⟨a, ell, ?_⟩
    dsimp only
    rw [hqReassemble]
    exact ⟨hpredExternal, haccepted, hbase, fun _ ↦ rfl⟩
  have hsource : positiveInterfaceExternalPairSourcePredicate eta cap
      threshold cutoff q := by
    unfold positiveInterfaceExternalPairSourcePredicate
    exact ⟨hselected, ell, hscreen, fun _ ↦ rfl⟩
  refine ⟨eta, cap, ?_, ?_⟩
  · exact positiveInterfaceExternalPairSupportedIndexOfPath_code t
      o m band.oldRank band.externalThreshold
        (shellWidth48 m) shell s hvalid hreach
  refine ⟨hvalid', ?_⟩
  let qsource : PrefixedTilingAcceptedCappedCoordinates
      (truncatedLevelTime m band.oldRank
        (externalCoordinateCutoff eta.1.1
          ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)
      eta.1.1.tail.1
      (positiveInterfaceExternalPairSourcePredicate eta cap threshold cutoff) :=
    ⟨q, hsource, haccepted⟩
  apply Set.mem_iUnion.mpr
  refine ⟨qsource, ?_⟩
  have hstopping : (PositiveInterfaceExternalPairFiber eta).stoppingTime cap =
      truncatedLevelTime m band.oldRank
        (externalCoordinateCutoff eta.1.1
          ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap)) := rfl
  change truncatedLevelTime m band.oldRank
        (externalCoordinateCutoff eta.1.1
          ((PositiveInterfaceExternalPairFiber eta).coordinateCap cap))
        (stepsOfWalk s) = v.length ∧
      incrementPrefixList v.length (stepsOfWalk s) = v
  constructor
  · rw [← hstopping]
    exact hqstop.1
  · exact hqstop.2

/-- Every early physical adjacent-row growth path lies in a canonical
external-pair source cap at the same coordinate cutoff. -/
theorem mem_iUnion_positiveInterfaceExternalPairSourceCap_of_raw_growth
    {t : DominoTiling} {o : Orientation} {m cutoff n : ℕ}
    {band : RandomClockBand}
    {threshold : ℕ → ℕ} {shell : ℕ} {s : WalkPath}
    (hm : 1 < m)
    (hphase : band.vertexPhase = false)
    (hthreshold : 0 < band.externalThreshold)
    (hcreation : ThresholdCreation s m band.oldRank n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hclock : n ≤ cutoff)
    (hvalid : s ∈ validStepWalk)
    (hfailure : s ∈ thresholdedGrowthFailure
      (dominantPositiveInterfaceBandOccupancy t o m cutoff band)
        threshold shellGrowth48 shell) :
    s ∈ ⋃ eta : PositiveInterfaceExternalPairSupportedIndex t
        o m band.oldRank band.externalThreshold
          (shellWidth48 m) shell,
      ⋃ cap : ℕ,
        positiveInterfaceExternalPairSourceCap eta cap threshold cutoff := by
  rcases exists_positiveInterfaceExternalPairSourceCap_of_raw_growth hm hphase
    hthreshold hcreation hnext hclock hvalid hfailure with
    ⟨eta, cap, _hcode, hcap⟩
  exact Set.mem_iUnion.mpr ⟨eta, Set.mem_iUnion.mpr ⟨cap, hcap⟩⟩

end

end Erdos1165.HLOZPositiveInterfacePairSourceCapCover
