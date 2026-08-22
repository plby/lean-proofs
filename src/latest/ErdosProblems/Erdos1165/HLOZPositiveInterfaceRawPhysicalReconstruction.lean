/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalTailRecovery
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalBaseWindow
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalScreenedEvent
import ErdosProblems.Erdos1165.HLOZRawFullGapProductPromotion

/-!
# Raw positive-interface growth as a physical stopped-coordinate tail

This module is the deterministic path lift missing from the physical
positive-interface product.  An early raw adjacent-shell growth failure is
placed in its exact all-creation `(trace, support)` atom, reconstructed by a
capped stopped coordinate vector, and identified with the ungated physical
random-total tail.  No probability estimate is used here.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfaceRawPhysicalReconstruction

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZAllSixBandProductClosure
open HLOZDynamicThresholdedScreening
open HLOZFullBetaRegimeSplit
open HLOZGapRandomClockScreen HLOZPathEvents
open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfaceSupportSelector
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPositiveInterfacePhysicalCoordinateRecovery
open HLOZPositiveInterfacePhysicalBaseWindow
open HLOZPositiveInterfacePhysicalScreenedEvent
open HLOZPositiveInterfacePhysicalTailRecovery
open HLOZPositiveInterfacePhysicalWindows
open HLOZProposition48Candidates
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement.StaticSupportRecoveryCertificate
open HLOZPositiveInterfaceGatedPhysicalSplit
open HLOZRawFullGapProductPromotion
open HLOZTilingGapBandExtraction HLOZTilingGapRandomClockScreen
open LazyDecomposition NearFavoriteShells NearFavoriteThresholded
open PathInsertion PreStoppingFiber PreStoppingSpatialLaw ScreeningInstantiation
open StoppedInsertion
open TilingCappedMarginalization
open TilingExternalPhaseSplit TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedPrefixedBoundarySourceLocalTime
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev DominoTiling := Tilings.Tiling

/-- The endpoint phase of a finite list has at most half of its vertices,
rounded up.  This sharpens the generic `length` bound by the one vertex
needed by the strict random-total cutoff. -/
private theorem two_mul_endpointPhaseVertices_length_le_add_one
    (p : List Point) :
    2 * (phaseVertices .endpoint p).length ≤ p.length + 1 := by
  change 2 * (endpointPhaseVertices p).length ≤ p.length + 1
  induction p using List.twoStepInduction with
  | nil => simp [endpointPhaseVertices]
  | singleton a => simp [endpointPhaseVertices]
  | cons_cons a b rest ih _ =>
      simp only [endpointPhaseVertices, List.length_cons]
      omega

/-- At a positive physical clock, endpoint-phase external sites are bounded
by the clock rather than by `clock + 1`. -/
theorem pathPhaseFilteredEndpointVisitedSites_card_le_clock
    (t : DominoTiling) (o : Orientation) (s : WalkPath) {n : ℕ}
    (hn : 0 < n) :
    (pathPhaseFilteredExternalVisitedSites t o false s n).card ≤ n := by
  classical
  unfold pathPhaseFilteredExternalVisitedSites
  change (phasedExternalVertexVisitedSites t o .endpoint
    (finitePathList (pathPrefix s n))).card ≤ n
  calc
    _ ≤ (phasedExternalVertexPath t o .endpoint
        (finitePathList (pathPrefix s n))).length := List.toFinset_card_le _
    _ = (phaseVertices .endpoint
        (tilingExternalPath t
          (phasedInput o (finitePathList (pathPrefix s n))))).length := rfl
    _ ≤ n := by
      have hphase := two_mul_endpointPhaseVertices_length_le_add_one
        (tilingExternalPath t
          (phasedInput o (finitePathList (pathPrefix s n))))
      have hexternal := HLOZAllSixBandProductClosure.tilingExternalPath_length_le
        t (phasedInput o (finitePathList (pathPrefix s n)))
      cases o with
      | even =>
          have hinput :
              (phasedInput .even
                (finitePathList (pathPrefix s n))).length = n + 1 := by
            simp [phasedInput, finitePathList]
          rw [hinput] at hexternal
          omega
      | shifted =>
          have hinput :
              (phasedInput .shifted
                (finitePathList (pathPrefix s n))).length = n := by
            simp [phasedInput, finitePathList]
          exact (HLOZSourceOrientedProposition44.endpointPhaseVertices_length_le
            (tilingExternalPath t
              (phasedInput .shifted
                (finitePathList (pathPrefix s n))))).trans
                  (hexternal.trans_eq hinput)

/-- On an endpoint band whose stopped clock is the genuine creation clock,
the raw dynamic occupancy is literally the physical endpoint-shell count. -/
theorem tilingBandOccupancy_eq_positiveInterfacePhysicalShell
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (s : WalkPath) (n shell : ℕ)
    (hphase : band.vertexPhase = false)
    (hclock : pathTruncatedLevelTime m band.oldRank cutoff s = n) :
    tilingBandOccupancy t m cutoff band s shell =
      (shellCandidates
        (positiveInterfacePhysicalSites t band.orientation
          band.externalThreshold s n)
        (fun x ↦ (m - localTime s n x) / shellWidth48 m) shell).card := by
  classical
  unfold tilingBandOccupancy dynamicShellOccupancy shellOccupancy
    dynamicThickCandidates positiveInterfacePhysicalSites
    tilingRandomClockVisitedSites tilingRandomClockExternalLargeEvent
    tilingRandomClockDistinguishedSites tilingRandomClockTotalLocalTime
    deficitShellLabel
  simp only [hphase, hclock, Set.mem_ofPred_eq]

/-- An early endpoint-band growth failure with the genuine old-rank favorite
profile belongs to the ungated physical stopped-coordinate screen.  The
strict product bound is the early creation cutoff itself. -/
theorem mem_positiveInterfacePhysicalScreenedEvent_of_raw_growth
    {t : DominoTiling} {m cutoff n : ℕ} {band : RandomClockBand}
    {threshold : ℕ → ℕ} {shell : ℕ} {s : WalkPath}
    (hm : 1 < m)
    (hphase : band.vertexPhase = false)
    (hthreshold : 0 < band.externalThreshold)
    (hcreation : ThresholdCreation s m band.oldRank n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hclock : n ≤ cutoff)
    (hvalid : s ∈ validStepWalk)
    (hfailure : s ∈ thresholdedGrowthFailure
      (tilingBandOccupancy t m cutoff band) threshold shellGrowth48 shell) :
    s ∈ positiveInterfacePhysicalScreenedEvent t band.orientation m
      band.oldRank band.externalThreshold hm band.oldRank_pos threshold
      (shellWidth48 m) shell cutoff := by
  classical
  have hn : 0 < n := by
    have hcreation' : ThresholdCreation (trajectory (stepsOfWalk s)) m
        band.oldRank n := by
      rw [show trajectory (stepsOfWalk s) = s from hvalid]
      exact hcreation
    exact HLOZThetaOneSourceShift.thresholdCreation_time_pos_of_two_le
      (stepsOfWalk s) (by omega) band.oldRank_pos hcreation'
  have hreach : ReachesThreshold s m band.oldRank := ⟨n, hcreation.1⟩
  have hatomUnion : s ∈ ⋃ eta : PositiveInterfaceSupportedIndex t
      band.orientation m band.oldRank band.externalThreshold,
      orientedAllCreationSupportTraceAtom t band.orientation m band.oldRank
        (PositiveInterfaceSupportAt t band.orientation m
          band.externalThreshold) eta.1.1 eta.1.2 := by
    rw [iUnion_supported_orientedAllCreationSupportTraceAtom]
    exact ⟨hreach, hvalid⟩
  rcases Set.mem_iUnion.mp hatomUnion with ⟨eta, hatom⟩
  have hcomplete := (PositiveInterfaceFiber eta).atom_complete hatom
  rcases Set.mem_iUnion.mp hcomplete with ⟨cap, hcap⟩
  rcases hcap with ⟨hvalid', hfiber⟩
  rcases Set.mem_iUnion.mp hfiber with ⟨qacc, hqstop⟩
  rcases qacc with ⟨q, hpred, haccepted⟩
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  have hstopTime : (PositiveInterfaceFiber eta).stoppingTime cap
      (stepsOfWalk s) = v.length := by
    exact hqstop.1
  have hvlt : v.length < orientedAllCreationCoordinateCutoff eta.1.1
      ((PositiveInterfaceFiber eta).coordinateCap cap) :=
    prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1
      ((PositiveInterfaceFiber eta).coordinateCap cap) q
  have hcreationV : ThresholdCreation s m band.oldRank v.length := by
    have hraw : ThresholdCreation (trajectory (stepsOfWalk s)) m
        band.oldRank v.length :=
      (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff m
        band.oldRank
        (orientedAllCreationCoordinateCutoff eta.1.1
          ((PositiveInterfaceFiber eta).coordinateCap cap))
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
        directionVectorOfList v := by
      exact (incrementPrefixList_eq_iff_stepPrefix_eq_directionVector
        (stepsOfWalk s) v).mp hqstop.2
    calc
      pathPrefix s v.length =
          trajectoryPrefix (stepPrefix v.length (stepsOfWalk s)) := by
        rw [trajectoryPrefix_stepPrefix, hvalid]
      _ = trajectoryPrefix (directionVectorOfList v) := congrArg _ hstep
      _ = trajectoryPrefix
          (stepPrefix v.length
            (extendPrefix (directionVectorOfList v))) := by
        rw [stepPrefix_extendPrefix]
      _ = pathPrefix
          (trajectory (extendPrefix (directionVectorOfList v))) v.length :=
        trajectoryPrefix_stepPrefix _ _
  have hfavorite : thresholdSites s v.length m = favoriteSites s v.length := by
    rw [hvn]
    exact thresholdSites_eq_favoriteSites_at_creation_of_terminal
      band.oldRank_pos hcreation le_rfl hnext
  have hsupport : orientedPositiveInterfaceSupportAt t band.orientation m
      band.externalThreshold s v.length = eta.1.2 := by
    rw [hvn, ← hcreationNat]
    exact hatom.2
  have hcanonical := canonical_mem_supportAtom_of_predicate_accepted
    ((PositiveInterfaceFiber eta).coordinateCap cap) q hpred haccepted
  have hstrict := positiveInterfaceCanonical_strictAway eta hm q hcanonical
    haccepted
  let D := supportComplementDistinguished t eta.1.1.external.start
    eta.1.1.external.retained eta.1.2
  let a := (splitTilingCoordinatesEquiv t eta.1.1.external.start
    eta.1.1.external.retained D q).2
  have hbelow : ∀ b : TilingAwayDomino t eta.1.1.external.start
      eta.1.1.external.retained D,
      localTime s v.length (orientedDominoEndpoint t band.orientation b.1.1) <
        m := by
    intro b
    have hphysical := positiveInterface_orientedEndpointLocalTime_eq_of_pathPrefix
      eta hm band.oldRank_pos q b s hprefix
    have hcanonicalBelow := hstrict b.1 b.2
    change localTime s v.length (orientedDominoEndpoint t
      band.orientation b.1.1) < m
    rw [hphysical]
    have hmax := positiveInterfaceCoordinateCount_le_fixedBoundaryDominoMax
      eta hm band.oldRank_pos b.1
    have htotal : tilingDominoTotal t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b.1 =
      tilingAwayTotal t eta.1.1.external.start eta.1.1.external.retained
        D a b := by
      exact (tilingAwayTotal_split_eq_dominoTotal t
        eta.1.1.external.start eta.1.1.external.retained D q b).symm
    exact lt_of_le_of_lt (Nat.add_le_add_right hmax _)
      (by simpa only [htotal] using hcanonicalBelow)
  let ell : TruncatedTotals ((PositiveInterfaceFiber eta).upper cap) :=
    fun b ↦ ⟨tilingAwayTotal t eta.1.1.external.start
      eta.1.1.external.retained D a b, by
        have hb := hstrict b.1 b.2
        have htotal : tilingDominoTotal t eta.1.1.external.start
            eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b.1 =
          tilingAwayTotal t eta.1.1.external.start eta.1.1.external.retained
            D a b := by
          exact (tilingAwayTotal_split_eq_dominoTotal t
            eta.1.1.external.start eta.1.1.external.retained D q b).symm
        rw [htotal] at hb
        change tilingAwayTotal t eta.1.1.external.start
          eta.1.1.external.retained D a b <
            max eta.1.1.external.retainedCount (m + shellWidth48 m) + 1
        omega⟩
  have hbase : (positiveInterfaceStaticSupportRecoveryCertificate eta hm
      band.oldRank_pos).baseProp cap ell := by
    intro b
    change (ell b : ℕ) ∈ positiveInterfaceBaseWindow eta cap b
    unfold ell positiveInterfaceBaseWindow
    rw [Finset.mem_range]
    have hb := hstrict b.1 b.2
    have htotal : tilingDominoTotal t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b.1 =
      tilingAwayTotal t eta.1.1.external.start eta.1.1.external.retained
        D a b := by
      exact (tilingAwayTotal_split_eq_dominoTotal t
        eta.1.1.external.start eta.1.1.external.retained D q b).symm
    exact Nat.lt_sub_of_add_lt
      (by simpa only [htotal, Nat.add_comm] using hb)
  have hclockEq : pathTruncatedLevelTime m band.oldRank cutoff s = n :=
    pathTruncatedLevelTime_eq_of_creation_le_cutoff hcreation hclock
  have hrawLower := tilingBandOccupancy_eq_positiveInterfacePhysicalShell
    t m cutoff band s n shell hphase hclockEq
  have hrawUpper := tilingBandOccupancy_eq_positiveInterfacePhysicalShell
    t m cutoff band s n (shell + 1) hphase hclockEq
  have hvpos : 0 < v.length := by omega
  have hlowerCard := card_positiveInterfacePhysicalShell_eq_awayWindow
    eta hm band.oldRank_pos q s hprefix hvalid hvpos hfavorite hsupport
      hthreshold hbelow (shellWidth48 m) shell
  have hupperCard := card_positiveInterfacePhysicalShell_eq_awayWindow
    eta hm band.oldRank_pos q s hprefix hvalid hvpos hfavorite hsupport
      hthreshold hbelow (shellWidth48 m) (shell + 1)
  dsimp only at hlowerCard hupperCard
  rw [hvn] at hlowerCard hupperCard
  let sites := positiveInterfacePhysicalSites t band.orientation
    band.externalThreshold s n
  let label := fun x ↦ (m - localTime s n x) / shellWidth48 m
  have hpairs :
      (shellCandidates sites label shell).card +
          (shellCandidates sites label (shell + 1)).card ≤ sites.card := by
    have hdisjoint : Disjoint (shellCandidates sites label shell)
        (shellCandidates sites label (shell + 1)) := by
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
  have hsites : sites.card ≤ n := by
    unfold sites positiveInterfacePhysicalSites
    exact (Finset.card_filter_le _ _).trans
      (pathPhaseFilteredEndpointVisitedSites_card_le_clock
        t band.orientation s hn)
  have hbound : tilingBandOccupancy t m cutoff band s shell +
      tilingBandOccupancy t m cutoff band s (shell + 1) < cutoff + 1 := by
    rw [hrawLower, hrawUpper]
    exact Nat.lt_succ_of_le (hpairs.trans (hsites.trans hclock))
  have htail : allCreationRandomTotalThresholdedUpperTail
      (PositiveInterfaceFiber eta) cap
      (fun b (u : Fin ((PositiveInterfaceFiber eta).upper cap b)) ↦
        (u : ℕ) ∈ physicalDeficitFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap) b.1)) (shell + 1))
      (fun b (u : Fin ((PositiveInterfaceFiber eta).upper cap b)) ↦
        (u : ℕ) ∈ physicalDeficitFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap) b.1)) shell)
      threshold shellGrowth48 shell cutoff ell := by
    let I := instFintypeTilingAwayDomino t
      ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)
    have huniv :
        (@Finset.univ (TilingAwayDomino t
          ((PositiveInterfaceFiber eta).start cap)
          ((PositiveInterfaceFiber eta).retained cap)
          ((PositiveInterfaceFiber eta).distinguished cap)) I) =
        (@Finset.univ (TilingAwayDomino t
          ((PositiveInterfaceFiber eta).start cap)
          ((PositiveInterfaceFiber eta).retained cap)
          ((PositiveInterfaceFiber eta).distinguished cap))
          (Subtype.fintype _)) := by
      ext b
      simp only [Finset.mem_univ]
    unfold allCreationRandomTotalThresholdedUpperTail
    apply @randomTotalThresholdedUpperTail_of_shell_cardinalities
      (TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
        ((PositiveInterfaceFiber eta).retained cap)
        ((PositiveInterfaceFiber eta).distinguished cap))
      I
      (fun b ↦ Fin ((PositiveInterfaceFiber eta).upper cap b))
      (fun b (u : Fin ((PositiveInterfaceFiber eta).upper cap b)) ↦
        (u : ℕ) ∈ physicalDeficitFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap) b.1)) (shell + 1))
      (fun b (u : Fin ((PositiveInterfaceFiber eta).upper cap b)) ↦
        (u : ℕ) ∈ physicalDeficitFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap) b.1)) shell)
      inferInstance inferInstance
      threshold shellGrowth48 shell cutoff ell
      (tilingBandOccupancy t m cutoff band s shell)
      (tilingBandOccupancy t m cutoff band s (shell + 1))
    · intro b hb
      exact Finset.disjoint_left.mp physicalAdjacentFailureWindows_disjoint
        hb.1 hb.2
    · rw [huniv]
      simp only [OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
        OrientedAllCreationPrefixedStoppedCoordinateSpec.retained, ell, D, a]
      exact hupperCard.symm.trans hrawUpper.symm
    · rw [huniv]
      simp only [OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
        OrientedAllCreationPrefixedStoppedCoordinateSpec.retained, ell, D, a]
      exact hlowerCard.symm.trans hrawLower.symm
    · simpa only [thresholdedGrowthFailure, Set.mem_ofPred_eq] using hfailure
    · exact hbound
  refine Set.mem_iUnion.mpr ⟨eta, Set.mem_iUnion.mpr ⟨cap, ?_⟩⟩
  refine ⟨hvalid', Set.mem_iUnion.mpr ⟨⟨q, ?_, haccepted⟩, hqstop⟩⟩
  refine ⟨hpred, ell, ?_, ?_⟩
  · dsimp only
    apply (positiveInterfacePhysicalScreenedAccepts_eq_true_iff eta hm
      band.oldRank_pos threshold (shellWidth48 m) shell cutoff cap ell).mpr
    exact ⟨hbase, htail⟩
  · intro b
    rfl


end

end Erdos1165.HLOZPositiveInterfaceRawPhysicalReconstruction
