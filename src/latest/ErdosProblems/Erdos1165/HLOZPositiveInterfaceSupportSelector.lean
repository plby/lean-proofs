/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaCreationSlots
import ErdosProblems.Erdos1165.HLOZTilingGapRandomClockScreen
import ErdosProblems.Erdos1165.TilingOrientedRetainedDominoEndpoint

/-!
# Retained support for a positive endpoint interface

An endpoint-phase band is indexed by physical sites in one temporal parity
class.  The independent insertion coordinates, however, are indexed by
canonical tiling bases.  This file selects every represented tiling domino
whose retained coordinate multiplicity is above the external threshold and
which is not already at level `m`.  The selector is a literal function of the
complete retained/threshold creation trace, hence is measurable and constant
on creation-prefix fibres.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZPositiveInterfaceSupportSelector

open HLOZSourceOrientedThetaCreationSlots
open HLOZSourceOrientedExternalLocalTime
open HLOZGapRandomClockScreen
open HLOZTilingGapRandomClockScreen NearFavoriteShells
open LazyDecomposition SpatialInsertionFiber
open TilingExternalPhaseSplit TilingLazyDecomposition
open TilingSpatialInsertionFiber
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedRetainedCoordinateSupport
open TilingOrientedRetainedSourceLocalTime
open TilingOrientedShellZeroSourcePartition
open VariableStoppedFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- Canonical tiling bases with thick retained multiplicity, excluding an
explicit finite family of domino bases. -/
def orientedPositiveInterfaceCodeSupport
    (t : DominoTiling) (externalThreshold : ℕ)
    (excludedBases : Finset Point)
    (z : OrientedTilingTypedExternalWordCode t) : Finset Point :=
  (tilingExternalDominoBases t z.start z.retained).filter
    fun b ↦
      externalThreshold ≤ orientedThetaCodeExternalCount t z b ∧
        b ∉ excludedBases

/-- Physical-path form of the thick below-threshold coordinate support. -/
def orientedPositiveInterfaceSupportAt
    (t : DominoTiling) (o : Orientation) (m externalThreshold : ℕ)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  orientedPositiveInterfaceCodeSupport t externalThreshold
    ((thresholdSites s n m).image (tilingBase t))
    (fixedOrientedTypedExternalWordCode t o n s)

theorem mem_orientedPositiveInterfaceCodeSupport_iff
    {t : DominoTiling} {externalThreshold : ℕ}
    {excludedBases : Finset Point}
    {z : OrientedTilingTypedExternalWordCode t} {b : Point} :
    b ∈ orientedPositiveInterfaceCodeSupport t externalThreshold
        excludedBases z ↔
      ∃ hb : b ∈ tilingExternalDominoBases t z.start z.retained,
        externalThreshold ≤ Fintype.card
          (TilingCoordinatesAt t z.start z.retained ⟨b, hb⟩) ∧
        b ∉ excludedBases := by
  classical
  unfold orientedPositiveInterfaceCodeSupport
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hb, hthick, hout⟩
    refine ⟨hb, ?_, hout⟩
    simpa [orientedThetaCodeExternalCount, hb] using hthick
  · rintro ⟨hb, hthick, hout⟩
    refine ⟨hb, ?_, hout⟩
    simpa [orientedThetaCodeExternalCount, hb] using hthick

/-- On a valid positive-time physical prefix, the totalized retained count
at a represented base is the source external local time of that domino's
oriented endpoint. -/
theorem orientedThetaCodeExternalCount_fixed_eq_source
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (hvalid : s ∈ validStepWalk) (hn : 0 < n) (b : Point)
    (hb : b ∈ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained) :
    orientedThetaCodeExternalCount t
        (fixedOrientedTypedExternalWordCode t o n s) b =
      HLOZSourceOrientedExternalLocalTime.tilingSourceExternalBaseLocalTime
        t o s n (orientedDominoEndpoint t o b) := by
  rw [orientedThetaCodeExternalCount, dif_pos hb]
  unfold validStepWalk at hvalid
  change trajectory (stepsOfWalk s) = s at hvalid
  generalize homega : stepsOfWalk s = omega at hvalid
  subst s
  rw [card_tilingCoordinatesAt_eq_orientedEndpointLocalTime t
    (fixedOrientedTypedExternalWordCode t o n
      (trajectory omega)).start
    (orientationCompatible_fixedOrientedTypedExternalWordCode_start
      t o n (trajectory omega) hn)
    (fixedOrientedTypedExternalWordCode t o n
      (trajectory omega)).retained ⟨b, hb⟩]
  have hphase := phasedExternalVertexPath_eq_orientedRawEndpointPath
    t o omega n hn
  unfold TilingExternalPhaseSplit.phasedExternalVertexPath at hphase
  exact congrArg
    (fun p : List Point ↦ listLocalTime p (orientedDominoEndpoint t o b))
    ((fixedOrientedTypedExternalWordCode_endpointPath t o omega n hn).trans
      hphase.symm)

/-- Every endpoint-chain site of a valid positive physical prefix is carried
by a represented retained domino coordinate. -/
theorem tilingBase_mem_fixedExternalDominoBases_of_mem_sourceVisited
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (hvalid : s ∈ validStepWalk) (hn : 0 < n) (x : Point)
    (hx : x ∈ tilingSourceExternalVisitedSites t o s n) :
    tilingBase t x ∈ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained := by
  unfold validStepWalk at hvalid
  change trajectory (stepsOfWalk s) = s at hvalid
  generalize homega : stepsOfWalk s = omega at hvalid
  subst s
  rw [tilingSourceExternalVisitedSites, Finset.mem_filter] at hx
  have hxphase := hx.1
  change x ∈ phasedExternalVertexVisitedSites t o .endpoint
      (finitePathList (pathPrefix (trajectory omega) n)) at hxphase
  unfold phasedExternalVertexVisitedSites tilingExternalPhaseVisitedSites at hxphase
  rw [List.mem_toFinset] at hxphase
  change x ∈ phasedExternalVertexPath t o .endpoint
      (finitePathList (pathPrefix (trajectory omega) n)) at hxphase
  have hendpoint :=
    (fixedOrientedTypedExternalWordCode_endpointPath t o omega n hn).trans
      (phasedExternalVertexPath_eq_orientedRawEndpointPath
        t o omega n hn).symm
  rw [← hendpoint, blockEndpointPath_eq_rawExternalBaseList,
    List.mem_ofFn] at hxphase
  obtain ⟨j, hj⟩ := hxphase
  unfold tilingExternalDominoBases
  rw [Finset.mem_image]
  exact ⟨j, Finset.mem_univ _, congrArg (tilingBase t) hj⟩

/-- On a level-favorite prefix, a thick nonfavorite endpoint-phase site
selects its canonical domino in the retained positive-interface support. -/
theorem tilingBase_mem_orientedPositiveInterfaceSupportAt
    (t : DominoTiling) (o : Orientation) (m externalThreshold : ℕ)
    (s : WalkPath) (n : ℕ) (hvalid : s ∈ validStepWalk) (hn : 0 < n)
    (hfavorite : thresholdSites s n m = favoriteSites s n)
    (hthreshold : 0 < externalThreshold) (x : Point)
    (hvisited : x ∈ pathPhaseFilteredExternalVisitedSites t o false s n)
    (hexternal : externalThreshold ≤
      pathPhaseFilteredExternalLocalTime t o false s n x)
    (hout : x ∉ favoriteTilingDominoSites t s n) :
    tilingBase t x ∈
      orientedPositiveInterfaceSupportAt t o m externalThreshold s n := by
  have hcompatible : OrientationCompatible o x := by
    by_contra hnot
    unfold validStepWalk at hvalid
    have hzero := phasedExternalEndpointLocalTime_eq_zero_of_incompatible
      t o (stepsOfWalk s) n x hnot
    rw [hvalid] at hzero
    change externalThreshold ≤ phasedExternalVertexLocalTime t o .endpoint
      (finitePathList (pathPrefix s n)) x at hexternal
    omega
  have hxSourceVisited : x ∈ tilingSourceExternalVisitedSites t o s n := by
    rw [tilingSourceExternalVisitedSites, Finset.mem_filter]
    refine ⟨?_, hcompatible⟩
    simpa only [pathPhaseFilteredExternalVisitedSites,
      externalVertexPhaseOfBool] using hvisited
  have hb := tilingBase_mem_fixedExternalDominoBases_of_mem_sourceVisited
    t o s n hvalid hn x hxSourceVisited
  have hxendpoint : x = orientedDominoEndpoint t o (tilingBase t x) :=
    eq_orientedDominoEndpoint_of_compatible_of_tilingBase_eq
      t o hcompatible rfl
  unfold orientedPositiveInterfaceSupportAt
  unfold orientedPositiveInterfaceCodeSupport
  rw [Finset.mem_filter]
  refine ⟨hb, ?_, ?_⟩
  · rw [orientedThetaCodeExternalCount_fixed_eq_source
      t o s n hvalid hn (tilingBase t x) hb]
    rw [← hxendpoint]
    change externalThreshold ≤ phasedExternalVertexLocalTime t o .endpoint
      (finitePathList (pathPrefix s n)) x
    simpa only [pathPhaseFilteredExternalLocalTime,
      externalVertexPhaseOfBool] using hexternal
  · rw [hfavorite]
    intro hbFavorite
    obtain ⟨y, hy, hbase⟩ := Finset.mem_image.mp hbFavorite
    apply hout
    rw [favoriteTilingDominoSites, Finset.mem_union]
    rcases (tilingBase_eq_iff t y x).mp hbase with hxy | hdom
    · left
      simpa only [hxy] using hy
    · right
      rw [Finset.mem_image]
      refine ⟨y, hy, ?_⟩
      have hp : tilingPartner t y = x :=
        (sameDomino_iff_partner_eq t y x).mp hdom
      exact hp

/-- Every genuine endpoint-band candidate at a positive truncated clock is
represented by the concrete positive-interface support. -/
theorem tilingRandomClockBandSite_base_mem_positiveInterfaceSupport
    {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    {band : HLOZGapRandomClockScreen.RandomClockBand} {x : Point}
    (hvalid : s ∈ validStepWalk)
    (hn : 0 < pathTruncatedLevelTime m band.oldRank cutoff s)
    (hfavorite : thresholdSites s
      (pathTruncatedLevelTime m band.oldRank cutoff s) m =
        favoriteSites s
          (pathTruncatedLevelTime m band.oldRank cutoff s))
    (hthreshold : 0 < band.externalThreshold)
    (hphase : band.vertexPhase = false)
    (hx : x ∈ tilingRandomClockBandSites t m cutoff s band) :
    tilingBase t x ∈ orientedPositiveInterfaceSupportAt t band.orientation
      m band.externalThreshold s
        (pathTruncatedLevelTime m band.oldRank cutoff s) := by
  rw [tilingRandomClockBandSites, mem_boundedCandidates] at hx
  rcases hx with ⟨hx, _hshell⟩
  rw [Finset.mem_filter] at hx
  rcases hx with ⟨hvisited, hexternal, hout⟩
  apply tilingBase_mem_orientedPositiveInterfaceSupportAt
    t band.orientation m band.externalThreshold s
      (pathTruncatedLevelTime m band.oldRank cutoff s)
      hvalid hn hfavorite hthreshold x
  · simpa only [tilingRandomClockVisitedSites, hphase] using hvisited
  · change band.externalThreshold ≤
      pathPhaseFilteredExternalLocalTime t band.orientation
        band.vertexPhase s
          (pathTruncatedLevelTime m band.oldRank cutoff s) x at hexternal
    simpa only [hphase] using hexternal
  · simpa only [tilingRandomClockDistinguishedSites] using hout
theorem orientedPositiveInterfaceSupportAt_prefix_invariant
    (t : DominoTiling) (o : Orientation) (m externalThreshold : ℕ)
    {s s' : WalkPath} {n : ℕ} (hp : pathPrefix s n = pathPrefix s' n) :
    orientedPositiveInterfaceSupportAt t o m externalThreshold s n =
      orientedPositiveInterfaceSupportAt t o m externalThreshold s' n := by
  unfold orientedPositiveInterfaceSupportAt
  have hthreshold : thresholdSites s n m = thresholdSites s' n m := by
    have hvisited : visitedSites s n = visitedSites s' n := by
      unfold visitedSites
      rw [hp]
    ext x
    simp only [thresholdSites, Finset.mem_filter]
    have hlocal : localTime s n x = localTime s' n x := by
      unfold localTime
      rw [hp]
    rw [hvisited, hlocal]
  rw [fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp,
    hthreshold]

theorem measurable_orientedPositiveInterfaceSupportAt
    (t : DominoTiling) (o : Orientation) (m externalThreshold n : ℕ) :
    Measurable fun s ↦
      orientedPositiveInterfaceSupportAt t o m externalThreshold s n := by
  apply measurable_of_pathPrefix_invariant n
  exact orientedPositiveInterfaceSupportAt_prefix_invariant
    t o m externalThreshold

/-- The thick below-threshold support is a valid concrete all-creation support
selector at rank `k`. -/
theorem orientedPositiveInterfaceSupportSelectorData
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ) :
    OrientedAllCreationSupportSelectorData t o m k
      (orientedPositiveInterfaceSupportAt t o m externalThreshold) := by
  constructor
  · exact measurable_natIndexed (creationTimeNat m k)
      (measurable_creationTimeNat m k)
      (fun n s ↦ orientedPositiveInterfaceSupportAt
        t o m externalThreshold s n)
      (measurable_orientedPositiveInterfaceSupportAt
        t o m externalThreshold)
  · intro s s' n hp
    exact orientedPositiveInterfaceSupportAt_prefix_invariant
      t o m externalThreshold hp
  · intro s n _hvalid
    exact Finset.filter_subset _ _

end

end Erdos1165.HLOZPositiveInterfaceSupportSelector
