/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceAggregateRecovery
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalWindows
import ErdosProblems.Erdos1165.TilingOrientedPrefixedBoundarySourceLocalTime

/-!
# Physical local time of a positive-interface stopped coordinate

On an exact positive-interface trace atom, an away insertion coordinate is
indexed by a retained tiling domino.  This file identifies the physical local
time of the orientation-selected endpoint of that domino with the retained
coordinate multiplicity plus its away insertion total.  The identity is the
deterministic bridge between raw deficit shells and the physical product
windows.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfacePhysicalCoordinateRecovery

open HLOZPositiveInterfaceAggregateRecovery
open HLOZPathEvents
open HLOZPositiveInterfaceSupportSelector
open HLOZPositiveInterfacePhysicalWindows
open HLOZSourceOrientedExternalLocalTime
open HLOZTilingGapRandomClockScreen
open NearFavoriteShells
open LazyDecomposition PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber
open StoppedInsertion
open TilingCappedMarginalization TilingInsertedLocalTime
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedPrefixedBoundarySourceLocalTime
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedFiber
open TilingLazyDecomposition
open TilingExternalPhaseSplit
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- The physical endpoint-phase candidates represented by a positive-interface
support, before deficit-shell filtering. -/
noncomputable def positiveInterfacePhysicalSites
    (t : DominoTiling) (o : Orientation) (externalThreshold : ℕ)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  (pathPhaseFilteredExternalVisitedSites t o false s n).filter fun x ↦
    externalThreshold ≤
        pathPhaseFilteredExternalLocalTime t o false s n x ∧
      x ∉ favoriteTilingDominoSites t s n

/-- On a genuine positive old-rank prefix, the raw endpoint-phase thick sites
are exactly the orientation-selected physical endpoints of the retained
positive-interface support. -/
theorem positiveInterfacePhysicalSites_eq_support_image
    (t : DominoTiling) (o : Orientation) (m externalThreshold : ℕ)
    (s : WalkPath) (n : ℕ) (hvalid : s ∈ validStepWalk) (hn : 0 < n)
    (hfavorite : thresholdSites s n m = favoriteSites s n)
    (hthreshold : 0 < externalThreshold) :
    positiveInterfacePhysicalSites t o externalThreshold s n =
      (orientedPositiveInterfaceSupportAt t o m externalThreshold s n).image
        (orientedDominoEndpoint t o) := by
  classical
  ext x
  constructor
  · intro hx
    rw [positiveInterfacePhysicalSites, Finset.mem_filter] at hx
    rcases hx with ⟨hvisited, hexternal, hout⟩
    have hcompat : OrientationCompatible o x := by
      by_contra hnot
      unfold validStepWalk at hvalid
      have hzero := phasedExternalEndpointLocalTime_eq_zero_of_incompatible
        t o (stepsOfWalk s) n x hnot
      rw [hvalid] at hzero
      change externalThreshold ≤ phasedExternalVertexLocalTime t o .endpoint
        (finitePathList (pathPrefix s n)) x at hexternal
      omega
    have hsupport : tilingBase t x ∈
        orientedPositiveInterfaceSupportAt t o m externalThreshold s n :=
      tilingBase_mem_orientedPositiveInterfaceSupportAt t o m
        externalThreshold s n hvalid hn hfavorite hthreshold x
          hvisited hexternal hout
    rw [Finset.mem_image]
    refine ⟨tilingBase t x, hsupport, ?_⟩
    exact (eq_orientedDominoEndpoint_of_compatible_of_tilingBase_eq
      t o hcompat rfl).symm
  · intro hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨b, hbSupport, rfl⟩
    unfold orientedPositiveInterfaceSupportAt at hbSupport
    rw [mem_orientedPositiveInterfaceCodeSupport_iff] at hbSupport
    rcases hbSupport with ⟨hbRepresented, hbThick, hbOutside⟩
    let bext : TilingExternalDomino t
        (fixedOrientedTypedExternalWordCode t o n s).start
        (fixedOrientedTypedExternalWordCode t o n s).retained :=
      ⟨b, hbRepresented⟩
    have hcount : pathPhaseFilteredExternalLocalTime t o false s n
          (orientedDominoEndpoint t o b) =
        Fintype.card (TilingCoordinatesAt t
          (fixedOrientedTypedExternalWordCode t o n s).start
          (fixedOrientedTypedExternalWordCode t o n s).retained bext) := by
      have hc := orientedThetaCodeExternalCount_fixed_eq_source
        t o s n hvalid hn b hbRepresented
      rw [HLOZSourceOrientedThetaCreationSlots.orientedThetaCodeExternalCount,
        dif_pos hbRepresented] at hc
      simpa only [bext, pathPhaseFilteredExternalLocalTime,
        externalVertexPhaseOfBool, tilingSourceExternalBaseLocalTime,
        prefixTilingSourceExternalBaseLocalTime] using hc.symm
    have hvisited : orientedDominoEndpoint t o b ∈
        pathPhaseFilteredExternalVisitedSites t o false s n := by
      unfold pathPhaseFilteredExternalVisitedSites
      unfold phasedExternalVertexVisitedSites
      rw [mem_tilingExternalPhaseVisitedSites_iff]
      change 0 < pathPhaseFilteredExternalLocalTime t o false s n
        (orientedDominoEndpoint t o b)
      rw [hcount]
      exact lt_of_lt_of_le hthreshold hbThick
    have hbBase : IsTilingBase t b :=
      isTilingBase_of_tilingBase_eq_self t b
        (tilingExternalDomino_is_base t
          (fixedOrientedTypedExternalWordCode t o n s).start
          (fixedOrientedTypedExternalWordCode t o n s).retained bext)
    have hbaseEndpoint :
        tilingBase t (orientedDominoEndpoint t o b) = b :=
      tilingBase_orientedDominoEndpoint t o b hbBase
    have hout : orientedDominoEndpoint t o b ∉
        favoriteTilingDominoSites t s n := by
      intro hin
      apply hbOutside
      rw [hfavorite, Finset.mem_image]
      unfold favoriteTilingDominoSites at hin
      rw [Finset.mem_union] at hin
      rcases hin with hfavoriteEndpoint | hpartnerImage
      · exact ⟨orientedDominoEndpoint t o b, hfavoriteEndpoint,
          hbaseEndpoint⟩
      · rw [Finset.mem_image] at hpartnerImage
        rcases hpartnerImage with ⟨y, hyFavorite, hy⟩
        refine ⟨y, hyFavorite, ?_⟩
        rw [← hbaseEndpoint, ← hy, tilingBase_partner]
    rw [positiveInterfacePhysicalSites, Finset.mem_filter]
    exact ⟨hvisited, hcount.symm ▸ hbThick, hout⟩

/-- On the canonical prefixed insertion path, the physical local time of an
away domino's orientation-selected endpoint is exactly its retained
multiplicity plus its away insertion total. -/
theorem positiveInterfaceCanonical_orientedEndpointLocalTime_eq
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k)
    {cap : ℕ}
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (b : TilingAwayDomino t eta.1.1.external.start
      eta.1.1.external.retained
      (supportComplementDistinguished t eta.1.1.external.start
        eta.1.1.external.retained eta.1.2)) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    localTime s v.length (orientedDominoEndpoint t o b.1.1) =
      Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
        eta.1.1.external.retained b.1) +
      tilingAwayTotal t eta.1.1.external.start eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2)
        ((splitTilingCoordinatesEquiv t eta.1.1.external.start
          eta.1.1.external.retained
          (supportComplementDistinguished t eta.1.1.external.start
            eta.1.1.external.retained eta.1.2) q).2) b := by
  classical
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained (fun j ↦ (q j : ℕ))
    eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath eta.1.1.external.initial.1
        eta.1.1.external.start
        (tilingInsertGapVector t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)))
        (positiveInterfaceTerminal eta) := by
    rw [← positiveInterfaceTerminal_eq_coordinates eta
      (fun j ↦ (q j : ℕ))]
    exact finitePathList_prefixedTilingInsertionPrefix
      eta.1.1.external.initial t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail rfl
  have hbBase : IsTilingBase t b.1.1 :=
    isTilingBase_of_tilingBase_eq_self t b.1.1
      (tilingExternalDomino_is_base t eta.1.1.external.start
        eta.1.1.external.retained b.1)
  have hlocal : localTime s v.length
        (orientedDominoEndpoint t o b.1.1) =
      prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (positiveInterfaceTerminal eta)
          (orientedDominoEndpoint t o b.1.1) +
        tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b.1 := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        (positiveInterfaceTerminal eta) b.1
        (orientedDominoEndpoint t o b.1.1)]
    exact tilingBase_orientedDominoEndpoint t o b.1.1 hbBase
  let etaExternal : SupportedIndex t o m k :=
    ⟨eta.1.1.external, by
      rcases eta.2 with ⟨s0, hs0⟩
      refine ⟨s0, hs0.1.1, hs0.1.2.1, ?_⟩
      exact congrArg OrientedAllCreationTraceCode.external hs0.1.2.2⟩
  have hboundary : prefixedTilingFixedBoundaryLocalTime
        eta.1.1.external.initial.1 eta.1.1.external.start
        eta.1.1.external.retained (positiveInterfaceTerminal eta)
        (orientedDominoEndpoint t o b.1.1) =
      Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
        eta.1.1.external.retained b.1) := by
    rw [← positiveInterfaceTerminal_eq_coordinates eta
      (fun j ↦ (q j : ℕ))]
    exact prefixedBoundaryLocalTime_orientedEndpoint_eq_coordinateCard
      etaExternal hm hk (fun j ↦ (q j : ℕ)) b.1
  change localTime s v.length (orientedDominoEndpoint t o b.1.1) =
    Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
      eta.1.1.external.retained b.1) +
    tilingAwayTotal t eta.1.1.external.start eta.1.1.external.retained
      (supportComplementDistinguished t eta.1.1.external.start
        eta.1.1.external.retained eta.1.2)
      ((splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q).2) b
  rw [hlocal, hboundary,
    tilingAwayTotal_split_eq_dominoTotal t eta.1.1.external.start
      eta.1.1.external.retained
      (supportComplementDistinguished t eta.1.1.external.start
      eta.1.1.external.retained eta.1.2) q b]

/-- The same coordinate identity on any physical path with the canonical
stopped prefix.  This is the form used after destructing a member of a
prefixed stopped insertion atom. -/
theorem positiveInterface_orientedEndpointLocalTime_eq_of_pathPrefix
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) {cap : ℕ}
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (b : TilingAwayDomino t eta.1.1.external.start
      eta.1.1.external.retained
      (supportComplementDistinguished t eta.1.1.external.start
        eta.1.1.external.retained eta.1.2))
    (s : WalkPath)
    (hprefix :
      let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
      let sq := trajectory (extendPrefix (directionVectorOfList v))
      pathPrefix s v.length = pathPrefix sq v.length) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    localTime s v.length (orientedDominoEndpoint t o b.1.1) =
      Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
        eta.1.1.external.retained b.1) +
      tilingAwayTotal t eta.1.1.external.start eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2)
        ((splitTilingCoordinatesEquiv t eta.1.1.external.start
          eta.1.1.external.retained
          (supportComplementDistinguished t eta.1.1.external.start
            eta.1.1.external.retained eta.1.2) q).2) b := by
  classical
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained (fun j ↦ (q j : ℕ))
    eta.1.1.external.tail.1
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  change localTime s v.length (orientedDominoEndpoint t o b.1.1) = _
  have hlocal : localTime s v.length (orientedDominoEndpoint t o b.1.1) =
      localTime sq v.length (orientedDominoEndpoint t o b.1.1) := by
    rw [localTime_eq_listLocalTime, localTime_eq_listLocalTime, hprefix]
  rw [hlocal]
  exact positiveInterfaceCanonical_orientedEndpointLocalTime_eq
    eta hm hk q b

/-- Membership in a physical failure-count window is exactly the physical
deficit-shell label of the corresponding stopped endpoint.  The explicit
`< m+1` conjunct records the finite range built into the coordinate window. -/
theorem positiveInterface_awayTotal_mem_physicalWindow_iff
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) {cap : ℕ}
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (b : TilingAwayDomino t eta.1.1.external.start
      eta.1.1.external.retained
      (supportComplementDistinguished t eta.1.1.external.start
        eta.1.1.external.retained eta.1.2))
    (s : WalkPath)
    (hprefix :
      let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
      let sq := trajectory (extendPrefix (directionVectorOfList v))
      pathPrefix s v.length = pathPrefix sq v.length)
    (hbelow :
      let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
      localTime s v.length (orientedDominoEndpoint t o b.1.1) < m)
    (width shell : ℕ) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    tilingAwayTotal t eta.1.1.external.start eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2)
        ((splitTilingCoordinatesEquiv t eta.1.1.external.start
          eta.1.1.external.retained
          (supportComplementDistinguished t eta.1.1.external.start
            eta.1.1.external.retained eta.1.2) q).2) b ∈
      physicalDeficitFailureWindow m width
        (Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
          eta.1.1.external.retained b.1)) shell ↔
      (m - localTime s v.length (orientedDominoEndpoint t o b.1.1)) /
        width = shell := by
  classical
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained (fun j ↦ (q j : ℕ))
    eta.1.1.external.tail.1
  have hlocal := positiveInterface_orientedEndpointLocalTime_eq_of_pathPrefix
    eta hm hk q b s hprefix
  rw [mem_physicalDeficitFailureWindow]
  let a := tilingAwayTotal t eta.1.1.external.start
    eta.1.1.external.retained
    (supportComplementDistinguished t eta.1.1.external.start
      eta.1.1.external.retained eta.1.2)
    ((splitTilingCoordinatesEquiv t eta.1.1.external.start
      eta.1.1.external.retained
      (supportComplementDistinguished t eta.1.1.external.start
        eta.1.1.external.retained eta.1.2) q).2) b
  let i := Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
    eta.1.1.external.retained b.1)
  change localTime s v.length (orientedDominoEndpoint t o b.1.1) =
    i + a at hlocal
  change localTime s v.length (orientedDominoEndpoint t o b.1.1) < m at hbelow
  change (a < m + 1 ∧ (m - (i + a)) / width = shell) ↔
    (m - localTime s v.length (orientedDominoEndpoint t o b.1.1)) /
      width = shell
  rw [hlocal] at hbelow ⊢
  constructor
  · exact fun h ↦ h.2
  · intro hshell
    constructor
    · omega
    · exact hshell

/-- For one exact stopped coordinate vector, raw physical shell occupancy is
the cardinality of the corresponding away-coordinate physical window.  This
is the all-site count transport required by the thresholded product tail. -/
theorem card_positiveInterfacePhysicalShell_eq_awayWindow
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) {cap : ℕ}
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (s : WalkPath)
    (hprefix :
      let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
      let sq := trajectory (extendPrefix (directionVectorOfList v))
      pathPrefix s v.length = pathPrefix sq v.length)
    (hvalid : s ∈ validStepWalk)
    (hpositive :
      let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
      0 < v.length)
    (hfavorite :
      let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
      thresholdSites s v.length m = favoriteSites s v.length)
    (hsupport :
      let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
      orientedPositiveInterfaceSupportAt t o m externalThreshold s v.length =
        eta.1.2)
    (hthreshold : 0 < externalThreshold)
    (hbelow :
      let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
      ∀ b : TilingAwayDomino t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2),
        localTime s v.length (orientedDominoEndpoint t o b.1.1) < m)
    (width shell : ℕ) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    (shellCandidates
      (positiveInterfacePhysicalSites t o externalThreshold s v.length)
      (fun x ↦ (m - localTime s v.length x) / width) shell).card =
    (Finset.univ.filter fun b : TilingAwayDomino t eta.1.1.external.start
      eta.1.1.external.retained
      (supportComplementDistinguished t eta.1.1.external.start
        eta.1.1.external.retained eta.1.2) ↦
        tilingAwayTotal t eta.1.1.external.start eta.1.1.external.retained
          (supportComplementDistinguished t eta.1.1.external.start
            eta.1.1.external.retained eta.1.2)
          ((splitTilingCoordinatesEquiv t eta.1.1.external.start
            eta.1.1.external.retained
            (supportComplementDistinguished t eta.1.1.external.start
              eta.1.1.external.retained eta.1.2) q).2) b ∈
        physicalDeficitFailureWindow m width
          (Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
            eta.1.1.external.retained b.1)) shell).card := by
  classical
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained (fun j ↦ (q j : ℕ))
    eta.1.1.external.tail.1
  change _ = _
  have hsites := positiveInterfacePhysicalSites_eq_support_image
    t o m externalThreshold s v.length hvalid hpositive hfavorite hthreshold
  rw [hsupport] at hsites
  symm
  apply Finset.card_bij
    (fun b _hb ↦ orientedDominoEndpoint t o b.1.1)
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [mem_shellCandidates, hsites]
    constructor
    · rw [Finset.mem_image]
      exact ⟨b.1.1,
        (away_mem_support_iff t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2 b.1).1 b.2, rfl⟩
    · exact (positiveInterface_awayTotal_mem_physicalWindow_iff
        eta hm hk q b s hprefix (hbelow b) width shell).mp hb.2
  · intro b _hb c _hc heq
    have hbBase : IsTilingBase t b.1.1 :=
      isTilingBase_of_tilingBase_eq_self t b.1.1
        (tilingExternalDomino_is_base t eta.1.1.external.start
          eta.1.1.external.retained b.1)
    have hcBase : IsTilingBase t c.1.1 :=
      isTilingBase_of_tilingBase_eq_self t c.1.1
        (tilingExternalDomino_is_base t eta.1.1.external.start
          eta.1.1.external.retained c.1)
    apply Subtype.ext
    apply Subtype.ext
    rw [← tilingBase_orientedDominoEndpoint t o b.1.1 hbBase,
      ← tilingBase_orientedDominoEndpoint t o c.1.1 hcBase, heq]
  · intro x hx
    rw [mem_shellCandidates, hsites] at hx
    rcases hx with ⟨hxSupport, hxShell⟩
    rw [Finset.mem_image] at hxSupport
    rcases hxSupport with ⟨b, hbS, hbx⟩
    let ba := supportAwayChosen t eta.1.1.external.start
      eta.1.1.external.retained eta.1.2
      (PositiveInterfaceFiber eta).support_represented b hbS
    refine ⟨ba, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      apply (positiveInterface_awayTotal_mem_physicalWindow_iff
        eta hm hk q ba s hprefix (hbelow ba) width shell).mpr
      simpa only [ba, supportAwayChosen_base] using hbx ▸ hxShell
    · rw [show ba.1.1 = b by
        exact supportAwayChosen_base t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2
          (PositiveInterfaceFiber eta).support_represented b hbS]
      exact hbx

end

end Erdos1165.HLOZPositiveInterfacePhysicalCoordinateRecovery
