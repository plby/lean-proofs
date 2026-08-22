/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongSingletonAccepted

/-!
# Same-cap cover for a physical strong broad-source singleton

The physical source strip is intersected with the monotone stopped creation
atom.  On a singleton support atom, the source window, low external count,
and honest mate-below-level condition reconstruct the literal zero-increment
broad-Theta predicate at the same coordinate cap.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZCandidateLocalBroadThetaStrongSlotCapCover

open HLOZCandidateLocalBroadSourceStrongRoute
open HLOZCandidateLocalBroadThetaStrongSingletonAccepted
open HLOZCandidateLocalBroadThetaActualDeltaCapBound
open HLOZCandidateLocalBroadThetaActualDeltaWalkCap
open HLOZPathEvents
open HLOZSourceOrientedThetaSourceSlotCapCover
open HLOZTypedStoppedCandidateObservability
open LazyDecomposition PathInsertion PreStoppingFiber SpatialInsertionFiber
open StoppedInsertion
open TilingCappedMarginalization TilingLazyDecomposition
open TilingDistinguishedTraceInvariant
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedRetainedSourceLocalTime
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The monotone stopped atom intersected with one physical strong source
singleton. -/
def physicalSingletonBroadSourceStrongCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt) (b : Point)
    (cap width externalThreshold : ℕ) : Set WalkPath :=
  sourceSlotAtomCap supportData eta cap ∩
    {s | b ∈ orientedBroadSourceLowThetaStrongBases t o m width
      externalThreshold s (creationTimeNat m k s)}

theorem physicalSingletonBroadSourceStrongCap_monotone
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt) (b : Point)
    (width externalThreshold : ℕ) :
    Monotone fun cap ↦ physicalSingletonBroadSourceStrongCap supportData eta b
      cap width externalThreshold := by
  intro cap cap' hcap s hs
  exact ⟨sourceSlotAtomCap_monotone supportData eta hcap hs.1, hs.2⟩

/-- Same-cap reconstruction of the physical strong singleton into the broad
zero-increment stopped product cap. -/
theorem physicalSingletonBroadSourceStrongCap_subset_zeroDeltaCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (b : Point) (hsingleton : eta.1.2 = {b})
    (hm : 1 < m) (hk : 0 < k) (cap width externalThreshold : ℕ) :
    physicalSingletonBroadSourceStrongCap supportData eta b cap width
        externalThreshold ⊆
      broadSourceZeroDeltaCap supportData eta cap width externalThreshold := by
  classical
  intro s hs
  rcases hs with ⟨hcap, hbstrong⟩
  let data := concreteFiber o m k supportAt supportData eta
  have hatom := data.atom_sound cap hcap
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hatom
  rcases hcap with ⟨hvalid', hpre⟩
  rcases Set.mem_iUnion.mp hpre with ⟨q, hq⟩
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  have hp : pathPrefix s v.length = pathPrefix sq v.length := by
    have hp' := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
      eta.1.1.initial.1 eta.1.1.start eta.1.1.retained
      (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1 (stepsOfWalk s) hq
    have hwalk : trajectory (stepsOfWalk s) = s := hatom.1
    rw [hwalk] at hp'
    simpa only [v, sq] using hp'
  have htime : creationTimeNat m k s = v.length := by
    have hstop := q.2.2
    change truncatedLevelTime m k
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap))
        (extendPrefix (directionVectorOfList v)) = v.length at hstop
    have hlt : v.length <
        externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
      let dummy : TilingCreationFavoriteData :=
        ((∅, ∅), (eta.1.1.start, eta.1.1.start))
      have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
        (withFavorite eta.1.1 dummy) (data.coordinateCap cap) q.1
      rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
      exact hraw
    have hcreationQ : ThresholdCreation sq m k v.length :=
      (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
        m k (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap))
        v.length _ hlt).mp hstop
    exact creationTimeNat_eq_of_creation
      ((thresholdCreation_iff_of_pathPrefix_eq hp
        (Nat.le_refl v.length)).mpr hcreationQ)
  change b ∈ orientedBroadSourceLowThetaStrongBases t o m width
    externalThreshold s (creationTimeNat m k s) at hbstrong
  rw [orientedBroadSourceLowThetaStrongBases, Finset.mem_filter] at hbstrong
  have hblower := hbstrong.1
  rw [HLOZCandidateLocalBroadSourceLowThetaGeometry.orientedBroadSourceLowThetaBases,
    Finset.mem_filter] at hblower
  rcases hblower with ⟨_hvisited, hcompat, hbsource, hexternalS⟩
  have hbrepresented : b ∈
      tilingExternalDominoBases t eta.1.1.start eta.1.1.retained := by
    have hmem : b ∈ supportAt s (creationTimeNat m k s) := by
      rw [hatom.2.2.2, hsingleton]
      simp
    rw [← hatom.2.2.1]
    exact supportData.represented s (creationTimeNat m k s) hatom.1 hmem
  have hpTime : pathPrefix s (creationTimeNat m k s) =
      pathPrefix sq (creationTimeNat m k s) := by
    rw [htime]
    exact hp
  have hbsourceQ : localTime sq v.length b ∈
      HLOZShellZeroReplacementWindows.shellZeroSourceTotalWindow m width := by
    rw [← htime, ← localTime_eq_of_pathPrefix_eq hpTime b]
    exact hbsource
  have hpartnerQ : localTime sq v.length (tilingPartner t b) < m := by
    rw [← htime,
      ← localTime_eq_of_pathPrefix_eq hpTime (tilingPartner t b)]
    exact hbstrong.2
  have hcreationPos : 0 < creationTimeNat m k s := by
    have hcreationS : ThresholdCreation s m k (creationTimeNat m k s) := by
      simpa only [creationTimeNat, hatom.2.1, dif_pos] using
        thresholdCreation_natFind hatom.2.1
    by_contra hn
    have hzero := Nat.eq_zero_of_not_pos hn
    have hsite := position_mem_thresholdSites_of_creation hk hcreationS
    have hlevel := (mem_thresholdSites s _ m _).mp hsite |>.2
    have hlocal : localTime s 0 (s 0) = 1 := by
      simp [localTime, localTimePrefix, pathPrefix]
    rw [hzero, hlocal] at hlevel
    omega
  have hcardEta := card_tilingCoordinatesAt_eq_source_of_fixedCode_eq
    hatom.1 hcreationPos eta.1.1 hatom.2.2.1
      ⟨b, hbrepresented⟩ hcompat
  have hexternal : Fintype.card (TilingCoordinatesAt t eta.1.1.start
      eta.1.1.retained ⟨b, hbrepresented⟩) < externalThreshold := by
    rw [hcardEta]
    exact hexternalS
  have hpredicate := broadSourceZeroDeltaBadPredicate_of_singleton_strong
    supportData eta hm hk cap width externalThreshold b hsingleton
    hbrepresented hcompat q.1 q.2.1 q.2.2
    (by simpa only [sq, v] using hbsourceQ)
    (by simpa only [sq, v] using hpartnerQ) hexternal
  refine ⟨hvalid', ?_⟩
  let qsource : PrefixedTilingAcceptedCappedCoordinates
      (truncatedLevelTime m k
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (data.coordinateCap cap) eta.1.1.tail.1
      (broadSourceZeroDeltaBadPredicate data width externalThreshold cap) :=
    ⟨q.1, hpredicate, q.2.2⟩
  apply Set.mem_iUnion.mpr
  refine ⟨qsource, ?_⟩
  simpa only [qsource, data, concreteFiber] using hq

end

end Erdos1165.HLOZCandidateLocalBroadThetaStrongSlotCapCover
