/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceAtomRecovery
import ErdosProblems.Erdos1165.TilingSourceTraceInvariant

/-!
# Creation records on a canonical source fibre

On a fixed source atom, changing only source-support coordinates changes the
path solely through sites which remain strictly below the creation level.
Consequently every creation record (site and complete prefix, after deleting
those subcritical sites) is fixed by the distinguished projection.
-/

namespace Erdos1165.HLOZSourceCreationRecordInvariant

open HLOZPathEvents HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedCanonicalSourceLowRecovery
open LazyDecomposition PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSourceTraceInvariant TilingSpatialInsertionFiber
open TilingThresholdHitRecordInvariant
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Every point in the literal source support is subcritical on a canonical
accepted reconstruction. -/
theorem sourceCanonical_localTime_lt_of_base_mem_support
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (hcanonical : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1)
    (y : Point) (hy : tilingBase t y ∈ eta.1.2) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    localTime (trajectory (extendPrefix (directionVectorOfList v)))
      v.length y < m := by
  classical
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  have hrepresented : tilingBase t y ∈
      tilingExternalDominoBases t eta.1.1.external.start
        eta.1.1.external.retained :=
    (SourceFiber eta).support_represented hy
  let b : TilingExternalDomino t eta.1.1.external.start
      eta.1.1.external.retained := ⟨tilingBase t y, hrepresented⟩
  have hbAway : b.1 ∉ supportComplementDistinguished t
      eta.1.1.external.start eta.1.1.external.retained eta.1.2 := by
    intro hb
    exact (Finset.mem_sdiff.mp hb).2 hy
  have hstrict := sourceCanonical_strictAway eta q hcanonical haccepted b hbAway
  have hends := prefixedTilingActualEndpointsBelow_of_max_add_total_lt
    eta.1.1.external.initial.1 t eta.1.1.external.start
    eta.1.1.external.retained (fun j ↦ (q j : ℕ))
    (sourceTerminal eta) m b hstrict
  have hstart : trajectory (extendPrefix (directionVectorOfList
      eta.1.1.external.initial.1)) eta.1.1.external.initial.1.length =
      eta.1.1.external.start := rfl
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath eta.1.1.external.initial.1
        eta.1.1.external.start
        (tilingInsertGapVector t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)))
        (sourceTerminal eta) := by
    simpa only [sourceTerminal_eq_coordinates eta q] using
      (finitePathList_prefixedTilingInsertionPrefix
        eta.1.1.external.initial t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        eta.1.1.external.tail hstart)
  have hlocal : localTime s v.length y < m := by
    rw [localTime_eq_listLocalTime, hpath]
    rcases point_eq_tilingBase_or_partner_base t y with hybase | hypartner
    · have : y = b.1 := hybase
      simpa only [this] using hends.1
    · have : y = tilingPartner t b.1 := hypartner
      simpa only [this] using hends.2
  simpa only [v, s] using hlocal

/-- Equal distinguished projections in one source atom have equal creation
sites and equal outside-source creation prefixes at every common rank. -/
theorem sourceCanonical_filtered_creation_record_eq
    {t : DominoTiling} {o : Orientation} {m k cap rank n n' : ℕ}
    (eta : SourceSupportedIndex t o m k) (hm : 1 < m)
    (hrank : 0 < rank)
    (q q' : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (hdist : (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q').1)
    (hcanonical : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1)
    (hcanonical' : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted' : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q' j : ℕ))
      eta.1.1.external.tail.1)
    (hcreation :
      let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
      ThresholdCreation (trajectory (extendPrefix (directionVectorOfList v)))
        m rank n)
    (hcreation' :
      let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
      ThresholdCreation (trajectory (extendPrefix (directionVectorOfList v')))
        m rank n')
    (hn : n ≤ (prefixedTilingInsertionPrefixList
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1).length)
    (hn' : n' ≤ (prefixedTilingInsertionPrefixList
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q' j : ℕ))
      eta.1.1.external.tail.1).length) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    let s' := trajectory (extendPrefix (directionVectorOfList v'))
    s n = s' n' ∧
      (finitePathList (pathPrefix s n)).filter
          (pointOutsideTilingBases t eta.1.2) =
        (finitePathList (pathPrefix s' n')).filter
          (pointOutsideTilingBases t eta.1.2) := by
  classical
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  have hstart : trajectory (extendPrefix (directionVectorOfList
      eta.1.1.external.initial.1)) eta.1.1.external.initial.1.length =
      eta.1.1.external.start := rfl
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath eta.1.1.external.initial.1
        eta.1.1.external.start
        (tilingInsertGapVector t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)))
        (sourceTerminal eta) := by
    simpa only [sourceTerminal_eq_coordinates eta q] using
      (finitePathList_prefixedTilingInsertionPrefix
        eta.1.1.external.initial t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        eta.1.1.external.tail hstart)
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      prefixedTilingPrefixPointPath eta.1.1.external.initial.1
        eta.1.1.external.start
        (tilingInsertGapVector t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q' j : ℕ)))
        (sourceTerminal eta) := by
    simpa only [sourceTerminal_eq_coordinates eta q'] using
      (finitePathList_prefixedTilingInsertionPrefix
        eta.1.1.external.initial t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q' j : ℕ))
        eta.1.1.external.tail hstart)
  have hfilter :
      (finitePathList (pathPrefix s v.length)).filter
          (pointOutsideTilingBases t eta.1.2) =
        (finitePathList (pathPrefix s' v'.length)).filter
          (pointOutsideTilingBases t eta.1.2) := by
    rw [hpath, hpath']
    exact filter_prefixedTilingPrefixPointPath_tilingInsertGapVector_outside_eq
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (sourceTerminal eta) eta.1.2 q q'
      hdist
  apply filtered_creation_record_eq (m := m) (rank := rank)
    (N := v.length) (N' := v'.length) (s := s) (s' := s')
    (by omega) hrank hcreation hcreation' hn hn'
    (pointOutsideTilingBases t eta.1.2) hfilter
  · intro y hy
    apply sourceCanonical_localTime_lt_of_base_mem_support eta q
      hcanonical haccepted y
    simpa [pointOutsideTilingBases] using hy
  · intro y hy
    apply sourceCanonical_localTime_lt_of_base_mem_support eta q'
      hcanonical' haccepted' y
    simpa [pointOutsideTilingBases] using hy

/-- The preceding theorem at the canonical clock of any rank already reached
by the accepted source reconstruction. -/
theorem sourceCanonical_creationTime_record_eq
    {t : DominoTiling} {o : Orientation} {m k cap rank : ℕ}
    (eta : SourceSupportedIndex t o m k) (hm : 1 < m)
    (hk : 0 < k) (hrank : 0 < rank) (hrank_le : rank ≤ k)
    (q q' : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (hdist : (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q').1)
    (hcanonical : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1)
    (hcanonical' : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted' : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q' j : ℕ))
      eta.1.1.external.tail.1) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    let s' := trajectory (extendPrefix (directionVectorOfList v'))
    s (creationTimeNat m rank s) = s' (creationTimeNat m rank s') ∧
      (finitePathList (pathPrefix s (creationTimeNat m rank s))).filter
          (pointOutsideTilingBases t eta.1.2) =
        (finitePathList (pathPrefix s'
          (creationTimeNat m rank s'))).filter
          (pointOutsideTilingBases t eta.1.2) := by
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  have hlt : v.length < orientedAllCreationCoordinateCutoff eta.1.1 cap :=
    prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1 cap q
  have hlt' : v'.length < orientedAllCreationCoordinateCutoff eta.1.1 cap :=
    prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1 cap q'
  have hcurrent : ThresholdCreation s m k v.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff eta.1.1 cap)
        v.length _ hlt).mp haccepted
  have hcurrent' : ThresholdCreation s' m k v'.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff eta.1.1 cap)
        v'.length _ hlt').mp haccepted'
  have hreachSpec : rank ≤ thresholdCount s v.length m :=
    hrank_le.trans hcurrent.1
  have hreachSpec' : rank ≤ thresholdCount s' v'.length m :=
    hrank_le.trans hcurrent'.1
  let hreach : ReachesThreshold s m rank := ⟨v.length, hreachSpec⟩
  let hreach' : ReachesThreshold s' m rank := ⟨v'.length, hreachSpec'⟩
  have hfind : ThresholdCreation s m rank (Nat.find hreach) :=
    thresholdCreation_natFind hreach
  have hfind' : ThresholdCreation s' m rank (Nat.find hreach') :=
    thresholdCreation_natFind hreach'
  have htime : creationTimeNat m rank s = Nat.find hreach :=
    creationTimeNat_eq_of_creation hfind
  have htime' : creationTimeNat m rank s' = Nat.find hreach' :=
    creationTimeNat_eq_of_creation hfind'
  have hcreation : ThresholdCreation s m rank (creationTimeNat m rank s) := by
    rw [htime]
    exact hfind
  have hcreation' : ThresholdCreation s' m rank
      (creationTimeNat m rank s') := by
    rw [htime']
    exact hfind'
  have hn : creationTimeNat m rank s ≤ v.length := by
    rw [htime]
    exact Nat.find_min' hreach hreachSpec
  have hn' : creationTimeNat m rank s' ≤ v'.length := by
    rw [htime']
    exact Nat.find_min' hreach' hreachSpec'
  exact sourceCanonical_filtered_creation_record_eq eta hm hrank q q' hdist
    hcanonical haccepted hcanonical' haccepted' hcreation hcreation' hn hn'

/-- Every positive rank already reached by an accepted canonical source
reconstruction is created at its canonical creation clock, before the end of
the reconstructed prefix. -/
theorem sourceCanonical_creationTime_data
    {t : DominoTiling} {o : Orientation} {m k cap rank : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (hrank : 0 < rank) (hrank_le : rank ≤ k)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    ThresholdCreation s m rank (creationTimeNat m rank s) ∧
      creationTimeNat m rank s ≤ v.length := by
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  have hlt : v.length < orientedAllCreationCoordinateCutoff eta.1.1 cap :=
    prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1 cap q
  have hcurrent : ThresholdCreation s m k v.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff eta.1.1 cap)
        v.length _ hlt).mp haccepted
  have hreachSpec : rank ≤ thresholdCount s v.length m :=
    hrank_le.trans hcurrent.1
  let hreach : ReachesThreshold s m rank := ⟨v.length, hreachSpec⟩
  have hfind : ThresholdCreation s m rank (Nat.find hreach) :=
    thresholdCreation_natFind hreach
  have htime : creationTimeNat m rank s = Nat.find hreach :=
    creationTimeNat_eq_of_creation hfind
  constructor
  · rw [htime]
    exact hfind
  · rw [htime]
    exact Nat.find_min' hreach hreachSpec

/-- The accepted endpoint of a canonical source reconstruction is precisely
the canonical creation clock of its source rank. -/
theorem sourceCanonical_creationTime_eq_length
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k) (hk : 0 < k)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    creationTimeNat m k s = v.length := by
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  have hlt : v.length < orientedAllCreationCoordinateCutoff eta.1.1 cap :=
    prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1 cap q
  have hcurrent : ThresholdCreation s m k v.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff eta.1.1 cap)
        v.length _ hlt).mp haccepted
  exact creationTimeNat_eq_of_creation hcurrent

/-- A level-`m` creation site cannot lie in the removable source support of
an accepted canonical source reconstruction. -/
theorem sourceCanonical_pointOutside_of_creation
    {t : DominoTiling} {o : Orientation} {m k cap rank n : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (hrank : 0 < rank)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (hcanonical : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1)
    (hcreation :
      let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
      ThresholdCreation (trajectory (extendPrefix (directionVectorOfList v)))
        m rank n)
    (hn : n ≤ (prefixedTilingInsertionPrefixList
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1).length) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    pointOutsideTilingBases t eta.1.2 (s n) = true := by
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  simp only [pointOutsideTilingBases, decide_eq_true_eq]
  intro hinside
  have hlow : localTime s v.length (s n) < m :=
    sourceCanonical_localTime_lt_of_base_mem_support eta q hcanonical
      haccepted (s n) hinside
  have hhigh : m ≤ localTime s n (s n) :=
    (mem_thresholdSites s n m (s n)).mp
      (position_mem_thresholdSites_of_creation hrank hcreation) |>.2
  have hmono : localTime s n (s n) ≤ localTime s v.length (s n) :=
    localTime_mono_time s (s n) hn
  omega

/-- A low-gap test is determined by the retained old-creation prefix and the
two creation sites, provided the new site survives the filter. -/
theorem lowGapDeficitFailure_iff_of_filtered_creation_records
    {s s' : WalkPath} {m nOld nOld' nNew nNew' : ℕ}
    (P : Point → Bool)
    (hOld : s nOld = s' nOld') (hNew : s nNew = s' nNew')
    (hprefix :
      (finitePathList (pathPrefix s nOld)).filter P =
        (finitePathList (pathPrefix s' nOld')).filter P)
    (hkeep : P (s nNew) = true) (hkeep' : P (s' nNew') = true) :
    lowGapDeficitFailure s m nOld nNew ↔
      lowGapDeficitFailure s' m nOld' nNew' := by
  have hcount :
      (finitePathList (pathPrefix s nOld)).count (s nNew) =
        (finitePathList (pathPrefix s' nOld')).count (s' nNew') := by
    have h := congrArg (fun p : List Point ↦ p.count (s nNew)) hprefix
    rw [List.count_filter hkeep, List.count_filter hkeep] at h
    exact h.trans (by rw [hNew])
  have hlocal : localTime s nOld (s nNew) =
      localTime s' nOld' (s' nNew') := by
    rw [localTime_eq_listLocalTime, localTime_eq_listLocalTime]
    exact hcount
  unfold lowGapDeficitFailure
  rw [hlocal, hOld, hNew]

/-- The low-gap predicate between two already reached creation ranks is
constant on a distinguished source-coordinate fibre. -/
theorem sourceCanonical_lowGapDeficitFailure_iff
    {t : DominoTiling} {o : Orientation} {m k cap oldRank newRank : ℕ}
    (eta : SourceSupportedIndex t o m k) (hm : 1 < m)
    (hold : 0 < oldRank) (hnew : 0 < newRank)
    (hold_le : oldRank ≤ k) (hnew_le : newRank ≤ k)
    (q q' : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (hdist : (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q').1)
    (hcanonical : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1)
    (hcanonical' : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted' : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q' j : ℕ))
      eta.1.1.external.tail.1) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    let s' := trajectory (extendPrefix (directionVectorOfList v'))
    lowGapDeficitFailure s m (creationTimeNat m oldRank s)
        (creationTimeNat m newRank s) ↔
      lowGapDeficitFailure s' m (creationTimeNat m oldRank s')
        (creationTimeNat m newRank s') := by
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  have hOld := sourceCanonical_creationTime_record_eq eta hm (by omega) hold
    hold_le q q' hdist hcanonical haccepted hcanonical' haccepted'
  have hNew := sourceCanonical_creationTime_record_eq eta hm (by omega) hnew
    hnew_le q q' hdist hcanonical haccepted hcanonical' haccepted'
  have hdata := sourceCanonical_creationTime_data eta hnew hnew_le q haccepted
  have hdata' := sourceCanonical_creationTime_data eta hnew hnew_le q' haccepted'
  have hkeep := sourceCanonical_pointOutside_of_creation eta hnew q hcanonical
    haccepted hdata.1 hdata.2
  have hkeep' := sourceCanonical_pointOutside_of_creation eta hnew q'
    hcanonical' haccepted' hdata'.1 hdata'.2
  exact lowGapDeficitFailure_iff_of_filtered_creation_records
    (pointOutsideTilingBases t eta.1.2) hOld.1 hNew.1 hOld.2 hkeep hkeep'

/-- The number of sites which have reached level `m+1` at the accepted
rank-`k` clock is fixed by the distinguished projection. -/
theorem sourceCanonical_thresholdCount_succ_eq
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (q q' : TilingCappedCoordinates eta.1.1.external.retainedCount cap)
    (hdist : (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q').1)
    (hcanonical : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail.1)
    (hcanonical' : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1))) ∈
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2)
    (haccepted' : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k (orientedAllCreationCoordinateCutoff eta.1.1 cap))
      eta.1.1.external.initial.1 t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q' j : ℕ))
      eta.1.1.external.tail.1) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
    thresholdCount (trajectory (extendPrefix (directionVectorOfList v)))
        v.length (m + 1) =
      thresholdCount (trajectory (extendPrefix (directionVectorOfList v')))
        v'.length (m + 1) := by
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  let v' := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
    (fun j ↦ (q' j : ℕ)) eta.1.1.external.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  have hbelow := sourceCanonical_strictAway eta q hcanonical haccepted
  have hbelow' := sourceCanonical_strictAway eta q' hcanonical' haccepted'
  have hsites := thresholdSites_prefixedTilingInsertionPrefix_eq_of_distinguished_eq
    eta.1.1.external.initial t eta.1.1.external.start
    eta.1.1.external.retained eta.1.1.external.tail (m + 1) (by omega)
    (supportComplementDistinguished t eta.1.1.external.start
      eta.1.1.external.retained eta.1.2) q q' rfl hdist
    (fun b hb ↦ by
      simpa only [sourceTerminal_eq_coordinates eta q] using
        (hbelow b hb).trans (Nat.lt_succ_self m))
    (fun b hb ↦ by
      simpa only [sourceTerminal_eq_coordinates eta q'] using
        (hbelow' b hb).trans (Nat.lt_succ_self m))
  unfold thresholdCount
  exact congrArg Finset.card hsites

end

end Erdos1165.HLOZSourceCreationRecordInvariant
