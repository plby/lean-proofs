import ErdosProblems.Erdos1165.TilingTypedFavoriteFactorization
import ErdosProblems.Erdos1165.TilingDistinguishedTraceInvariant
import ErdosProblems.Erdos1165.TilingFavoriteHistoryInvariant

/-!
# Typed all-six transition fibres

This module discharges the path-semantic part of the capped product law on
the genuinely retained, non-null tiling trace partition.  Physical creation
times are deliberately not part of the trace code: changing an away-domino
insertion coordinate can change that time.  Instead, the ordered sequence of
threshold hits recovers the rank-one, rank-two, and rank-three creation
locations from the stopped prefix.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.TilingTypedTransitionFactorization

open HLOZPathEvents HLOZStoppedProductRefinement
open HLOZStoppedSpatialScreening HLOZTracePartitionAdapter
open TilingStoppedProductDisintegration
open VariableStoppedTracePartition TilingVariableStoppedTracePartition
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingCappedMarginalization
open TilingFavoriteTraceSupport TilingTypedFavoriteTrace
open TilingTypedFavoriteFactorization TilingDistinguishedTraceInvariant
open TilingFavoriteHistoryInvariant
open TilingInsertionTerminalInvariant TilingStoppedAcceptanceFactorization
open PreStoppingFiber PreStoppingSpatialLaw SpatialInsertionFiber
open StoppedInsertion VariableStoppedFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

theorem stepPrefix_stepsOfWalk_eq_of_pathPrefix_eq
    {s s' : WalkPath} {N : ℕ} (hp : pathPrefix s N = pathPrefix s' N) :
    stepPrefix N (stepsOfWalk s) = stepPrefix N (stepsOfWalk s') := by
  funext j
  unfold stepPrefix stepsOfWalk
  have hj : (j : ℕ) ≤ N := Nat.le_of_lt j.isLt
  have hjsucc : (j : ℕ) + 1 ≤ N := Nat.succ_le_of_lt j.isLt
  rw [walkPoint_eq_of_pathPrefix_eq hp hj,
    walkPoint_eq_of_pathPrefix_eq hp hjsucc]

theorem fixedTilingExternalWordCode_eq_of_pathPrefix_eq
    (t : DominoTiling) {s s' : WalkPath} {N : ℕ}
    (hp : pathPrefix s N = pathPrefix s' N) :
    fixedTilingExternalWordCode t N s =
      fixedTilingExternalWordCode t N s' := by
  have hstep := stepPrefix_stepsOfWalk_eq_of_pathPrefix_eq hp
  unfold fixedTilingExternalWordCode prefixBlockWord prefixDirectionTail
    incrementPrefixList
  dsimp only
  apply Prod.ext
  · change deleteTilingBlocks t (0, 0)
        (pairDirectionList (List.ofFn (stepPrefix N (stepsOfWalk s)))) =
      deleteTilingBlocks t (0, 0)
        (pairDirectionList (List.ofFn (stepPrefix N (stepsOfWalk s'))))
    rw [hstep]
  · apply Subtype.ext
    change unpairedDirectionTail
        (List.ofFn (stepPrefix N (stepsOfWalk s))) =
      unpairedDirectionTail
        (List.ofFn (stepPrefix N (stepsOfWalk s')))
    rw [hstep]

theorem fixedTilingCreationFavoriteData_eq_of_pathPrefix_eq
    (t : DominoTiling) {s s' : WalkPath} {N : ℕ}
    (hp : pathPrefix s N = pathPrefix s' N) :
    fixedTilingCreationFavoriteData t N s =
      fixedTilingCreationFavoriteData t N s' := by
  unfold fixedTilingCreationFavoriteData favoriteSites
  rw [hp]
  have hend := walkPoint_eq_of_pathPrefix_eq hp (Nat.le_refl N)
  rw [hend]

/-- On one accepted stopped word, the cylinder predicate is equivalent to
the corresponding canonical reconstructed-path predicate whenever the stage
itself is fixed by that stopped prefix. -/
theorem typedStoppedFavoriteStageBase_iff_canonical
    (t : DominoTiling) (m k : ℕ) (hk : 0 < k)
    (stage : Set WalkPath) (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1)
    (hstage : ∀ omega,
      omega ∈ tilingStoppedInsertionAtom (typedStoppingTime m k z cap)
        t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
        (typedBoundaryTail z).1 →
      (trajectory omega ∈ stage ↔ typedInsertionWalk z q ∈ stage)) :
    typedStoppedFavoriteStageBasePredicate t m k stage z cap q ↔
      typedFavoriteStageBasePredicate t m k stage z q := by
  constructor
  · intro hbase
    exact typedStoppedFavoriteStageBase_canonical
      t m k stage z q hbase haccepted
  · intro hcanonical omega homega
    let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
    let s := typedInsertionWalk z q
    let s' := trajectory omega
    have hlt := tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q
    have hp : pathPrefix s' v.length = pathPrefix s v.length :=
      pathPrefix_eq_canonical_of_mem_tilingStoppedInsertionAtom
        t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
        (typedBoundaryTail z).1 omega homega
    have hcreation : ThresholdCreation s m k v.length :=
      (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
        m k (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z) hlt).mp haccepted
    have hcreation' : ThresholdCreation s' m k v.length :=
      (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
        m k (typedCoordinateCutoff z cap) v.length omega hlt).mp homega.1
    have htime : creationTimeNat m k s = v.length :=
      creationTimeNat_eq_of_creation hcreation
    have htime' : creationTimeNat m k s' = v.length :=
      creationTimeNat_eq_of_creation hcreation'
    have hcodes : tilingCreationExternalCode t m k s' =
          tilingCreationExternalCode t m k s ∧
        tilingCreationFavoriteData t m k s' =
          tilingCreationFavoriteData t m k s := by
      exact tilingCreationCodes_eq_of_fixedPrefixData t m k v.length v.length
        s' s htime' htime
        (fixedTilingExternalWordCode_eq_of_pathPrefix_eq t hp)
        (by unfold favoriteSites; rw [hp])
        (walkPoint_eq_of_pathPrefix_eq hp (Nat.le_refl v.length))
    have hpiece : s' ∈ favoriteTilingCreationPiece t m k
        (some (eraseTypedFavoriteTilingTraceCode t z)) := by
      apply (mem_favoriteTilingCreationPiece_some_iff_of_codes_eq
        t m k (eraseTypedFavoriteTilingTraceCode t z)
        ⟨v.length, hcreation'.1⟩ ⟨v.length, hcreation.1⟩
        (trajectory_mem_validStepWalk omega)
        (trajectory_mem_validStepWalk
          (extendPrefix (directionVectorOfList v)))
        hcodes.1 hcodes.2).2
      exact hcanonical.1.1
    have hlevel : levelFavorite s' m k ↔ levelFavorite s m k := by
      change levelFavorite (trajectory omega) m k ↔
        levelFavorite
          (trajectory (extendPrefix (directionVectorOfList v))) m k
      rw [levelFavorite_iff_nextLevel_zero_at_truncatedLevelTime
          m k (typedCoordinateCutoff z cap) v.length omega hk hlt homega.1,
        levelFavorite_iff_nextLevel_zero_at_truncatedLevelTime
          m k (typedCoordinateCutoff z cap) v.length
          (extendPrefix (directionVectorOfList v)) hk hlt haccepted]
      rw [thresholdCount_eq_of_pathPrefix_eq hp (Nat.le_refl v.length)]
      rfl
    change s' ∈ typedFavoriteTilingStagePiece t m k stage z ∩
      levelFavoriteSet m k
    refine ⟨⟨hpiece, (hstage omega homega).2 hcanonical.1.2⟩, ?_⟩
    exact hlevel.2 hcanonical.2

/-- The abstract true-screen used in `TypedStoppedStageScreeningData`
becomes the literal endpoint-domino truncation as soon as one coordinate is
known to belong to the stopped favorite fibre. -/
theorem typedDominoTruncation_of_stoppedBase_accepted
    (t : DominoTiling) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (stage : Set WalkPath) (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hbase : typedStoppedFavoriteStageBasePredicate t m k stage z cap q)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1)
    (hscreen : TilingAwayTotalsScreen t (0, 0) (typedRetained z)
      (typedDistinguished z) (typedPositiveAwayUpper t m z)
      (fun _ ↦ True)
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).2) :
    TilingInsertedLocalTime.TilingDominoTruncation t (0, 0)
      (typedRetained z)
      (tilingInsertionTerminal t (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z))
      m (typedDistinguished z) (fun j ↦ (q j : ℕ)) := by
  have hcanonical := typedStoppedFavoriteStageBase_canonical
    t m k stage z q hbase haccepted
  have hupper := typedPositiveAwayUpper_eq_of_base_accepted
    t m k hm hk stage z q hcanonical haccepted
  rw [hupper] at hscreen
  rw [tilingInsertionTerminal_eq_typedInsertionTerminal z q]
  exact (tilingAwayTotalsScreen_true_iff_dominoTruncation
    (cap := cap) t (0, 0) (typedRetained z)
    (typedInsertionTerminal t z)
    m (typedDistinguished z) q).mp hscreen

/-- The same conversion for another coordinate once the positive cutoff has
been identified from a known stopped-base coordinate. -/
theorem typedDominoTruncation_of_trueScreen_of_upper_eq
    (t : DominoTiling) (m : ℕ)
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hupper : typedPositiveAwayUpper t m z = typedFavoriteAwayUpper t m z)
    (hscreen : TilingAwayTotalsScreen t (0, 0) (typedRetained z)
      (typedDistinguished z) (typedPositiveAwayUpper t m z)
      (fun _ ↦ True)
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).2) :
    TilingInsertedLocalTime.TilingDominoTruncation t (0, 0)
      (typedRetained z)
      (tilingInsertionTerminal t (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z))
      m (typedDistinguished z) (fun j ↦ (q j : ℕ)) := by
  rw [hupper] at hscreen
  rw [tilingInsertionTerminal_eq_typedInsertionTerminal z q]
  exact (tilingAwayTotalsScreen_true_iff_dominoTruncation
    (cap := cap) t (0, 0) (typedRetained z)
    (typedInsertionTerminal t z)
    m (typedDistinguished z) q).mp hscreen

theorem typedStoppedFirstCreationBase_iff_canonical
    (t : DominoTiling) (m : ℕ)
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m 1 z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    typedStoppedFavoriteStageBasePredicate t m 1 (firstCreationStage m)
        z cap q ↔
      typedFavoriteStageBasePredicate t m 1 (firstCreationStage m) z q := by
  apply typedStoppedFavoriteStageBase_iff_canonical
    t m 1 (by omega) (firstCreationStage m) z q haccepted
  intro omega homega
  exact firstCreationStage_iff_canonical_of_mem_tilingStoppedInsertionAtom
    t m (typedCoordinateCutoff z cap) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z) haccepted
    (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q)
    omega homega

theorem typedStoppedFirstTransitionBase_iff_canonical
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m 2 z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    typedStoppedFavoriteStageBasePredicate t m 2
        (firstTransitionEvent t m a) z cap q ↔
      typedFavoriteStageBasePredicate t m 2
        (firstTransitionEvent t m a) z q := by
  apply typedStoppedFavoriteStageBase_iff_canonical
    t m 2 (by omega) (firstTransitionEvent t m a) z q haccepted
  intro omega homega
  exact firstTransitionEvent_iff_canonical_of_mem_tilingStoppedInsertionAtom
    t m (typedCoordinateCutoff z cap) a (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z) haccepted
    (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q)
    omega homega

theorem typedStoppedSecondTransitionBase_iff_canonical
    (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m 3 z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    typedStoppedFavoriteStageBasePredicate t m 3
        (secondTransitionEvent t m a) z cap q ↔
      typedFavoriteStageBasePredicate t m 3
        (secondTransitionEvent t m a) z q := by
  apply typedStoppedFavoriteStageBase_iff_canonical
    t m 3 (by omega) (secondTransitionEvent t m a) z q haccepted
  intro omega homega
  exact secondTransitionEvent_iff_canonical_of_mem_tilingStoppedInsertionAtom
    t m (typedCoordinateCutoff z cap) a (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z) haccepted
    (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q)
    omega homega

/-- The favorite-base component recorded in a typed trace is exactly the
literal favorite-base set at its accepted canonical stopping word. -/
theorem favoriteTilingBases_eq_typedDistinguished_of_base_accepted
    (t : DominoTiling) (m k : ℕ)
    (stage : Set WalkPath) (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hbase : typedFavoriteStageBasePredicate t m k stage z q)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
    favoriteTilingBases t (typedInsertionWalk z q) v.length =
      typedDistinguished z := by
  let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
  let s := typedInsertionWalk z q
  have hcreation : ThresholdCreation s m k v.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m k (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z)
      (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q)).mp
        haccepted
  have hdata := hbase.1.1.2
  change fixedTilingCreationFavoriteData t (creationTimeNat m k s) s =
    (eraseTypedFavoriteTilingTraceCode t z).2 at hdata
  rw [creationTimeNat_eq_of_creation hcreation] at hdata
  exact congrArg (fun data : TilingCreationFavoriteData ↦ data.1.2) hdata

/-- Once acceptance and strict away support have been transported, the
trace-code and level-favorite parts of the canonical base predicate are
coordinate invariant.  Only the transition-stage predicate remains for the
rank-specific history argument. -/
theorem typedFavoriteStageBase_transfer
    (t : DominoTiling) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (stage : Set WalkPath) (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q q' : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q').1)
    (htrunc : TilingInsertedLocalTime.TilingDominoTruncation t (0, 0)
      (typedRetained z)
      (tilingInsertionTerminal t (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z))
      m (typedDistinguished z) (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingInsertedLocalTime.TilingDominoTruncation t (0, 0)
      (typedRetained z)
      (tilingInsertionTerminal t (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z))
      m (typedDistinguished z) (fun j ↦ (q' j : ℕ)))
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1)
    (haccepted' : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q' j : ℕ))
      (typedBoundaryTail z).1)
    (hstage : levelFavorite (typedInsertionWalk z q') m k →
      typedInsertionWalk z q ∈ stage →
      typedInsertionWalk z q' ∈ stage)
    (hbase : typedFavoriteStageBasePredicate t m k stage z q) :
    typedFavoriteStageBasePredicate t m k stage z q' := by
  let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
  let v' := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q' j : ℕ)) (typedBoundaryTail z).1
  let s := typedInsertionWalk z q
  let s' := typedInsertionWalk z q'
  have hlt := tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q
  have hlt' := tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q'
  have hfavorite' : levelFavorite s' m k :=
    (levelFavorite_tilingInsertionPrefix_iff_of_distinguished_eq_canonical
      t m k (typedCoordinateCutoff z cap) hk (typedRetained z)
      (typedBoundaryTail z) (typedDistinguished z) q q' hdist htrunc htrunc'
      haccepted haccepted' hlt hlt').mp hbase.2
  have hsites : favoriteSites s v.length = favoriteSites s' v'.length :=
    favoriteSites_tilingInsertionPrefix_eq_of_distinguished_eq
      t m k (typedCoordinateCutoff z cap) hm hk (typedRetained z)
      (typedBoundaryTail z)
      (tilingInsertionTerminal t (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z))
      (typedDistinguished z) q q' rfl
      ((tilingInsertionTerminal_eq_of_coordinates t (typedRetained z)
        (fun j ↦ (q j : ℕ)) (fun j ↦ (q' j : ℕ))
        (typedBoundaryTail z)).symm)
      hdist htrunc htrunc' haccepted haccepted' hbase.2 hfavorite' hlt hlt'
  have hcreation : ThresholdCreation s m k v.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m k (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z) hlt).mp haccepted
  have hcreation' : ThresholdCreation s' m k v'.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m k (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q' j : ℕ)) (typedBoundaryTail z) hlt').mp haccepted'
  have hcodes : tilingCreationExternalCode t m k s =
        tilingCreationExternalCode t m k s' ∧
      tilingCreationFavoriteData t m k s =
        tilingCreationFavoriteData t m k s' := by
    exact tilingCreationCodes_eq_of_fixedPrefixData t m k v.length v'.length
      s s' (creationTimeNat_eq_of_creation hcreation)
      (creationTimeNat_eq_of_creation hcreation')
      (fixedTilingExternalWordCode_insertionCoordinates_eq
        t (typedRetained z) (typedBoundaryTail z) q q')
      hsites
      (canonical_tilingInsertion_endpoint_eq_of_coordinates
        t (typedRetained z) (fun j ↦ (q j : ℕ))
        (fun j ↦ (q' j : ℕ)) (typedBoundaryTail z))
  have hpiece' : s' ∈ favoriteTilingCreationPiece t m k
      (some (eraseTypedFavoriteTilingTraceCode t z)) := by
    apply (mem_favoriteTilingCreationPiece_some_iff_of_codes_eq
      t m k (eraseTypedFavoriteTilingTraceCode t z)
      ⟨v.length, hcreation.1⟩ ⟨v'.length, hcreation'.1⟩
      (trajectory_mem_validStepWalk
        (extendPrefix (directionVectorOfList v)))
      (trajectory_mem_validStepWalk
        (extendPrefix (directionVectorOfList v')))
      hcodes.1 hcodes.2).mp
    exact hbase.1.1
  exact ⟨⟨hpiece', hstage hfavorite' hbase.1.2⟩, hfavorite'⟩

theorem firstCreationStage_transfer
    (t : DominoTiling) (m : ℕ)
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q' : TilingCappedCoordinates (typedRetainedCount z) cap)
    (haccepted' : TilingStoppingAccepted (typedStoppingTime m 1 z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q' j : ℕ))
      (typedBoundaryTail z).1) :
    typedInsertionWalk z q' ∈ firstCreationStage m := by
  let v' := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q' j : ℕ)) (typedBoundaryTail z).1
  have hcreation' : ThresholdCreation (typedInsertionWalk z q') m 1 v'.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m 1 (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q' j : ℕ)) (typedBoundaryTail z)
      (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q')).mp
        haccepted'
  exact Set.mem_iUnion.mpr ⟨v'.length, hcreation'⟩

theorem firstTransitionEvent_transfer
    (t : DominoTiling) (m : ℕ) (hm : 0 < m)
    (a : (GapScale × GapScale) × GapScale)
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q q' : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hD :
      let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
      favoriteTilingBases t (typedInsertionWalk z q) v.length =
        typedDistinguished z)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q').1)
    (htrunc : TilingInsertedLocalTime.TilingDominoTruncation t (0, 0)
      (typedRetained z)
      (tilingInsertionTerminal t (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z))
      m (typedDistinguished z) (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingInsertedLocalTime.TilingDominoTruncation t (0, 0)
      (typedRetained z)
      (tilingInsertionTerminal t (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z))
      m (typedDistinguished z) (fun j ↦ (q' j : ℕ)))
    (haccepted : TilingStoppingAccepted (typedStoppingTime m 2 z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1)
    (haccepted' : TilingStoppingAccepted (typedStoppingTime m 2 z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q' j : ℕ))
      (typedBoundaryTail z).1)
    (hfavorite : levelFavorite (typedInsertionWalk z q) m 2)
    (hfavorite' : levelFavorite (typedInsertionWalk z q') m 2)
    (hstage : typedInsertionWalk z q ∈ firstTransitionEvent t m a) :
    typedInsertionWalk z q' ∈ firstTransitionEvent t m a := by
  let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
  let v' := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q' j : ℕ)) (typedBoundaryTail z).1
  let s := typedInsertionWalk z q
  let s' := typedInsertionWalk z q'
  have hlt := tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q
  have hlt' := tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q'
  have hcreation2 : ThresholdCreation s m 2 v.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m 2 (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z) hlt).mp haccepted
  have hcreation2' : ThresholdCreation s' m 2 v'.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m 2 (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q' j : ℕ)) (typedBoundaryTail z) hlt').mp haccepted'
  simp only [firstTransitionEvent, Set.mem_iUnion] at hstage ⊢
  rcases hstage with ⟨n₁, n₂, hpair⟩
  have hn₂ : n₂ = v.length :=
    HLOZSpatialAdapter.thresholdCreation_time_unique hpair.2.1 hcreation2
  subst n₂
  let hreach1' : ReachesThreshold s' m 1 := ⟨v'.length,
    (show 1 ≤ thresholdCount s' v'.length m by
      exact (by omega : 1 ≤ 2).trans hcreation2'.1)⟩
  let n₁' := Nat.find hreach1'
  have hcreation1' : ThresholdCreation s' m 1 n₁' :=
    thresholdCreation_natFind hreach1'
  have hn₁ : n₁ ≤ v.length :=
    (creation_time_lt (by omega) (by omega) (by omega)
      hpair.1 hcreation2).le
  have hn₁' : n₁' ≤ v'.length := by
    apply Nat.find_min' hreach1'
    exact (by omega : 1 ≤ 2).trans hcreation2'.1
  have hloc1 : s n₁ = s' n₁' :=
    canonical_creation_location_eq_of_favorite_trace
      t m 2 1 (typedCoordinateCutoff z cap) hm (by omega) (by omega)
      (typedRetained z) (typedBoundaryTail z) (typedDistinguished z)
      q q' hD hdist htrunc htrunc' haccepted hfavorite hlt
      hpair.1 hcreation1' hn₁ hn₁'
  have hend : s v.length = s' v'.length :=
    canonical_tilingInsertion_endpoint_eq_of_coordinates
      t (typedRetained z) (fun j ↦ (q j : ℕ))
      (fun j ↦ (q' j : ℕ)) (typedBoundaryTail z)
  have hnext' : thresholdCount s' v'.length (m + 1) = 0 :=
    (levelFavorite_iff_nextLevel_zero_at_truncatedLevelTime
      m 2 (typedCoordinateCutoff z cap) v'.length
      (extendPrefix (directionVectorOfList v')) (by omega) hlt'
      haccepted').mp hfavorite'
  refine ⟨n₁', v'.length, hcreation1', hcreation2', hnext', ?_⟩
  change ¬Tilings.sameDomino t (s' n₁') (s' v'.length) ∧
    gapScaleOf m (s' n₁') (s' v'.length) = a.1.1
  rw [← hloc1, ← hend]
  exact hpair.2.2.2

theorem secondTransitionEvent_transfer
    (t : DominoTiling) (m : ℕ) (hm : 0 < m)
    (a : (GapScale × GapScale) × GapScale)
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q q' : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hD :
      let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
      favoriteTilingBases t (typedInsertionWalk z q) v.length =
        typedDistinguished z)
    (hdist : (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q').1)
    (htrunc : TilingInsertedLocalTime.TilingDominoTruncation t (0, 0)
      (typedRetained z)
      (tilingInsertionTerminal t (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z))
      m (typedDistinguished z) (fun j ↦ (q j : ℕ)))
    (htrunc' : TilingInsertedLocalTime.TilingDominoTruncation t (0, 0)
      (typedRetained z)
      (tilingInsertionTerminal t (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z))
      m (typedDistinguished z) (fun j ↦ (q' j : ℕ)))
    (haccepted : TilingStoppingAccepted (typedStoppingTime m 3 z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1)
    (haccepted' : TilingStoppingAccepted (typedStoppingTime m 3 z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q' j : ℕ))
      (typedBoundaryTail z).1)
    (hfavorite : levelFavorite (typedInsertionWalk z q) m 3)
    (hfavorite' : levelFavorite (typedInsertionWalk z q') m 3)
    (hstage : typedInsertionWalk z q ∈ secondTransitionEvent t m a) :
    typedInsertionWalk z q' ∈ secondTransitionEvent t m a := by
  let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
  let v' := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q' j : ℕ)) (typedBoundaryTail z).1
  let s := typedInsertionWalk z q
  let s' := typedInsertionWalk z q'
  have hlt := tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q
  have hlt' := tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q'
  have hcreation3 : ThresholdCreation s m 3 v.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m 3 (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z) hlt).mp haccepted
  have hcreation3' : ThresholdCreation s' m 3 v'.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m 3 (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q' j : ℕ)) (typedBoundaryTail z) hlt').mp haccepted'
  simp only [secondTransitionEvent, Set.mem_iUnion] at hstage ⊢
  rcases hstage with ⟨n₁, n₂, n₃, htriple⟩
  have hn₃ : n₃ = v.length :=
    HLOZSpatialAdapter.thresholdCreation_time_unique htriple.2.2.1 hcreation3
  subst n₃
  let hreach1' : ReachesThreshold s' m 1 := ⟨v'.length,
    (show 1 ≤ thresholdCount s' v'.length m by
      exact (by omega : 1 ≤ 3).trans hcreation3'.1)⟩
  let hreach2' : ReachesThreshold s' m 2 := ⟨v'.length,
    (show 2 ≤ thresholdCount s' v'.length m by
      exact (by omega : 2 ≤ 3).trans hcreation3'.1)⟩
  let n₁' := Nat.find hreach1'
  let n₂' := Nat.find hreach2'
  have hcreation1' : ThresholdCreation s' m 1 n₁' :=
    thresholdCreation_natFind hreach1'
  have hcreation2' : ThresholdCreation s' m 2 n₂' :=
    thresholdCreation_natFind hreach2'
  have hn₁ : n₁ ≤ v.length :=
    (creation_time_lt (by omega) (by omega) (by omega)
      htriple.1 hcreation3).le
  have hn₂ : n₂ ≤ v.length :=
    (creation_time_lt (by omega) (by omega) (by omega)
      htriple.2.1 hcreation3).le
  have hn₁' : n₁' ≤ v'.length := by
    apply Nat.find_min' hreach1'
    exact (by omega : 1 ≤ 3).trans hcreation3'.1
  have hn₂' : n₂' ≤ v'.length := by
    apply Nat.find_min' hreach2'
    exact (by omega : 2 ≤ 3).trans hcreation3'.1
  have hloc1 : s n₁ = s' n₁' :=
    canonical_creation_location_eq_of_favorite_trace
      t m 3 1 (typedCoordinateCutoff z cap) hm (by omega) (by omega)
      (typedRetained z) (typedBoundaryTail z) (typedDistinguished z)
      q q' hD hdist htrunc htrunc' haccepted hfavorite hlt
      htriple.1 hcreation1' hn₁ hn₁'
  have hloc2 : s n₂ = s' n₂' :=
    canonical_creation_location_eq_of_favorite_trace
      t m 3 2 (typedCoordinateCutoff z cap) hm (by omega) (by omega)
      (typedRetained z) (typedBoundaryTail z) (typedDistinguished z)
      q q' hD hdist htrunc htrunc' haccepted hfavorite hlt
      htriple.2.1 hcreation2' hn₂ hn₂'
  have hend : s v.length = s' v'.length :=
    canonical_tilingInsertion_endpoint_eq_of_coordinates
      t (typedRetained z) (fun j ↦ (q j : ℕ))
      (fun j ↦ (q' j : ℕ)) (typedBoundaryTail z)
  have hnext' : thresholdCount s' v'.length (m + 1) = 0 :=
    (levelFavorite_iff_nextLevel_zero_at_truncatedLevelTime
      m 3 (typedCoordinateCutoff z cap) v'.length
      (extendPrefix (directionVectorOfList v')) (by omega) hlt'
      haccepted').mp hfavorite'
  refine ⟨n₁', n₂', v'.length, hcreation1', hcreation2', hcreation3',
    hnext', ?_⟩
  change ¬Tilings.sameDomino t (s' n₁') (s' n₂') ∧
    ¬Tilings.sameDomino t (s' n₁') (s' v'.length) ∧
    ¬Tilings.sameDomino t (s' n₂') (s' v'.length) ∧
    gapScaleOf m (s' n₁') (s' n₂') = a.1.1 ∧
    gapScaleOf m (s' n₂') (s' v'.length) = a.1.2
  rw [← hloc1, ← hloc2, ← hend]
  exact htriple.2.2.2.2

/-! ## Exact stopped-base invariance for the three stages -/

theorem typedFirstCreationStoppedInvariant
    (t : DominoTiling) (m : ℕ) (hm : 1 < m) :
    ∀ (z : TypedFavoriteTilingTraceCode t) cap q q',
    (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q').1 →
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
        (typedDistinguished z) (typedPositiveAwayUpper t m z)
        (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q).2 →
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
        (typedDistinguished z) (typedPositiveAwayUpper t m z)
        (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q').2 →
    (typedStoppedFavoriteStageBasePredicate t m 1 (firstCreationStage m)
          z cap q ∧
        TilingStoppingAccepted (typedStoppingTime m 1 z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
          (typedBoundaryTail z).1 ↔
      typedStoppedFavoriteStageBasePredicate t m 1 (firstCreationStage m)
          z cap q' ∧
        TilingStoppingAccepted (typedStoppingTime m 1 z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q' j : ℕ))
          (typedBoundaryTail z).1) := by
  intro z cap q q' hdist hscreen hscreen'
  have transfer : ∀ (u u' : TilingCappedCoordinates
      (typedRetainedCount z) cap),
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) u).1 =
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) u').1 →
      TilingAwayTotalsScreen t (0, 0) (typedRetained z)
          (typedDistinguished z) (typedPositiveAwayUpper t m z)
          (fun _ ↦ True)
          (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
            (typedDistinguished z) u).2 →
      TilingAwayTotalsScreen t (0, 0) (typedRetained z)
          (typedDistinguished z) (typedPositiveAwayUpper t m z)
          (fun _ ↦ True)
          (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
            (typedDistinguished z) u').2 →
      typedStoppedFavoriteStageBasePredicate t m 1 (firstCreationStage m)
          z cap u ∧
        TilingStoppingAccepted (typedStoppingTime m 1 z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (u j : ℕ))
          (typedBoundaryTail z).1 →
      typedStoppedFavoriteStageBasePredicate t m 1 (firstCreationStage m)
          z cap u' ∧
        TilingStoppingAccepted (typedStoppingTime m 1 z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (u' j : ℕ))
          (typedBoundaryTail z).1 := by
    intro u u' hdistU hscreenU hscreenU' hu
    have hcanonical := (typedStoppedFirstCreationBase_iff_canonical
      t m z u hu.2).mp hu.1
    have hupper := typedPositiveAwayUpper_eq_of_base_accepted
      t m 1 (by omega) (by omega) (firstCreationStage m) z u
      hcanonical hu.2
    have htrunc := typedDominoTruncation_of_stoppedBase_accepted
      t m 1 (by omega) (by omega) (firstCreationStage m) z u
      hu.1 hu.2 hscreenU
    have htrunc' := typedDominoTruncation_of_trueScreen_of_upper_eq
      t m z u' hupper hscreenU'
    rw [← tilingInsertionTerminal_eq_of_coordinates t (typedRetained z)
      (fun j ↦ (u j : ℕ)) (fun j ↦ (u' j : ℕ))
      (typedBoundaryTail z)] at htrunc'
    have hend := typedInsertionEndpoint_base_mem_distinguished
      t m 1 (by omega) (firstCreationStage m) z u hcanonical hu.2
    have haccepted' :=
      (tilingStoppingAccepted_iff_of_distinguished_eq_of_truncated_one_lt
        t m 1 (typedCoordinateCutoff z cap) hm (by omega)
        (typedRetained z) (typedBoundaryTail z) (typedDistinguished z)
        u u' hend hdistU htrunc htrunc'
        (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap u)
        (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap u')).mp hu.2
    have hcanonical' := typedFavoriteStageBase_transfer
      t m 1 (by omega) (by omega) (firstCreationStage m) z u u'
      hdistU htrunc htrunc' hu.2 haccepted'
      (fun _ _ ↦ firstCreationStage_transfer t m z u' haccepted')
      hcanonical
    exact ⟨(typedStoppedFirstCreationBase_iff_canonical
      t m z u' haccepted').mpr hcanonical', haccepted'⟩
  exact ⟨transfer q q' hdist hscreen hscreen',
    transfer q' q hdist.symm hscreen' hscreen⟩

/-- Generic lifting from a rank-specific canonical stage transport to the
literal cylinder-level conjunction used by the factored mass theorem. -/
theorem typedStoppedStageInvariant_of_canonical_transfer
    (t : DominoTiling) (m k : ℕ) (hm : 1 < m) (hk : 0 < k)
    (stage : Set WalkPath)
    (hcylinder : ∀ (z : TypedFavoriteTilingTraceCode t) cap
      (q : TilingCappedCoordinates (typedRetainedCount z) cap),
      TilingStoppingAccepted (typedStoppingTime m k z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
          (typedBoundaryTail z).1 →
      (typedStoppedFavoriteStageBasePredicate t m k stage z cap q ↔
        typedFavoriteStageBasePredicate t m k stage z q))
    (hstageTransfer : ∀ (z : TypedFavoriteTilingTraceCode t) cap
      (q q' : TilingCappedCoordinates (typedRetainedCount z) cap),
      (let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
          (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1;
        favoriteTilingBases t (typedInsertionWalk z q) v.length =
          typedDistinguished z) →
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q).1 =
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q').1 →
      TilingInsertedLocalTime.TilingDominoTruncation t (0, 0)
        (typedRetained z)
        (tilingInsertionTerminal t (typedRetained z)
          (fun j ↦ (q j : ℕ)) (typedBoundaryTail z))
        m (typedDistinguished z) (fun j ↦ (q j : ℕ)) →
      TilingInsertedLocalTime.TilingDominoTruncation t (0, 0)
        (typedRetained z)
        (tilingInsertionTerminal t (typedRetained z)
          (fun j ↦ (q j : ℕ)) (typedBoundaryTail z))
        m (typedDistinguished z) (fun j ↦ (q' j : ℕ)) →
      TilingStoppingAccepted (typedStoppingTime m k z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
          (typedBoundaryTail z).1 →
      TilingStoppingAccepted (typedStoppingTime m k z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q' j : ℕ))
          (typedBoundaryTail z).1 →
      levelFavorite (typedInsertionWalk z q) m k →
      levelFavorite (typedInsertionWalk z q') m k →
      typedInsertionWalk z q ∈ stage → typedInsertionWalk z q' ∈ stage) :
    ∀ (z : TypedFavoriteTilingTraceCode t) cap q q',
    (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q').1 →
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
        (typedDistinguished z) (typedPositiveAwayUpper t m z)
        (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q).2 →
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
        (typedDistinguished z) (typedPositiveAwayUpper t m z)
        (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q').2 →
    (typedStoppedFavoriteStageBasePredicate t m k stage z cap q ∧
        TilingStoppingAccepted (typedStoppingTime m k z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
          (typedBoundaryTail z).1 ↔
      typedStoppedFavoriteStageBasePredicate t m k stage z cap q' ∧
        TilingStoppingAccepted (typedStoppingTime m k z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q' j : ℕ))
          (typedBoundaryTail z).1) := by
  intro z cap q q' hdist hscreen hscreen'
  have transfer : ∀ (u u' : TilingCappedCoordinates
      (typedRetainedCount z) cap),
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) u).1 =
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) u').1 →
      TilingAwayTotalsScreen t (0, 0) (typedRetained z)
          (typedDistinguished z) (typedPositiveAwayUpper t m z)
          (fun _ ↦ True)
          (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
            (typedDistinguished z) u).2 →
      TilingAwayTotalsScreen t (0, 0) (typedRetained z)
          (typedDistinguished z) (typedPositiveAwayUpper t m z)
          (fun _ ↦ True)
          (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
            (typedDistinguished z) u').2 →
      typedStoppedFavoriteStageBasePredicate t m k stage z cap u ∧
        TilingStoppingAccepted (typedStoppingTime m k z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (u j : ℕ))
          (typedBoundaryTail z).1 →
      typedStoppedFavoriteStageBasePredicate t m k stage z cap u' ∧
        TilingStoppingAccepted (typedStoppingTime m k z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (u' j : ℕ))
          (typedBoundaryTail z).1 := by
    intro u u' hdistU hscreenU hscreenU' hu
    have hcanonical := (hcylinder z cap u hu.2).mp hu.1
    have hupper := typedPositiveAwayUpper_eq_of_base_accepted
      t m k (by omega) hk stage z u hcanonical hu.2
    have htrunc := typedDominoTruncation_of_stoppedBase_accepted
      t m k (by omega) hk stage z u hu.1 hu.2 hscreenU
    have htrunc' := typedDominoTruncation_of_trueScreen_of_upper_eq
      t m z u' hupper hscreenU'
    rw [← tilingInsertionTerminal_eq_of_coordinates t (typedRetained z)
      (fun j ↦ (u j : ℕ)) (fun j ↦ (u' j : ℕ))
      (typedBoundaryTail z)] at htrunc'
    have hend := typedInsertionEndpoint_base_mem_distinguished
      t m k hk stage z u hcanonical hu.2
    have haccepted' :=
      (tilingStoppingAccepted_iff_of_distinguished_eq_of_truncated_one_lt
        t m k (typedCoordinateCutoff z cap) hm hk
        (typedRetained z) (typedBoundaryTail z) (typedDistinguished z)
        u u' hend hdistU htrunc htrunc'
        (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap u)
        (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap u')).mp hu.2
    have hD := favoriteTilingBases_eq_typedDistinguished_of_base_accepted
      t m k stage z u hcanonical hu.2
    have hcanonical' := typedFavoriteStageBase_transfer
      t m k (by omega) hk stage z u u' hdistU htrunc htrunc'
      hu.2 haccepted'
      (fun hfavorite' hstage ↦ hstageTransfer z cap u u' hD hdistU
        htrunc htrunc' hu.2 haccepted' hcanonical.2 hfavorite' hstage)
      hcanonical
    exact ⟨(hcylinder z cap u' haccepted').mpr hcanonical', haccepted'⟩
  exact ⟨transfer q q' hdist hscreen hscreen',
    transfer q' q hdist.symm hscreen' hscreen⟩

theorem typedFirstTransitionStoppedInvariant
    (t : DominoTiling) (m : ℕ) (hm : 1 < m)
    (a : (GapScale × GapScale) × GapScale) :
    ∀ (z : TypedFavoriteTilingTraceCode t) cap q q',
    (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q').1 →
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
        (typedDistinguished z) (typedPositiveAwayUpper t m z)
        (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q).2 →
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
        (typedDistinguished z) (typedPositiveAwayUpper t m z)
        (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q').2 →
    (typedStoppedFavoriteStageBasePredicate t m 2
          (firstTransitionEvent t m a) z cap q ∧
        TilingStoppingAccepted (typedStoppingTime m 2 z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
          (typedBoundaryTail z).1 ↔
      typedStoppedFavoriteStageBasePredicate t m 2
          (firstTransitionEvent t m a) z cap q' ∧
        TilingStoppingAccepted (typedStoppingTime m 2 z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q' j : ℕ))
          (typedBoundaryTail z).1) := by
  apply typedStoppedStageInvariant_of_canonical_transfer
    t m 2 hm (by omega) (firstTransitionEvent t m a)
  · intro z cap q haccepted
    exact typedStoppedFirstTransitionBase_iff_canonical
      t m a z q haccepted
  · intro z cap q q' hD hdist htrunc htrunc' haccepted haccepted'
      hfavorite hfavorite' hstage
    exact firstTransitionEvent_transfer t m (by omega) a z q q' hD hdist
      htrunc htrunc' haccepted haccepted' hfavorite hfavorite' hstage

theorem typedSecondTransitionStoppedInvariant
    (t : DominoTiling) (m : ℕ) (hm : 1 < m)
    (a : (GapScale × GapScale) × GapScale) :
    ∀ (z : TypedFavoriteTilingTraceCode t) cap q q',
    (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q').1 →
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
        (typedDistinguished z) (typedPositiveAwayUpper t m z)
        (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q).2 →
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
        (typedDistinguished z) (typedPositiveAwayUpper t m z)
        (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q').2 →
    (typedStoppedFavoriteStageBasePredicate t m 3
          (secondTransitionEvent t m a) z cap q ∧
        TilingStoppingAccepted (typedStoppingTime m 3 z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
          (typedBoundaryTail z).1 ↔
      typedStoppedFavoriteStageBasePredicate t m 3
          (secondTransitionEvent t m a) z cap q' ∧
        TilingStoppingAccepted (typedStoppingTime m 3 z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q' j : ℕ))
          (typedBoundaryTail z).1) := by
  apply typedStoppedStageInvariant_of_canonical_transfer
    t m 3 hm (by omega) (secondTransitionEvent t m a)
  · intro z cap q haccepted
    exact typedStoppedSecondTransitionBase_iff_canonical
      t m a z q haccepted
  · intro z cap q q' hD hdist htrunc htrunc' haccepted haccepted'
      hfavorite hfavorite' hstage
    exact secondTransitionEvent_transfer t m (by omega) a z q q' hD hdist
      htrunc htrunc' haccepted haccepted' hfavorite hfavorite' hstage

/-! ## Constructors with only the finite away-total screen left -/

/-- Residual data after the complete stopped spatial fibre has been
identified.  These fields refer only to the finite away-total screen: its
cap coherence, path coverage, and finite product mass. -/
structure TypedFiniteAwayScreenData
    (t : DominoTiling) (m k : ℕ) (stage next : Set WalkPath)
    (cost : ℝ≥0∞) where
  accepts : ∀ z : TypedFavoriteTilingTraceCode t, ∀ cap,
    FiniteDominoProductLaw.TruncatedTotals
      (typedPositiveAwayUpper t m z) → Bool
  monotone_screened : ∀ z, Monotone fun cap ↦
    walkLift (tilingPreStoppingFiberEvent (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) cap (typedBoundaryTail z).1
      (typedStoppedScreenedPredicate t m k stage z cap (accepts z cap)))
  transition_covered : ∀ z,
    typedFavoriteTilingStagePiece t m k stage z ∩ next ⊆ ⋃ cap,
      walkLift (tilingPreStoppingFiberEvent (typedStoppingTime m k z cap)
        t (0, 0) (typedRetained z) cap (typedBoundaryTail z).1
        (typedStoppedScreenedPredicate t m k stage z cap (accepts z cap)))
  product_bound : ∀ z cap,
    FiniteDominoProductLaw.screenMass
      (tilingAwayPointMass (cap := cap) t (0, 0) (typedRetained z)
        (typedDistinguished z)) (typedPositiveAwayUpper t m z)
      (fun ell ↦ accepts z cap ell = true) ≤ cost.toReal

noncomputable def firstCreationScreeningData
    (t : DominoTiling) (m : ℕ) (hm : 1 < m)
    (next : Set WalkPath) (cost : ℝ≥0∞)
    (screen : TypedFiniteAwayScreenData t m 1
      (firstCreationStage m) next cost) :
    TypedStoppedStageScreeningData t m 1
      (firstCreationStage m) next cost where
  accepts := screen.accepts
  invariant := typedFirstCreationStoppedInvariant t m hm
  monotone_screened := screen.monotone_screened
  transition_covered := screen.transition_covered
  product_bound := screen.product_bound

noncomputable def firstTransitionScreeningData
    (t : DominoTiling) (m : ℕ) (hm : 1 < m)
    (a : (GapScale × GapScale) × GapScale)
    (next : Set WalkPath) (cost : ℝ≥0∞)
    (screen : TypedFiniteAwayScreenData t m 2
      (firstTransitionEvent t m a) next cost) :
    TypedStoppedStageScreeningData t m 2
      (firstTransitionEvent t m a) next cost where
  accepts := screen.accepts
  invariant := typedFirstTransitionStoppedInvariant t m hm a
  monotone_screened := screen.monotone_screened
  transition_covered := screen.transition_covered
  product_bound := screen.product_bound

noncomputable def secondTransitionScreeningData
    (t : DominoTiling) (m : ℕ) (hm : 1 < m)
    (a : (GapScale × GapScale) × GapScale)
    (next : Set WalkPath) (cost : ℝ≥0∞)
    (screen : TypedFiniteAwayScreenData t m 3
      (secondTransitionEvent t m a) next cost) :
    TypedStoppedStageScreeningData t m 3
      (secondTransitionEvent t m a) next cost where
  accepts := screen.accepts
  invariant := typedSecondTransitionStoppedInvariant t m hm a
  monotone_screened := screen.monotone_screened
  transition_covered := screen.transition_covered
  product_bound := screen.product_bound

/-- Literal rank-one factored stopped-coordinate law.  No spatial or
probabilistic equality remains as an input. -/
noncomputable def firstCreationFactoredStoppedCoordinateData
    (t : DominoTiling) (m : ℕ) (hm : 1 < m)
    (next : Set WalkPath) (cost : ℝ≥0∞)
    (screen : TypedFiniteAwayScreenData t m 1
      (firstCreationStage m) next cost) :
    TilingFactoredStoppedCoordinateData
      (typedFavoriteTilingStagePiece t m 1 (firstCreationStage m))
      next cost :=
  typedFactoredStoppedCoordinateData t m 1 (by omega) (by omega)
    (firstCreationStage m) next cost
    (firstCreationScreeningData t m hm next cost screen)

/-- Literal rank-two factored stopped-coordinate law. -/
noncomputable def firstTransitionFactoredStoppedCoordinateData
    (t : DominoTiling) (m : ℕ) (hm : 1 < m)
    (a : (GapScale × GapScale) × GapScale)
    (next : Set WalkPath) (cost : ℝ≥0∞)
    (screen : TypedFiniteAwayScreenData t m 2
      (firstTransitionEvent t m a) next cost) :
    TilingFactoredStoppedCoordinateData
      (typedFavoriteTilingStagePiece t m 2 (firstTransitionEvent t m a))
      next cost :=
  typedFactoredStoppedCoordinateData t m 2 (by omega) (by omega)
    (firstTransitionEvent t m a) next cost
    (firstTransitionScreeningData t m hm a next cost screen)

/-- Literal rank-three factored stopped-coordinate law. -/
noncomputable def secondTransitionFactoredStoppedCoordinateData
    (t : DominoTiling) (m : ℕ) (hm : 1 < m)
    (a : (GapScale × GapScale) × GapScale)
    (next : Set WalkPath) (cost : ℝ≥0∞)
    (screen : TypedFiniteAwayScreenData t m 3
      (secondTransitionEvent t m a) next cost) :
    TilingFactoredStoppedCoordinateData
      (typedFavoriteTilingStagePiece t m 3 (secondTransitionEvent t m a))
      next cost :=
  typedFactoredStoppedCoordinateData t m 3 (by omega) (by omega)
    (secondTransitionEvent t m a) next cost
    (secondTransitionScreeningData t m hm a next cost screen)

/-- The three literal typed factored laws at one level and one tiling. -/
structure ThreeTypedTransitionFactoredCoordinateData
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) where
  first : TilingFactoredStoppedCoordinateData
    (typedFavoriteTilingStagePiece t m 1 (firstCreationStage m))
    (firstTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m)
  second : TilingFactoredStoppedCoordinateData
    (typedFavoriteTilingStagePiece t m 2 (firstTransitionEvent t m a))
    (secondTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m)
  third : TilingFactoredStoppedCoordinateData
    (typedFavoriteTilingStagePiece t m 3 (secondTransitionEvent t m a))
    (screenedThirdTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m)

/-- All spatial fields of the three laws are filled automatically from the
finite away screens. -/
noncomputable def threeTypedTransitionFactoredCoordinateDataOfScreens
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ) (hm : 1 < m)
    (a : (GapScale × GapScale) × GapScale)
    (first : TypedFiniteAwayScreenData t m 1 (firstCreationStage m)
      (firstTransitionEvent t m a ∩ validStepWalk)
      (UpperCanonical.hlozTransitionCost K m))
    (second : TypedFiniteAwayScreenData t m 2 (firstTransitionEvent t m a)
      (secondTransitionEvent t m a ∩ validStepWalk)
      (UpperCanonical.hlozTransitionCost K m))
    (third : TypedFiniteAwayScreenData t m 3 (secondTransitionEvent t m a)
      (screenedThirdTransitionEvent t m a ∩ validStepWalk)
      (UpperCanonical.hlozTransitionCost K m)) :
    ThreeTypedTransitionFactoredCoordinateData K t m a where
  first := firstCreationFactoredStoppedCoordinateData t m hm
    (firstTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m) first
  second := firstTransitionFactoredStoppedCoordinateData t m hm a
    (secondTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m) second
  third := secondTransitionFactoredStoppedCoordinateData t m hm a
    (screenedThirdTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m) third

structure ThreeTypedTransitionStoppedCoordinateSpecs
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) where
  first : TilingStoppedCoordinateProductSpec
    (typedFavoriteTilingStagePiece t m 1 (firstCreationStage m))
    (firstTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m)
  second : TilingStoppedCoordinateProductSpec
    (typedFavoriteTilingStagePiece t m 2 (firstTransitionEvent t m a))
    (secondTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m)
  third : TilingStoppedCoordinateProductSpec
    (typedFavoriteTilingStagePiece t m 3 (secondTransitionEvent t m a))
    (screenedThirdTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m)

noncomputable def threeTypedTransitionStoppedSpecsOfFactoredData
    {K : ℝ≥0} {t : DominoTiling} {m : ℕ}
    {a : (GapScale × GapScale) × GapScale}
    (data : ThreeTypedTransitionFactoredCoordinateData K t m a) :
    ThreeTypedTransitionStoppedCoordinateSpecs K t m a where
  first := tilingStoppedCoordinateProductSpecOfFactoredData data.first
  second := tilingStoppedCoordinateProductSpecOfFactoredData data.second
  third := tilingStoppedCoordinateProductSpecOfFactoredData data.third

theorem firstTransition_measure_le_of_typedFactoredData
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (data : ThreeTypedTransitionFactoredCoordinateData K t m a) :
    simpleRandomWalk (firstTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m := by
  have hstageMeasurable : MeasurableSet (firstCreationStage m) := by
    rw [← thresholdReachStage_one_eq_firstCreationStage]
    exact measurableSet_thresholdReachStage m 1
  have hstage : firstCreationStage m ⊆ thresholdReachStage m 1 := by
    rw [thresholdReachStage_one_eq_firstCreationStage]
  have hnext : firstTransitionEvent t m a ⊆ firstCreationStage m := by
    rw [← thresholdReachStage_one_eq_firstCreationStage]
    exact firstTransitionEvent_subset_thresholdReachStage_one t m a
  have hbound := transition_measure_le_of_typedFavoriteTilingStoppedCoordinateSpec
    t m 1 (firstCreationStage m) (firstTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    hstageMeasurable
    (measurableSet_firstTransitionEvent t m a)
    hstage hnext
    (hlozTransitionCost_ne_top K m)
    (threeTypedTransitionStoppedSpecsOfFactoredData data).first
  have hstageMass : simpleRandomWalk (firstCreationStage m) ≤ 1 := by
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ (firstCreationStage m))
  exact hbound.trans (by
    simpa only [mul_one, one_mul, mul_comm] using
      (mul_le_mul_left hstageMass (UpperCanonical.hlozTransitionCost K m)))

theorem secondTransition_measure_le_of_typedFactoredData
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (data : ThreeTypedTransitionFactoredCoordinateData K t m a) :
    simpleRandomWalk (secondTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (firstTransitionEvent t m a) :=
  transition_measure_le_of_typedFavoriteTilingStoppedCoordinateSpec
    t m 2 (firstTransitionEvent t m a) (secondTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    (measurableSet_firstTransitionEvent t m a)
    (measurableSet_secondTransitionEvent t m a)
    (firstTransitionEvent_subset_thresholdReachStage_two t m a)
    (secondTransitionEvent_subset_first t m a)
    (hlozTransitionCost_ne_top K m)
    (threeTypedTransitionStoppedSpecsOfFactoredData data).second

theorem screenedThirdTransition_measure_le_of_typedFactoredData
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (data : ThreeTypedTransitionFactoredCoordinateData K t m a) :
    simpleRandomWalk (screenedThirdTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (secondTransitionEvent t m a) := by
  apply transition_measure_le_of_typedFavoriteTilingStoppedCoordinateSpec
    t m 3 (secondTransitionEvent t m a) (screenedThirdTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    (measurableSet_secondTransitionEvent t m a)
    (measurableSet_screenedThirdTransitionEvent t m a)
    (secondTransitionEvent_subset_thresholdReachStage_three t m a)
    _ (hlozTransitionCost_ne_top K m)
    (threeTypedTransitionStoppedSpecsOfFactoredData data).third
  exact fun _ hs ↦ thirdTransitionEvent_subset_second t m a hs.1

end

end Erdos1165.TilingTypedTransitionFactorization
