/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceDistinguishedEventProp49Family

/-!
# Restricting an existing source refinement by a distinguished event

This is the reusable form of the distinguished-carrier argument.  It applies
to any conditional refinement on a canonical source fibre, including the
checker exposed-origin refinement.
-/

open Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceRefinementEventRestriction

open HLOZPrefixedAllCreationDistinguishedRestriction
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZSourceDistinguishedEventProp49Family
open LazyDecomposition PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber TilingDistinguishedTraceInvariant
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def eventRestrictedBaseFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (refinement : OrientedAllCreationConditionalRefinementData
      (SourceFiber eta) piece next cost)
    (event : Set WalkPath) (cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (restrictPredicate (SourceFiber eta) (distinguishedEventSafe eta event)
      refinement.basePredicate cap))

def eventRestrictedScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (refinement : OrientedAllCreationConditionalRefinementData
      (SourceFiber eta) piece next cost)
    (event : Set WalkPath) (cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (restrictPredicate (SourceFiber eta) (distinguishedEventSafe eta event)
      refinement.screenedPredicate cap))

private def ordinaryBaseFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (refinement : OrientedAllCreationConditionalRefinementData
      (SourceFiber eta) piece next cost)
    (cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (refinement.basePredicate cap))

private def ordinaryScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (refinement : OrientedAllCreationConditionalRefinementData
      (SourceFiber eta) piece next cost)
    (cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (refinement.screenedPredicate cap))

theorem eventRestrictedBaseFiber_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (refinement : OrientedAllCreationConditionalRefinementData
      (SourceFiber eta) piece next cost)
    (event : Set WalkPath)
    (hinvariant : SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hk : 0 < k) (cap : ℕ) :
    eventRestrictedBaseFiber eta refinement event cap =
      ordinaryBaseFiber eta refinement cap ∩ event := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hvalid, hevent⟩
    rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
    have hpred := refinement.base_subset_atom cap q.1 q.2.1.1
    have hcanonicalEvent := canonical_mem_event_of_distinguishedEventSafe
      hinvariant q.1 hpred q.2.2 q.2.1.2
    have hactualEvent : s ∈ event := by
      have heq := event_iff_canonical_of_mem_stopped hk hprefix q.1 q.2.2
        (stepsOfWalk s) hq
      change trajectory (stepsOfWalk s) = s at hvalid
      rw [hvalid] at heq
      exact heq.mpr hcanonicalEvent
    exact ⟨⟨hvalid, Set.mem_iUnion.mpr
      ⟨⟨q.1, q.2.1.1, q.2.2⟩, hq⟩⟩, hactualEvent⟩
  · rintro ⟨hold, heventActual⟩
    rcases hold with ⟨hvalid, hfiber⟩
    rcases Set.mem_iUnion.mp hfiber with ⟨q, hq⟩
    have hpred := refinement.base_subset_atom cap q.1 q.2.1
    have hcanonicalEvent : trajectory (extendPrefix (directionVectorOfList
        (prefixedTilingInsertionPrefixList ((SourceFiber eta).initial cap) t
          ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
          (fun j ↦ (q.1 j : ℕ)) ((SourceFiber eta).tail cap)))) ∈ event := by
      have heq := event_iff_canonical_of_mem_stopped hk hprefix q.1 q.2.2
        (stepsOfWalk s) hq
      change trajectory (stepsOfWalk s) = s at hvalid
      rw [hvalid] at heq
      exact heq.mp heventActual
    have hsafe := distinguishedEventSafe_of_canonical_mem_event q.1 hpred
      q.2.2 hcanonicalEvent
    exact ⟨hvalid, Set.mem_iUnion.mpr
      ⟨⟨q.1, ⟨q.2.1, hsafe⟩, q.2.2⟩, hq⟩⟩

theorem eventRestrictedScreenedFiber_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (refinement : OrientedAllCreationConditionalRefinementData
      (SourceFiber eta) piece next cost)
    (event : Set WalkPath)
    (hinvariant : SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hk : 0 < k) (cap : ℕ) :
    eventRestrictedScreenedFiber eta refinement event cap =
      ordinaryScreenedFiber eta refinement cap ∩ event := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hvalid, hevent⟩
    rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
    have hbase := refinement.screened_subset_basePredicate cap q.1 q.2.1.1
    have hpred := refinement.base_subset_atom cap q.1 hbase
    have hcanonicalEvent := canonical_mem_event_of_distinguishedEventSafe
      hinvariant q.1 hpred q.2.2 q.2.1.2
    have hactualEvent : s ∈ event := by
      have heq := event_iff_canonical_of_mem_stopped hk hprefix q.1 q.2.2
        (stepsOfWalk s) hq
      change trajectory (stepsOfWalk s) = s at hvalid
      rw [hvalid] at heq
      exact heq.mpr hcanonicalEvent
    exact ⟨⟨hvalid, Set.mem_iUnion.mpr
      ⟨⟨q.1, q.2.1.1, q.2.2⟩, hq⟩⟩, hactualEvent⟩
  · rintro ⟨hold, heventActual⟩
    rcases hold with ⟨hvalid, hfiber⟩
    rcases Set.mem_iUnion.mp hfiber with ⟨q, hq⟩
    have hbase := refinement.screened_subset_basePredicate cap q.1 q.2.1
    have hpred := refinement.base_subset_atom cap q.1 hbase
    have hcanonicalEvent : trajectory (extendPrefix (directionVectorOfList
        (prefixedTilingInsertionPrefixList ((SourceFiber eta).initial cap) t
          ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
          (fun j ↦ (q.1 j : ℕ)) ((SourceFiber eta).tail cap)))) ∈ event := by
      have heq := event_iff_canonical_of_mem_stopped hk hprefix q.1 q.2.2
        (stepsOfWalk s) hq
      change trajectory (stepsOfWalk s) = s at hvalid
      rw [hvalid] at heq
      exact heq.mp heventActual
    have hsafe := distinguishedEventSafe_of_canonical_mem_event q.1 hpred
      q.2.2 hcanonicalEvent
    exact ⟨hvalid, Set.mem_iUnion.mpr
      ⟨⟨q.1, ⟨q.2.1, hsafe⟩, q.2.2⟩, hq⟩⟩

/-- Restrict a canonical source refinement to an invariant event. -/
noncomputable def restrictSourceRefinementToEvent
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (refinement : OrientedAllCreationConditionalRefinementData
      (SourceFiber eta) piece next cost)
    (event : Set WalkPath)
    (hinvariant : SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hk : 0 < k) :
    OrientedAllCreationConditionalRefinementData
      (withSelected (SourceFiber eta) (fun cap d ↦
        (SourceFiber eta).selected cap d ∧
          distinguishedEventSafe eta event cap d))
      (piece ∩ event) (next ∩ event) cost := by
  apply restrictRefinement (SourceFiber eta) refinement
    (distinguishedEventSafe eta event)
  · intro cap
    change eventRestrictedBaseFiber eta refinement event cap ⊆ piece ∩ event
    rw [eventRestrictedBaseFiber_eq eta refinement event hinvariant hprefix hk]
    exact inter_subset_inter_left event (refinement.base_subset_piece cap)
  · intro cap cap' hcap s hs
    change s ∈ eventRestrictedScreenedFiber eta refinement event cap at hs
    change s ∈ eventRestrictedScreenedFiber eta refinement event cap'
    rw [eventRestrictedScreenedFiber_eq eta refinement event hinvariant hprefix
      hk cap] at hs
    rw [eventRestrictedScreenedFiber_eq eta refinement event hinvariant hprefix
      hk cap']
    exact ⟨refinement.monotone_screened hcap hs.1, hs.2⟩
  · intro s hs
    have hold : s ∈ piece ∩ next := ⟨hs.1.1, hs.2.1⟩
    rcases Set.mem_iUnion.mp (refinement.transition_covered hold) with ⟨cap, hcap⟩
    apply Set.mem_iUnion.mpr
    refine ⟨cap, ?_⟩
    change s ∈ eventRestrictedScreenedFiber eta refinement event cap
    rw [eventRestrictedScreenedFiber_eq eta refinement event hinvariant hprefix
      hk cap]
    exact ⟨hcap, hs.1.2⟩

end

end Erdos1165.HLOZSourceRefinementEventRestriction
