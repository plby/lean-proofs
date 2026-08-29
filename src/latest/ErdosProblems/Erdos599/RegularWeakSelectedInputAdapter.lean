/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularLiftCleanTargetSlice
import ErdosProblems.Erdos599.RegularSplitCanonicalHistoryBase
import ErdosProblems.Erdos599.RegularRoofedAnnularSuccessor
import ErdosProblems.Erdos599.RegularDirectPersistentCanonicalSuccessor

/-!
# Installing a weak diagonal split on the active pending boundary

The diagonal source-9.15 table is built on the whole old ladder frontier.
Its request may contain extra coordinates which are not terminals of the
current pending row.  This module intersects the table's selected target
coordinates with that active terminal frontier, restricts both tracks, and
packages the result as the exact selected-coordinate input of the canonical
recursion.

Only the genuinely mathematical local inputs remain explicit: the weak
annular comparison, its clean target split, target links on the table
complement, the interval/maverick bounds, and closure of the restricted
installed carrier.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakSelectedInputAdapter

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- Closure of the restricted installed family from exactly the two causal
registrations.  Target-track vertices and clean mavericks are registered
directly.  Every other clean component is a fragment of the later stage
warp, hence embeds in the limit warp; its initial vertex lies on the active
boundary `D`, which supplies the required contact with the closed set. -/
theorem vertexSet_restrictLeftInter_union_subset
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} (hL : L.IsLegal)
    {Z left right U D : Set V}
    (hlimitClosed : SliceSplice.IsLimitWarpClosed G L Z)
    (S : RegularCompletedPendingSplice.CleanTargetSlice G left right U)
    (hDleft : D ⊆ left) {beta : Ladder.Stage kappa}
    (hDclosed : D ⊆ Z)
    (htargetClosed : G.vertexSet S.target ⊆ Z)
    (hmavericksClosed : G.vertexSet
      (ControlledSlices.sliceMavericks G (L.warpAt beta) S.clean) ⊆ Z) :
    G.vertexSet
        ((RegularLiftCleanTargetSlice.restrictLeftInter S hDleft).target ∪
          (RegularLiftCleanTargetSlice.restrictLeftInter S hDleft).clean) ⊆
      Z := by
  rintro x ⟨p, hpTarget | hpClean, hxp⟩
  · exact htargetClosed ⟨p,
      RegularLiftCleanTargetSlice.restrictLeftInter.target_subset
        S hDleft hpTarget, hxp⟩
  · by_cases hpOrdinary :
        ControlledSlices.IsLadderFragment G (L.warpAt beta) p
    · obtain ⟨q, hqStage, hpq⟩ := hpOrdinary
      obtain ⟨r, hrLimit, hqr⟩ :=
        ControlledSlices.stagesEmbedInLimit_of_legal G L hL beta q hqStage
      have hpInitialD : p.initial ∈ D := hpClean.2.1
      have hrMeets : (r.support ∩ Z).Nonempty := by
        refine ⟨p.initial, ?_, hDclosed hpInitialD⟩
        exact hqr.1 (hpq.1 p.initial_mem_support)
      exact (hlimitClosed r hrLimit hrMeets) (hqr.1 (hpq.1 hxp))
    · exact hmavericksClosed ⟨p,
        ⟨RegularLiftCleanTargetSlice.restrictLeftInter.clean_subset
          S hDleft hpClean, hpOrdinary⟩, hxp⟩

/-- A full-frontier weak annular split yields the exact selected-coordinate
successor input after restriction to the current pending terminal frontier.
The returned second component is the whole-row roof invariant required by
the recursive provider.

The table request `Utable` is allowed to strictly contain the currently
required coordinates.  The installed target index is therefore
`selected ∩ terminalFrontier (pendingPart base)`. -/
theorem exists_directSelectedSplitInput_of_annular
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (B : RegularSplitCanonicalHistoryBase.HistoryBase
      G L Sigma Z A request i previous)
    (hL : L.IsLegal)
    {beta : Ladder.Stage kappa} (hbeta : beta ∈ Sigma)
    (hab : B.baseStage < beta)
    {Utable selected : Set V} {comparison : Set G.DPath}
    (hrequired : RegularGlobalAdmissibleProvider.requiredPendingTerminals
      G L Sigma Z A request i previous B.base ⊆ Utable)
    (S : RegularCompletedPendingSplice.CleanTargetSlice G
      (L.frontier B.baseStage) (L.frontier beta) selected)
    (hcomparison : SliceSplice.IsAnnularSlice G L comparison
      B.baseStage beta (Utable \ selected))
    (hinstalled : S.target ∪ S.clean ⊆ comparison)
    (hcleanLinks : LinksToTarget G S.clean (Utable \ selected))
    (hintervals : SliceCandidate.HasStageIntervalSegments
      G L S.clean B.baseStage beta)
    (hmavericks : #(ControlledSlices.sliceMavericks G
      (L.warpAt beta) S.clean) < kappa)
    (hrestrictedClosed : G.vertexSet
      ((RegularLiftCleanTargetSlice.restrictLeftInter S
        B.pending_tight.1.terminalFrontier_subset).target ∪
       (RegularLiftCleanTargetSlice.restrictLeftInter S
        B.pending_tight.1.terminalFrontier_subset).clean) ⊆ Z) :
    ∃ I : RegularDirectPersistentCanonicalSuccessor.DirectSelectedSplitInput
        G L Sigma Z A request i previous,
      G.vertexSet
          (RegularCompletedPendingSplice.freezeCompletedStar G I.base
            (I.slice.target ∪ I.slice.clean) I.compatible) ⊆
        G.roof (L.frontier I.stageIndex) := by
  let D := G.terminalFrontier (pendingPart G B.base)
  have hDleft : D ⊆ L.frontier B.baseStage :=
    B.pending_tight.1.terminalFrontier_subset
  let slice := RegularLiftCleanTargetSlice.restrictLeftInter S hDleft
  have hsliceInstalled : slice.target ∪ slice.clean ⊆ comparison :=
    (RegularLiftCleanTargetSlice.restrictLeftInter.union_subset
      S hDleft).trans hinstalled
  have hfullCompat : G.StarCompatible (pendingPart G B.base) comparison :=
    SliceSpliceConstructor.starCompatible_of_annular
      (hL.frontiersEssential B.baseStage) B.pending_below_roof
        B.pending_tight.2 hcomparison
  let hcompat : G.StarCompatible (pendingPart G B.base)
      (slice.target ∪ slice.clean) :=
    fun p hp q hq x hxp hxq ↦
      hfullCompat p hp q (hsliceInstalled hq) x hxp hxq
  have hstarFinite : G.HasFiniteCharacter (G.star hcompat) :=
    SliceSpliceSource.hasFiniteCharacter_star
      B.pending_tight.1.finiteCharacter slice.finiteCharacter hcompat
  have hrequiredD : RegularGlobalAdmissibleProvider.requiredPendingTerminals
      G L Sigma Z A request i previous B.base ⊆ D :=
    RegularGlobalAdmissibleProvider.requiredPendingTerminals_subset_terminalFrontier
  have hcleanLinksRequired : LinksToTarget G slice.clean
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous B.base \ (selected ∩ D)) := by
    let M := RegularGlobalAdmissibleProvider.requiredPendingTerminals
      G L Sigma Z A request i previous B.base \ (selected ∩ D)
    have hMtable : M ⊆ Utable \ selected := by
      rintro x ⟨hxRequired, hxNotSelectedD⟩
      have hxD : x ∈ D := hrequiredD hxRequired
      exact ⟨hrequired hxRequired,
        fun hxSelected ↦ hxNotSelectedD ⟨hxSelected, hxD⟩⟩
    have hMD : M ⊆ D \ selected := by
      rintro x ⟨hxRequired, hxNotSelectedD⟩
      have hxD : x ∈ D := hrequiredD hxRequired
      exact ⟨hxD,
        fun hxSelected ↦ hxNotSelectedD ⟨hxSelected, hxD⟩⟩
    exact RegularLiftCleanTargetSlice.restrictLeftInter.clean_links
      S hDleft
        (ControlledSlices.linksToTarget_mono G S.clean hMtable hcleanLinks)
        hMD
  have hOldBoundary : MeetsOnlyAtTerminal G (pendingPart G B.base)
      (L.frontier beta) :=
    meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
      (hL.frontiersEssential B.baseStage) B.pending_below_roof
        B.pending_tight.2 (hL.strictFrontierChronology hab)
  have hmavericksClosed : G.vertexSet
      (ControlledSlices.sliceMavericks G (L.warpAt beta) slice.clean) ⊆
        Z := by
    rintro x ⟨p, hp, hxp⟩
    exact hrestrictedClosed ⟨p, Or.inr hp.1, hxp⟩
  have hverticesClosed : G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G B.base
        (slice.target ∪ slice.clean) hcompat) ⊆ Z := by
    rintro x ⟨p, hpResult, hxp⟩
    rcases hpResult with hpCompleted | hpStar
    · exact B.base_vertices_closed ⟨p, hpCompleted.1, hxp⟩
    · rcases SliceSpliceSource.vertexSet_star_subset_union hcompat
          ⟨p, hpStar, hxp⟩ with hxPending | hxInstalled
      · obtain ⟨q, hqPending, hxq⟩ := hxPending
        exact B.base_vertices_closed ⟨q, hqPending.1, hxq⟩
      · exact hrestrictedClosed hxInstalled
  let I :
      RegularDirectPersistentCanonicalSuccessor.DirectSelectedSplitInput
        G L Sigma Z A request i previous :=
    { baseStage := B.baseStage
      base := B.base
      base_warp := B.base_warp
      base_finite := B.base_finite
      base_initial := B.base_initial
      base_extends := B.base_extends
      base_freezes := B.base_freezes
      stageIndex := beta
      stageIndex_mem := hbeta
      index_strict := fun j hji ↦
        lt_of_le_of_lt (B.index_le_base j hji) hab
      selected := selected ∩ D
      required_subset_left := hrequiredD
      slice := slice
      compatible := hcompat
      cleanStep :=
        (RegularRoofedAnnularSuccessor.cleanTargetStep_and_result_below_roof_of_annular
          hL hab B.base_warp B.base_below_roof hcomparison slice
            hsliceInstalled hcompat).1
      installed_star_finite := hstarFinite
      vertices_closed := hverticesClosed
      pending_below_roof := by
        rintro x ⟨p, hp, hxp⟩
        exact
          (RegularRoofedAnnularSuccessor.cleanTargetStep_and_result_below_roof_of_annular
            hL hab B.base_warp B.base_below_roof hcomparison slice
              hsliceInstalled hcompat).2 ⟨p, hp.1, hxp⟩
      old_pending_boundary := hOldBoundary
      old_pending_status := B.old_pending_status
      clean_links_unselected := hcleanLinksRequired
      cleanIntervals :=
        RegularLiftCleanTargetSlice.restrictLeftInter.cleanIntervals
          S hDleft hintervals
      cleanMavericks_small :=
        RegularLiftCleanTargetSlice.restrictLeftInter.cleanMavericks_small
          S hDleft hmavericks
      cleanMavericks_closed := hmavericksClosed }
  refine ⟨I, ?_⟩
  exact
    RegularRoofedAnnularSuccessor.freezeCompletedStar_vertexSet_subset_roof_of_annular
      hL hab B.base_below_roof hcomparison hsliceInstalled hcompat

end RegularWeakSelectedInputAdapter
end CardinalInduction
end Erdos599
