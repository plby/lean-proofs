/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularLiftCleanTargetSlice
import ErdosProblems.Erdos599.RegularSplitCanonicalProvider
import ErdosProblems.Erdos599.RegularWeakSplitCandidate
import ErdosProblems.Erdos599.RegularPendingRoofCompatibility
import ErdosProblems.Erdos599.RegularRoofedAnnularSuccessor

/-!
# From one weak causal coordinate to a canonical selected successor

The diagonal request stored at a weak split coordinate may contain more
vertices than are currently exposed by the pending row.  We therefore
restrict both tracks of the chosen clean-target slice to the actual pending
terminal frontier.  The selected target set becomes the intersection with
that frontier, while every required but unselected coordinate remains on the
clean target-linked track.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakSelectedSource915Adapter

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- A chosen weak causal coordinate, together with its registered carrier,
supplies exactly the selected-coordinate successor output. -/
theorem selectedRoofedSource915Output_of_chosenWeakCoordinate
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized)
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (B : RegularSplitCanonicalHistoryBase.HistoryBase
      G L Sigma Z A request i previous)
    (tableRequest : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (beta gamma : Ladder.Stage kappa)
    (hbeta : beta ∈ Sigma) (hab : B.baseStage < beta)
    (hcandidate : RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate
      G L tableRequest B.baseStage beta gamma
        (RegularWeakSplitCandidate.chosenWeakSplitCandidate
          G L tableRequest B.baseStage beta gamma))
    (hrequired : RegularGlobalAdmissibleProvider.requiredPendingTerminals
      G L Sigma Z A request i previous B.base ⊆
        tableRequest B.baseStage gamma)
    (hregistered :
      RegularWeakSplitCandidate.registeredVerticesAt
        G L tableRequest B.baseStage beta gamma ⊆ Z)
    (hclosed : SliceSplice.IsLimitWarpClosed G L Z) :
    Nonempty (RegularSplitCanonicalProvider.SelectedRoofedSource915Output
      G L Sigma Z A request i previous B) := by
  let P := RegularWeakSplitCandidate.chosenWeakSplitCandidate
    G L tableRequest B.baseStage beta gamma
  let U := tableRequest B.baseStage gamma
  let persistent :=
    RegularWeakSplitCandidate.stagePersistent G (L.frontier beta) U
  let D := G.terminalFrontier (pendingPart G B.base)
  change ∃ E : Set V,
    persistent ⊆ E ∧
      ∃ S : RegularCompletedPendingSplice.CleanTargetSlice G
        (L.frontier B.baseStage) (L.frontier beta) E,
      S.target = P.target ∧ S.clean = P.clean ∧
        SliceSplice.IsAnnularSlice G L P.comparison
          B.baseStage beta (U \ E) ∧
        P.clean ⊆ P.comparison ∧
        G.vertexSet P.target ⊆ G.roof (L.frontier beta) ∧
        #P.target < kappa ∧ LinksToTarget G P.clean (U \ E) ∧
        SliceCandidate.HasStageIntervalSegments G L P.clean
          B.baseStage beta ∧
        #(ControlledSlices.sliceMavericks G (L.warpAt beta) P.clean) < kappa
      at hcandidate
  obtain ⟨E, _hpersistent, S₀, htarget, hclean, hannular,
    hcleanInstalled, htargetRoof, _htargetSmall, hcleanLinks, hintervals,
      hmavericksSmall⟩ := hcandidate
  have hDleft : D ⊆ L.frontier B.baseStage := by
    simpa only [D] using B.pending_tight.1.terminalFrontier_subset
  let S := RegularLiftCleanTargetSlice.restrictLeftInter S₀ hDleft
  have hrequiredD :
      RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous B.base ⊆ D :=
    by
      simpa only [D] using
        (RegularGlobalAdmissibleProvider.requiredPendingTerminals_subset_terminalFrontier
          (G := G) (L := L) (Sigma := Sigma) (Z := Z) (A := A)
          (request := request) (i := i) (previous := previous)
          (base := B.base))
  have hDclosed : D ⊆ Z := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hx
    exact B.base_vertices_closed
      ⟨p, hp.1, G.terminal_mem_support hpx⟩
  have hOldBoundary : MeetsOnlyAtTerminal G (pendingPart G B.base)
      (L.frontier beta) :=
    meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
      (hL.frontiersEssential B.baseStage) B.pending_below_roof
        B.pending_tight.2 (hL.strictFrontierChronology hab)
  have htargetAvoid : G.vertexSet S₀.target ⊆
      (G.strictRoof (L.frontier B.baseStage))ᶜ :=
    RegularPendingRoofCompatibility.target_vertexSet_subset_compl_strictRoof
      G hNorm (hL.frontiersEssential B.baseStage) S₀
  have hcleanAvoid : G.vertexSet S₀.clean ⊆
      (G.strictRoof (L.frontier B.baseStage))ᶜ := by
    rintro x ⟨p, hp, hxp⟩
    exact (hannular.2 ⟨p, hcleanInstalled (hclean ▸ hp), hxp⟩).1
  have hfullUsedAvoid : G.vertexSet (S₀.target ∪ S₀.clean) ⊆
      (G.strictRoof (L.frontier B.baseStage))ᶜ := by
    rintro x ⟨p, hpTarget | hpClean, hxp⟩
    · exact htargetAvoid ⟨p, hpTarget, hxp⟩
    · exact hcleanAvoid ⟨p, hpClean, hxp⟩
  have hfullCompat : G.StarCompatible (pendingPart G B.base)
      (S₀.target ∪ S₀.clean) :=
    RegularPendingRoofCompatibility.starCompatible_cleanTargetSlice_of_pendingRoof
      G (hL.frontiersEssential B.baseStage) B.pending_below_roof
        B.pending_tight.2 S₀ hfullUsedAvoid
  let hcompat : G.StarCompatible (pendingPart G B.base)
      (S.target ∪ S.clean) := fun p hp q hq ↦
    hfullCompat p hp q
      (RegularLiftCleanTargetSlice.restrictLeftInter.union_subset
        S₀ hDleft hq)
  have hpendingFinite : G.HasFiniteCharacter (pendingPart G B.base) :=
    fun {_} hp ↦ B.base_finite hp.1
  have hstarFinite : G.HasFiniteCharacter (G.star hcompat) :=
    SliceSpliceSource.hasFiniteCharacter_star hpendingFinite
      S.finiteCharacter hcompat
  have hinstalledClosed : G.vertexSet (S.target ∪ S.clean) ⊆ Z := by
    rintro x ⟨p, hpTarget | hpClean, hxp⟩
    · apply hregistered
      apply RegularWeakSplitCandidate.chosen_target_vertices_subset_registered
        G L tableRequest B.baseStage beta gamma
      refine ⟨p, ?_, hxp⟩
      have hp₀ :=
        RegularLiftCleanTargetSlice.restrictLeftInter.target_subset
          S₀ hDleft hpTarget
      exact htarget ▸ hp₀
    · have hp₀ :=
        RegularLiftCleanTargetSlice.restrictLeftInter.clean_subset
          S₀ hDleft hpClean
      have hpP : p ∈ P.clean := hclean ▸ hp₀
      apply RegularWeakSplitCandidate.chosen_clean_support_subset_of_initial_mem
        hL hclosed tableRequest B.baseStage beta gamma hregistered hpP
      · apply hDclosed
        rw [RegularLiftCleanTargetSlice.restrictLeftInter.clean] at hpClean
        exact hpClean.2.1
      · exact hxp
  have hstarClosed : G.vertexSet (G.star hcompat) ⊆ Z := by
    intro x hx
    rcases SliceSpliceSource.vertexSet_star_subset_union hcompat hx with
      hxOld | hxNew
    · obtain ⟨p, hp, hxp⟩ := hxOld
      exact B.base_vertices_closed ⟨p, hp.1, hxp⟩
    · exact hinstalledClosed hxNew
  have hresultClosed : G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G B.base
        (S.target ∪ S.clean) hcompat) ⊆ Z := by
    rintro x ⟨p, hpCompleted | hpStar, hxp⟩
    · exact B.base_vertices_closed ⟨p, hpCompleted.1, hxp⟩
    · exact hstarClosed ⟨p, hpStar, hxp⟩
  have hcompletedRoof : G.vertexSet (completedPart G B.base) ⊆
      G.roof (L.frontier B.baseStage) := by
    rintro x ⟨p, hp, hxp⟩
    exact B.base_below_roof ⟨p, hp.1, hxp⟩
  have hcleanAvoid' : G.vertexSet S.clean ⊆
      (G.strictRoof (L.frontier B.baseStage))ᶜ := by
    rintro x ⟨p, hp, hxp⟩
    apply hcleanAvoid
    exact ⟨p,
      RegularLiftCleanTargetSlice.restrictLeftInter.clean_subset
        S₀ hDleft hp,
      hxp⟩
  have hcleanOwner : G.vertexSet S.clean ∩
      L.frontier B.baseStage ⊆
      G.vertexSet (pendingPart G B.base) := by
    apply
      RegularRoofedAnnularSuccessor.frontierOwner_of_subfamily_of_sourceExactWarp
        G hannular.1.1.isWarp hannular.1.1.initialSet_eq
    · intro p hp
      exact hcleanInstalled (hclean ▸
        RegularLiftCleanTargetSlice.restrictLeftInter.clean_subset
          S₀ hDleft hp)
    · rw [S.clean_initial]
      exact Set.sdiff_subset
  have hcleanCross : Disjoint
      (G.vertexSet (completedPart G B.base)) (G.vertexSet S.clean) :=
    RegularRoofSuffixCompatibility.disjoint_subfamily_of_roofedCompleted
      G B.base_warp (hL.frontiersEssential B.baseStage) hcompletedRoof
        hcleanAvoid' hcleanOwner
  have htargetAvoid' : G.vertexSet S.target ⊆
      (G.strictRoof (L.frontier B.baseStage))ᶜ := by
    rintro x ⟨p, hp, hxp⟩
    apply htargetAvoid
    exact ⟨p,
      RegularLiftCleanTargetSlice.restrictLeftInter.target_subset
        S₀ hDleft hp,
      hxp⟩
  have htargetOwner : G.vertexSet S.target ∩
      L.frontier B.baseStage ⊆
      G.vertexSet (pendingPart G B.base) := by
    apply RegularRoofSuffixCompatibility.frontierOwner_of_sourcePure G
    · intro p hp
      exact S₀.source_pure p (Or.inl
        (RegularLiftCleanTargetSlice.restrictLeftInter.target_subset
          S₀ hDleft hp))
    · rw [S.target_initial]
      exact Set.inter_subset_right
  have htargetCross : Disjoint
      (G.vertexSet (completedPart G B.base)) (G.vertexSet S.target) :=
    RegularRoofSuffixCompatibility.disjoint_subfamily_of_roofedCompleted
      G B.base_warp (hL.frontiersEssential B.baseStage) hcompletedRoof
        htargetAvoid' htargetOwner
  have hcross : Disjoint
      (G.vertexSet (completedPart G B.base))
      (G.vertexSet (S.target ∪ S.clean)) := by
    apply Set.disjoint_left.2
    intro x hxCompleted hxInstalled
    obtain ⟨p, hpTarget | hpClean, hxp⟩ := hxInstalled
    · exact Set.disjoint_left.1 htargetCross hxCompleted
        ⟨p, hpTarget, hxp⟩
    · exact Set.disjoint_left.1 hcleanCross hxCompleted
        ⟨p, hpClean, hxp⟩
  have hcleanStep : RegularCompletedPendingSplice.IsCleanTargetStep
      G B.base (S.target ∪ S.clean) hcompat := by
    apply RegularCompletedPendingSplice.IsCleanTargetStep.of_disjoint_slice
      B.base_warp S.union_warp
    exact hcross
  have husedRoof : G.vertexSet (S.target ∪ S.clean) ⊆
      G.roof (L.frontier beta) := by
    rintro x ⟨p, hpTarget | hpClean, hxp⟩
    · apply htargetRoof
      exact ⟨p, htarget ▸
        RegularLiftCleanTargetSlice.restrictLeftInter.target_subset
          S₀ hDleft hpTarget, hxp⟩
    · exact (hannular.2 ⟨p,
        hcleanInstalled (hclean ▸
          RegularLiftCleanTargetSlice.restrictLeftInter.clean_subset
            S₀ hDleft hpClean),
        hxp⟩).2
  have hresultRoof : G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G B.base
        (S.target ∪ S.clean) hcompat) ⊆
      G.roof (L.frontier beta) :=
    RegularRoofedAnnularSuccessor.freezeCompletedStar_vertexSet_subset_roof
      G hcompat (hL.frontierChronology hab) B.base_below_roof husedRoof
  have hrequiredUnselected :
      RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous B.base \
            (E ∩ D) ⊆ D \ E := by
    intro x hx
    refine ⟨hrequiredD hx.1, ?_⟩
    intro hxE
    exact hx.2 ⟨hxE, hrequiredD hx.1⟩
  have hcleanRequired : LinksToTarget G S.clean
      (RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous B.base \
          (E ∩ D)) := by
    apply RegularLiftCleanTargetSlice.restrictLeftInter.clean_links
      S₀ hDleft
    · rw [hclean]
      apply ControlledSlices.linksToTarget_mono G P.clean _ hcleanLinks
      intro x hx
      refine ⟨hrequired hx.1, ?_⟩
      exact fun hxE ↦ hx.2 ⟨hxE, hrequiredD hx.1⟩
    · exact hrequiredUnselected
  have hcleanIntervals : SliceCandidate.HasStageIntervalSegments
      G L S.clean B.baseStage beta := by
    apply RegularLiftCleanTargetSlice.restrictLeftInter.cleanIntervals
      S₀ hDleft
    simpa only [hclean] using hintervals
  have hcleanMavericksSmall :
      #(ControlledSlices.sliceMavericks G (L.warpAt beta) S.clean) <
        kappa := by
    apply RegularLiftCleanTargetSlice.restrictLeftInter.cleanMavericks_small
      S₀ hDleft
    simpa only [hclean] using hmavericksSmall
  have hcleanMavericksClosed : G.vertexSet
      (ControlledSlices.sliceMavericks G (L.warpAt beta) S.clean) ⊆ Z := by
    apply RegularLiftCleanTargetSlice.restrictLeftInter.cleanMavericks_closed
      S₀ hDleft
    rintro x ⟨p, hp, hxp⟩
    apply hregistered
    apply RegularWeakSplitCandidate.chosen_cleanMaverick_vertices_subset_registered
      G L tableRequest B.baseStage beta gamma
    refine ⟨p, ?_, hxp⟩
    exact ⟨hclean ▸ hp.1, hp.2⟩
  have hindex : ∀ j (hji : j < i),
      (previous j hji).stageIndex < beta := by
    intro j hji
    exact lt_of_le_of_lt (B.index_le_base j hji) hab
  let input :
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
      index_strict := hindex
      selected := E ∩ D
      required_subset_left := hrequiredD
      slice := S
      compatible := hcompat
      cleanStep := hcleanStep
      installed_star_finite := hstarFinite
      vertices_closed := hresultClosed
      pending_below_roof := by
        rintro x ⟨p, hp, hxp⟩
        exact hresultRoof ⟨p, hp.1, hxp⟩
      old_pending_boundary := hOldBoundary
      old_pending_status := B.old_pending_status
      clean_links_unselected := hcleanRequired
      cleanIntervals := hcleanIntervals
      cleanMavericks_small := hcleanMavericksSmall
      cleanMavericks_closed := hcleanMavericksClosed }
  exact ⟨
    { input := input
      result_below_roof := by
        simpa only [input] using hresultRoof }⟩

end RegularWeakSelectedSource915Adapter
end CardinalInduction
end Erdos599
