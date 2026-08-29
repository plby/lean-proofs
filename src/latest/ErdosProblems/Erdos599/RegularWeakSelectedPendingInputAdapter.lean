/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularPendingRoofCompatibility
import ErdosProblems.Erdos599.RegularPendingOnlyHistoryBase
import ErdosProblems.Erdos599.RegularLiftCleanTargetSlice
import ErdosProblems.Erdos599.RegularDirectPersistentCanonicalSuccessor
import ErdosProblems.Erdos599.RegularRoofedAnnularSuccessor

/-!
# Installing a selected weak coordinate from the pending-roof invariant

Completed target components need not remain below later ladder roofs.  This
module packages the selected-coordinate successor using only the roof bound
on the pending subfamily.  The genuinely history-sensitive obligation is
stated explicitly: the newly installed target/clean tracks must avoid the
carrier of every already completed component.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakSelectedPendingInputAdapter

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- Restrict a full-frontier weak annular split to the active pending
frontier.  Pending-roof compatibility supplies the star and the next
pending-roof bound; completed-versus-installed disjointness supplies the
exact clean-step certificate.  No roof claim is made about frozen completed
paths. -/
theorem exists_directSelectedSplitInput_of_annular
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (B : RegularPendingOnlyHistoryBase.HistoryBase
      G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized)
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
    /- Only the clean continuation is annular.  Completed target ears are
    deliberately kept outside this comparison. -/
    (hcleanInstalled : S.clean ⊆ comparison)
    (hcleanLinks : LinksToTarget G S.clean (Utable \ selected))
    (hintervals : SliceCandidate.HasStageIntervalSegments
      G L S.clean B.baseStage beta)
    (hmavericks : #(ControlledSlices.sliceMavericks G
      (L.warpAt beta) S.clean) < kappa)
    (hrestrictedClosed : G.vertexSet
      ((RegularLiftCleanTargetSlice.restrictLeftInter S
        B.pending_tight.1.terminalFrontier_subset).target ∪
       (RegularLiftCleanTargetSlice.restrictLeftInter S
        B.pending_tight.1.terminalFrontier_subset).clean) ⊆ Z)
    /- Registration may place the already completed carrier below this
    later roof even though that fact is not an invariant of arbitrary
    pending-only histories. -/
    (hcompletedRoof : G.vertexSet (completedPart G B.base) ⊆
      G.roof (L.frontier B.baseStage)) :
    Nonempty
      (RegularDirectPersistentCanonicalSuccessor.DirectSelectedSplitInput
        G L Sigma Z A request i previous) := by
  let D := G.terminalFrontier (pendingPart G B.base)
  have hDleft : D ⊆ L.frontier B.baseStage :=
    B.pending_tight.1.terminalFrontier_subset
  let slice := RegularLiftCleanTargetSlice.restrictLeftInter S hDleft
  have htargetAvoid : G.vertexSet S.target ⊆
      (G.strictRoof (L.frontier B.baseStage))ᶜ :=
    RegularPendingRoofCompatibility.target_vertexSet_subset_compl_strictRoof
      G hNorm (hL.frontiersEssential B.baseStage) S
  have hcleanAvoid : G.vertexSet S.clean ⊆
      (G.strictRoof (L.frontier B.baseStage))ᶜ := by
    rintro x ⟨p, hp, hxp⟩
    exact (hcomparison.2 ⟨p, hcleanInstalled hp, hxp⟩).1
  have husedAvoid : G.vertexSet (S.target ∪ S.clean) ⊆
      (G.strictRoof (L.frontier B.baseStage))ᶜ := by
    rintro x ⟨p, hpTarget | hpClean, hxp⟩
    · exact htargetAvoid ⟨p, hpTarget, hxp⟩
    · exact hcleanAvoid ⟨p, hpClean, hxp⟩
  have hfullCompat : G.StarCompatible (pendingPart G B.base)
      (S.target ∪ S.clean) :=
    RegularPendingRoofCompatibility.starCompatible_cleanTargetSlice_of_pendingRoof
      G (hL.frontiersEssential B.baseStage) B.pending_below_roof
        B.pending_tight.2 S husedAvoid
  have hsliceSubset : slice.target ∪ slice.clean ⊆
      S.target ∪ S.clean :=
    RegularLiftCleanTargetSlice.restrictLeftInter.union_subset S hDleft
  let hcompat : G.StarCompatible (pendingPart G B.base)
      (slice.target ∪ slice.clean) :=
    fun p hp q hq x hxp hxq ↦
      hfullCompat p hp q (hsliceSubset hq) x hxp hxq
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
  have hcleanCross : Disjoint
      (G.vertexSet (completedPart G B.base))
      (G.vertexSet slice.clean) := by
    have hcleanAvoid' : G.vertexSet slice.clean ⊆
        (G.strictRoof (L.frontier B.baseStage))ᶜ := by
      rintro x ⟨p, hp, hxp⟩
      apply hcleanAvoid
      exact ⟨p,
        RegularLiftCleanTargetSlice.restrictLeftInter.clean_subset
          S hDleft hp,
        hxp⟩
    have hcleanOwner : G.vertexSet slice.clean ∩
        L.frontier B.baseStage ⊆
        G.vertexSet (pendingPart G B.base) := by
      apply
        RegularRoofedAnnularSuccessor.frontierOwner_of_subfamily_of_sourceExactWarp
          G hcomparison.1.1.isWarp hcomparison.1.1.initialSet_eq
      · intro p hp
        exact hcleanInstalled
          (RegularLiftCleanTargetSlice.restrictLeftInter.clean_subset
            S hDleft hp)
      · rw [slice.clean_initial]
        exact Set.sdiff_subset
    exact RegularRoofSuffixCompatibility.disjoint_subfamily_of_roofedCompleted
      G B.base_warp (hL.frontiersEssential B.baseStage) hcompletedRoof
        hcleanAvoid' hcleanOwner
  have htargetAvoid' : G.vertexSet slice.target ⊆
      (G.strictRoof (L.frontier B.baseStage))ᶜ := by
    rintro x ⟨p, hp, hxp⟩
    apply htargetAvoid
    exact ⟨p,
      RegularLiftCleanTargetSlice.restrictLeftInter.target_subset
        S hDleft hp,
      hxp⟩
  have htargetOwner : G.vertexSet slice.target ∩
      L.frontier B.baseStage ⊆
      G.vertexSet (pendingPart G B.base) := by
    apply RegularRoofSuffixCompatibility.frontierOwner_of_sourcePure G
    · intro p hp
      exact S.source_pure p (Or.inl
        (RegularLiftCleanTargetSlice.restrictLeftInter.target_subset
          S hDleft hp))
    · rw [slice.target_initial]
      exact Set.inter_subset_right
  have htargetCross : Disjoint
      (G.vertexSet (completedPart G B.base))
      (G.vertexSet slice.target) :=
    RegularRoofSuffixCompatibility.disjoint_subfamily_of_roofedCompleted
      G B.base_warp (hL.frontiersEssential B.baseStage) hcompletedRoof
        htargetAvoid' htargetOwner
  have hcross : Disjoint
      (G.vertexSet (completedPart G B.base))
      (G.vertexSet (slice.target ∪ slice.clean)) := by
    apply Set.disjoint_left.2
    intro x hxCompleted hxInstalled
    obtain ⟨p, hpTarget | hpClean, hxp⟩ := hxInstalled
    · exact Set.disjoint_left.1 htargetCross hxCompleted
        ⟨p, hpTarget, hxp⟩
    · exact Set.disjoint_left.1 hcleanCross hxCompleted
        ⟨p, hpClean, hxp⟩
  have hcleanStep : RegularCompletedPendingSplice.IsCleanTargetStep
      G B.base (slice.target ∪ slice.clean) hcompat := by
    apply RegularCompletedPendingSplice.IsCleanTargetStep.of_disjoint_slice
      B.base_warp slice.union_warp
    simpa only [slice, D, hDleft] using hcross
  have hpendingRoof : G.vertexSet
      (pendingPart G
        (RegularCompletedPendingSplice.freezeCompletedStar G B.base
          (slice.target ∪ slice.clean) hcompat)) ⊆
      G.roof (L.frontier beta) := by
    apply
      RegularPendingRoofCompatibility.pendingPart_freezeCompletedStar_vertexSet_subset_roof_clean
        G hNorm slice B.pending_tight.1.finiteCharacter hcompat
          (hL.frontierChronology hab) B.pending_below_roof
    rintro x ⟨p, hp, hxp⟩
    have hpS : p ∈ S.clean :=
      RegularLiftCleanTargetSlice.restrictLeftInter.clean_subset
        S hDleft hp
    exact (hcomparison.2 ⟨p, hcleanInstalled hpS, hxp⟩).2
  exact ⟨
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
      cleanStep := hcleanStep
      installed_star_finite := hstarFinite
      vertices_closed := hverticesClosed
      pending_below_roof := hpendingRoof
      old_pending_boundary := hOldBoundary
      old_pending_status := B.old_pending_status
      clean_links_unselected := hcleanLinksRequired
      cleanIntervals :=
        RegularLiftCleanTargetSlice.restrictLeftInter.cleanIntervals
          S hDleft hintervals
      cleanMavericks_small :=
        RegularLiftCleanTargetSlice.restrictLeftInter.cleanMavericks_small
          S hDleft hmavericks
      cleanMavericks_closed := hmavericksClosed }⟩

end RegularWeakSelectedPendingInputAdapter
end CardinalInduction
end Erdos599
