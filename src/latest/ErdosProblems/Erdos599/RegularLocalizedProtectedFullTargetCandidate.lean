/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularBetaSelection
import ErdosProblems.Erdos599.LadderSliceGeometry
import ErdosProblems.Erdos599.RegularLiftCleanTargetSlice
import ErdosProblems.Erdos599.RegularSliceStageCompletion
import ErdosProblems.Erdos599.RegularSliceStageLift
import ErdosProblems.Erdos599.RegularWeakSplitCandidate
import ErdosProblems.Erdos599.SingularSafeCarrierCardinal
import ErdosProblems.Erdos599.SingularFirstHitCleanPrefix

/-!
# The small whole-source regular coordinate

If a stage web has fewer than `kappa` sources, lower extension supplies a
full linkage to the original target.  Its entire carrier is registered
before the later frontier is chosen.  Once that carrier is roofed by the
later frontier, first-hit truncation gives the separate source-exact annular
comparison.  The original full linkage remains the completed target track;
the clean track and the comparison's target-link request are both empty.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularLocalizedProtectedFullTargetCandidate

open SliceSpliceSource

universe u

variable {V : Type u}

/-- A full target linkage is a clean-target slice with every source selected
and no clean complementary track.  No later-frontier terminal claim is made
about the target track. -/
noncomputable def fullTargetCleanSlice
    {Q : DWeb V} (hNorm : Q.IsNormalized) {T : Set V}
    {P : Set Q.DPath} (hP : IsLinkageBetween Q Q.source Q.target P) :
    RegularCompletedPendingSplice.CleanTargetSlice
      Q Q.source T Q.source where
  target := P
  clean := ∅
  union_warp := by simpa only [Set.union_empty] using hP.isWarp
  finiteCharacter := by
    intro p hp
    apply hP.finiteCharacter
    simpa only [Set.union_empty] using hp
  target_initial := hP.initialSet_eq
  clean_initial := by
    rw [Set.sdiff_self]
    apply Set.eq_empty_iff_forall_notMem.2
    rintro _ ⟨p, hp, _⟩
    exact hp.elim
  initial_cover := Set.Subset.rfl
  target_links := fullLinkage_linksToTarget hP Set.Subset.rfl
  clean_terminal := by
    rintro _ ⟨p, hp, _⟩
    exact hp.elim
  clean_terminal_only := by
    intro _ hp
    exact hp.elim
  source_pure := by
    intro p hp
    have hpP : p ∈ P := by simpa only [Set.union_empty] using hp
    apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxSource⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_initial_of_mem_path p hxp hxSource)
    · rintro x hx
      have hxp : x = p.initial := Set.mem_singleton_iff.1 hx
      subst x
      refine ⟨p.initial_mem_support, ?_⟩
      rw [← hP.initialSet_eq]
      exact ⟨p, hpP, rfl⟩

/-- Roofing the registered full target carrier puts every target endpoint on
the later frontier. -/
theorem terminalFrontier_subset_of_targetCarrier_roof
    {G : DWeb V} {Q : DWeb V} {T : Set V} {P : Set Q.DPath}
    (hP : IsLinkageBetween Q Q.source Q.target P)
    (hTarget : Q.target = G.target)
    (hroof : Q.vertexSet P ⊆ G.roof T) :
    Q.terminalFrontier P ⊆ T := by
  rintro b hb
  have hbTargetQ : b ∈ Q.target := hP.terminalFrontier_subset hb
  have hbTargetG : b ∈ G.target := hTarget ▸ hbTargetQ
  obtain ⟨p, hpP, hpb⟩ := hb
  exact SliceSpliceConstructor.target_mem_of_mem_roof hbTargetG
    (hroof ⟨p, hpP, Q.terminal_mem_support hpb⟩)

/-- The registered small-source branch gives a genuine repaired weak split
candidate.  The first-hit comparison links only `U \ selected`, which is
empty because every stage source is selected. -/
theorem exists_weakSplitAnnularCandidate_of_fullTarget
    {kappa : Cardinal.{u}} {G : DWeb V} {L : G.KappaLadder kappa}
    (hL : L.SliceGeometry)
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa}
    (hdeltaBeta : delta < beta)
    (hNorm : (L.stageWeb delta).IsNormalized)
    (hrequest : request delta gamma ⊆ L.frontier delta)
    {P : Set (L.stageWeb delta).DPath}
    (hP : IsLinkageBetween (L.stageWeb delta)
      (L.frontier delta) (L.stageWeb delta).target P)
    (hsourceSmall : #(L.frontier delta) < kappa)
    (hroof : (L.stageWeb delta).vertexSet P ⊆
      G.roof (L.frontier beta)) :
    ∃ C : RegularWeakSplitCandidate.WeakSplitFamilies G,
      RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate
        G L request delta beta gamma C := by
  let Q := L.stageWeb delta
  let U := request delta gamma
  let T := L.frontier beta
  have hPfull : IsLinkageBetween Q Q.source Q.target P := by
    simpa only [Q, DWeb.KappaLadder.frontier] using hP
  have htargetEq : Q.target = G.target := by
    rfl
  have hterminal : Q.terminalFrontier P ⊆ T := by
    exact terminalFrontier_subset_of_targetCarrier_roof
      hPfull htargetEq hroof
  let comparisonStage :=
    SingularFirstHitCleanPrefix.firstHitCleanPrefix Q P T
      hPfull.isWarp hPfull.finiteCharacter hPfull.initialSet_eq hterminal
  have hcomparisonStage : TightLinkageBetween Q Q.source T comparisonStage :=
    ⟨SingularFirstHitCleanPrefix.firstHitCleanPrefix_isLinkageBetween
        hPfull.isWarp hPfull.finiteCharacter hPfull.initialSet_eq hterminal,
      SingularFirstHitCleanPrefix.firstHitCleanPrefix_terminalClean
        hPfull.isWarp hPfull.finiteCharacter hPfull.initialSet_eq hterminal⟩
  have hremainingLinks : LinksToTarget Q comparisonStage
      (U \ Q.source) := by
    intro x hx
    exact (hx.2 (hrequest hx.1)).elim
  have hseparator : IsSeparatorFrom Q Q.source T := by
    simpa only [Q, T, DWeb.KappaLadder.frontier] using
      (RegularSliceStageCompletion.later_frontier_separates_stageWeb
        hL.frontierChronology hdeltaBeta)
  obtain ⟨hcomparisonTight, hcomparisonLinks, hcomparisonRegion⟩ :=
    RegularSliceStageLift.tightAnnularLinkage_liftStageFamily
      hL.roofsSourceAtStages hL.frontierChronology hdeltaBeta
        hcomparisonStage hremainingLinks hseparator
  let Sstage := fullTargetCleanSlice hNorm (T := T) hPfull
  let S := RegularLiftCleanTargetSlice.liftStageSlice L delta Sstage
  let comparison := SliceSegmentCore.liftStageFamily L delta comparisonStage
  have hannular : SliceSplice.IsAnnularSlice G L comparison delta beta
      (U \ Q.source) :=
    ⟨⟨hcomparisonTight.1, hcomparisonLinks⟩, hcomparisonRegion⟩
  have htargetSmallStage : #P < kappa :=
    (SliceCandidate.mk_linkage_le_initial Q hPfull).trans_lt
      (by simpa only [Q, DWeb.KappaLadder.frontier] using hsourceSmall)
  have htargetSmall : #S.target < kappa :=
    (SliceSegmentCore.mk_liftStageFamily_le L delta P).trans_lt
      htargetSmallStage
  have hcleanEmpty : S.clean = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro p hp
    obtain ⟨q, hq, _⟩ := hp
    exact hq.elim
  refine ⟨⟨S.target, S.clean, comparison⟩, ?_⟩
  unfold RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate
  dsimp only [U, Q, T]
  refine ⟨L.frontier delta, ?_, S, rfl, rfl, ?_, ?_, ?_,
    htargetSmall, ?_, ?_, ?_⟩
  · intro x hx
    exact hrequest hx.1.1
  · simpa only [DWeb.KappaLadder.frontier] using hannular
  · rw [hcleanEmpty]
    exact Set.empty_subset _
  · change G.vertexSet (SliceSegmentCore.liftStageFamily L delta P) ⊆
      G.roof (L.frontier beta)
    rw [RegularLiftCleanTargetSlice.vertexSet_liftStageFamily]
    exact hroof
  · rw [hcleanEmpty]
    intro x hx
    exact (hx.2 (hrequest hx.1)).elim
  · rw [hcleanEmpty]
    intro p hp
    exact hp.elim
  · have hmavericks : ControlledSlices.sliceMavericks G
        (L.warpAt beta) S.clean = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro p hp
      exact (hcleanEmpty ▸ hp.1).elim
    rw [hmavericks, Cardinal.mk_emptyCollection]
    exact Cardinal.aleph0_pos.trans hL.uncountable

end RegularLocalizedProtectedFullTargetCandidate
end CardinalInduction
end Erdos599
