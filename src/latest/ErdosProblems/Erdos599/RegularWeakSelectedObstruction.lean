/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularHalfwaySplit
import ErdosProblems.Erdos599.RegularWeakSplitCandidate

/-!
# The selected obstruction set for a weak regular slice

Besides coordinates which persist on the chosen later frontier, the target
track must retain every requested non-target source already lying in the
half-way stop-over.  Removing precisely these additional coordinates makes
first-hit normalization of the complementary track target-link preserving.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakSelectedObstruction

universe u

variable {V : Type u}

/-- Persistent coordinates together with requested non-target stop-over
starts. -/
def selectedObstruction (G : DWeb V) (right C U : Set V) : Set V :=
  RegularWeakSplitCandidate.stagePersistent G right U ∪
    ((U \ G.target) ∩ C)

theorem stagePersistent_subset_selectedObstruction
    (G : DWeb V) (right C U : Set V) :
    RegularWeakSplitCandidate.stagePersistent G right U ⊆
      selectedObstruction G right C U :=
  Set.subset_union_left

theorem selectedObstruction_subset_request
    (G : DWeb V) (right C U : Set V) :
    selectedObstruction G right C U ⊆ U := by
  intro x hx
  rcases hx with hxPersistent | hxStopover
  · exact RegularWeakSplitCandidate.stagePersistent_subset_request
      G right U hxPersistent
  · exact hxStopover.1.1

theorem mk_selectedObstruction_lt
    {kappa : Cardinal.{u}} (G : DWeb V) (right C U : Set V)
    (hU : #U < kappa) :
    #(selectedObstruction G right C U) < kappa :=
  (Cardinal.mk_subtype_mono
    (selectedObstruction_subset_request G right C U)).trans_lt hU

/-- Every unselected designated non-target source avoids the stop-over. -/
theorem disjoint_unselected_nonTarget_stopover
    (G : DWeb V) (right C U : Set V) :
    Disjoint ((U \ selectedObstruction G right C U) \ G.target) C := by
  apply Set.disjoint_left.2
  intro x hxUnselected hxC
  apply hxUnselected.1.2
  exact Or.inr ⟨⟨hxUnselected.1.1, hxUnselected.2⟩, hxC⟩

/-- The canonical selected obstruction splits a half-way row into a small
completed target track and a terminal-clean complementary track which still
links every unselected requested source. -/
theorem exists_cleanTargetSlice_selectedObstruction
    {kappa : Cardinal.{u}} {Q : DWeb V} (hNorm : Q.IsNormalized)
    {C U : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q Q.source C W)
    (hUsource : U ⊆ Q.source) (hlinks : LinksToTarget Q W U)
    (hUsmall : #U < kappa) (right : Set V) :
    let E := selectedObstruction Q right C U
    ∃ S : RegularCompletedPendingSplice.CleanTargetSlice
        Q Q.source C E,
      LinksToTarget Q S.clean (U \ E) ∧
        #S.target < kappa ∧
        S.target ⊆ SingularExtension.completedPart Q W := by
  dsimp only
  let E := selectedObstruction Q right C U
  have hEsource : E ⊆ Q.source :=
    (selectedObstruction_subset_request Q right C U).trans hUsource
  have hElinks : LinksToTarget Q W E :=
    ControlledSlices.linksToTarget_mono Q W
      (selectedObstruction_subset_request Q right C U) hlinks
  obtain ⟨S, _hStarget, hSclean, hStargetCard, hStargetCompleted⟩ :=
    RegularHalfwaySplit.exists_cleanTargetSlice_of_halfway
      hNorm hW hEsource hElinks
  let M := U \ E
  let P := SliceSpliceSource.initialRestriction Q W (Q.source \ E)
  have hP : IsLinkageBetween Q (Q.source \ E) C P :=
    SliceSpliceSource.isLinkageBetween_initialRestriction hW Set.sdiff_subset
  have hMsource : M ⊆ Q.source := Set.sdiff_subset.trans hUsource
  have hMsub : M ⊆ Q.source \ E := by
    intro x hx
    exact ⟨hMsource hx, hx.2⟩
  have hMlinksW : LinksToTarget Q W M :=
    ControlledSlices.linksToTarget_mono Q W Set.sdiff_subset hlinks
  have hMlinksP : LinksToTarget Q P M := by
    apply SliceSegmentCore.linksToTarget_mono_family
      (W := SliceSpliceSource.initialRestriction Q W M)
    · intro p hp
      exact ⟨hp.1, hMsub hp.2⟩
    · exact RegularHalfwaySplit.linksToTarget_initialRestriction
        hW hMsource hMlinksW
  have hcleanLinks : LinksToTarget Q
      (RegularBetaSelection.targetFirstHitFamily hP) M :=
    RegularBetaSelection.targetFirstHitFamily_linksToTarget_of_subsource
      hNorm hP hMsub hMlinksP
        (disjoint_unselected_nonTarget_stopover Q right C U)
  refine ⟨S, ?_, hStargetCard.trans_lt
      (mk_selectedObstruction_lt Q right C U hUsmall),
    hStargetCompleted⟩
  simpa only [E, M, P, hSclean] using hcleanLinks

end RegularWeakSelectedObstruction
end CardinalInduction
end Erdos599
