/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardSpliceDescent

/-!
# Reindexing strict forward-splice descent

The same-tail forward-splice step either roots the selected forward head or
restarts the native-frontier normalizer at a strictly earlier position on
the same parent.  This file transports the latter normalizer result back to
the original state, preserving the ancestry required by the final frontier
exchange.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open PopularGroundingBridge GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev ForwardNormalizationControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev ForwardNormalizationRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev ForwardNormalizationFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev ForwardNormalizationEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
    (ForwardNormalizationControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (ForwardNormalizationFrontier (L := L) (hL := hL) (S := S))

private abbrev ForwardNormalizationSources : Set V :=
  Gamma.source \ {
    (ForwardNormalizationRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)).record.initial}

/-- An ancestry-preserving normalization result whose terminal deleted head
is genuinely earlier than the initial one.  This is the well-founded payload
needed when a same-parent forward splice repeats. -/
structure SplitGroundedFreshRelevantBackwardStrictNormalizationResult
    (initial : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)) where
  outcome : L.SplitGroundedFreshRelevantBackwardNormalizedOutcome
    (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  same_parent : outcome.terminalState.parent = initial.parent
  terminal_head_before : GroundingCut.Before initial.parent
    outcome.terminalState.deleted.head initial.deleted.head
  terminal_finish_beforeEq : GroundingCut.BeforeEq initial.parent
    outcome.terminalState.rootPath.finish initial.rootPath.finish

/-- A strict same-tail descent can be reindexed over its original state.
Consequently the only nonrecursive alternative is a genuine root of the
selected forward head in the actual stopped relation. -/
theorem SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRooted_or_rebasedNormalization
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ForwardNormalizationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardNormalizationFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1) :
    (∃ a ∈ ForwardNormalizationSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardNormalizationEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        a splice.contact.forwardEdge.2) ∨
      L.SplitGroundedFreshRelevantBackwardNormalizationResult state := by
  rcases
      SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRooted_or_strictDescent
        state splice same_tail with
    hroot | ⟨next, hparent, hnextFinish, hhead, _hprecedes, hresult⟩
  · exact Or.inl hroot
  · right
    rcases hresult with ⟨outcome, hsame, hbefore, hfinish⟩
    rw [hparent] at hbefore
    exact SplitGroundedFreshRelevantBackwardNormalizationResult.mk outcome
      (hsame.trans hparent)
      (GroundingFragmentResidualOrder.beforeEq_trans hbefore hhead.1)
      (GroundingFragmentResidualOrder.beforeEq_trans
        (by simpa only [hparent] using hfinish) hnextFinish)

/-- Strict version of the same-parent descent.  Unlike the convenient
rebased result above, this statement does not forget that the recursive
terminal head moved genuinely earlier on the unchanged parent. -/
theorem SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRooted_or_strictNormalization
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ForwardNormalizationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardNormalizationFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1) :
    (∃ a ∈ ForwardNormalizationSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardNormalizationEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        a splice.contact.forwardEdge.2) ∨
      Nonempty
        (L.SplitGroundedFreshRelevantBackwardStrictNormalizationResult state) := by
  rcases
      SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRooted_or_strictDescent
        state splice same_tail with
    hroot | ⟨next, hparent, hnextFinish, hhead, _hprecedes, hresult⟩
  · exact Or.inl hroot
  · right
    rcases hresult with ⟨outcome, hsame, hbefore, hfinish⟩
    have hbefore' : GroundingCut.BeforeEq state.parent
        outcome.terminalState.deleted.head next.deleted.head := by
      simpa only [hparent] using hbefore
    have hfinish' : GroundingCut.BeforeEq state.parent
        outcome.terminalState.rootPath.finish next.rootPath.finish := by
      simpa only [hparent] using hfinish
    exact ⟨{
      outcome := outcome
      same_parent := hsame.trans hparent
      terminal_head_before :=
        splitGroundedFreshAvoiding_before_of_beforeEq_before
          state.parent hbefore' hhead
      terminal_finish_beforeEq :=
        GroundingFragmentResidualOrder.beforeEq_trans
          hfinish' hnextFinish }⟩

/-- Strict ancestry-preserving form of native-frontier departure progress.
The nonrooted-tail branch restarts normalization strictly earlier on the
same parent. -/
theorem SplitGroundedFreshRelevantBackwardNormalizedOutcome.boundaryDeparture_rooted_or_strictNormalization
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (tail : V)
    (incoming_mem : (tail, state.deleted.head) ∈ state.rootPath.edgeSet)
    (residual : (tail, state.deleted.head) ∈ residualLadderEdges
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S)
    (tail_mem : tail ∈ ForwardNormalizationFrontier
      (L := L) (hL := hL) (S := S)) :
    (∃ a ∈ ForwardNormalizationSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardNormalizationEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a tail) ∨
      Nonempty
        (L.SplitGroundedFreshRelevantBackwardStrictNormalizationResult state) := by
  rcases
      SplitGroundedFreshRelevantBackwardNormalizedOutcome.boundaryDeparture_rooted_or_strictDescent
        state tail incoming_mem residual tail_mem with
    hroot | ⟨next, hparent, hnextFinish, hhead, _hprecedes, hresult⟩
  · exact Or.inl hroot
  · right
    rcases hresult with ⟨outcome, hsame, hbefore, hfinish⟩
    have hbefore' : GroundingCut.BeforeEq state.parent
        outcome.terminalState.deleted.head next.deleted.head := by
      simpa only [hparent] using hbefore
    have hfinish' : GroundingCut.BeforeEq state.parent
        outcome.terminalState.rootPath.finish next.rootPath.finish := by
      simpa only [hparent] using hfinish
    exact ⟨{
      outcome := outcome
      same_parent := hsame.trans hparent
      terminal_head_before :=
        splitGroundedFreshAvoiding_before_of_beforeEq_before
          state.parent hbefore' hhead
      terminal_finish_beforeEq :=
        GroundingFragmentResidualOrder.beforeEq_trans
          hfinish' hnextFinish }⟩

/-- Combined same-tail progress: either the selected suffix reaches an
actually rooted stopping-frontier point, it reaches the finish of the
concrete forward link (retaining all provenance), or normalization restarts
strictly earlier while remaining indexed by the original state. -/
theorem SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_advances_or_rebasedNormalization
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ForwardNormalizationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardNormalizationFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1) :
    (∃ b ∈ ForwardNormalizationFrontier
          (L := L) (hL := hL) (S := S),
        ∃ a ∈ ForwardNormalizationSources
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S),
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardNormalizationEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a b) ∨
      (∃ l : Alternating.Link Gamma.graph,
        l ∈ (selectedErasedCompression
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
          (ForwardNormalizationControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest splice.contact.owner.1)).path.links ∧
        l.direction = .forward ∧
        splice.contact.forwardEdge ∈ l.path.edgeSet ∧
        ∃ a ∈ ForwardNormalizationSources
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S),
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardNormalizationEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a l.path.finish) ∨
      L.SplitGroundedFreshRelevantBackwardNormalizationResult state := by
  rcases
      SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRooted_or_rebasedNormalization
        state splice same_tail with hhead | hnormalized
  · rcases
        SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRoot_advances
          state splice hhead with hboundary | hfinish
    · exact Or.inl hboundary
    · exact Or.inr (Or.inl hfinish)
  · exact Or.inr (Or.inr hnormalized)

/-- Complete same-tail forward-splice normalization.  Besides an actual
rooted stopping-frontier point and a rooted request exit, the only
route-order alternative is a strictly later backward link already converted
to a concrete native-frontier normalization state.  Repeated same-parent
splices remain represented by the ancestry-preserving rebased result. -/
theorem SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_advances_or_backwardNormalization_or_rebased
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ForwardNormalizationControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardNormalizationFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1) :
    (∃ b ∈ ForwardNormalizationFrontier
          (L := L) (hL := hL) (S := S),
        ∃ a ∈ ForwardNormalizationSources
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S),
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardNormalizationEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a b) ∨
      (∃ a ∈ ForwardNormalizationSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ForwardNormalizationEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a
          (requestExit (chosenRequest splice.contact.owner.1))) ∨
      (∃ (Q : Alternating.FiniteTrace Gamma.graph)
          (i j : Fin (Q.lastIndex + 1))
          (l b : Alternating.Link Gamma.graph) (parent : Gamma.DPath)
          (next : L.SplitGroundedFreshRelevantBackwardState
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)),
        (selectedErasedCompression
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
          (ForwardNormalizationControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest splice.contact.owner.1)).path = .finite Q ∧
        Q.link i = l ∧ Q.link j = b ∧ i < j ∧
        l.direction = .forward ∧
        b.direction = .backward ∧
        parent ∈ (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths ∧
        b.path.IsSubpathOf parent ∧
        next.control = splice.contact.owner ∧ next.parent = parent ∧
        L.SplitGroundedFreshRelevantBackwardNormalizationResult next) ∨
      L.SplitGroundedFreshRelevantBackwardNormalizationResult state := by
  rcases
      SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_advances_or_rebasedNormalization
        state splice same_tail with hboundary | hfinish | hnormalized
  · exact Or.inl hboundary
  · obtain ⟨l, hl, hldir, _hf, hroot⟩ := hfinish
    rcases L.splitGroundedFreshRelevant_forwardLinkFinish_advances_or_backwardNormalization
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) splice.contact.owner l hl hldir hroot with
      hboundary | hexit | ⟨Q, i, j, b, parent, next, hpath, hi, hj,
        hij, hbdir, hparent, hbsub, hcontrol, hnextParent, hnext⟩
    · exact Or.inl hboundary
    · exact Or.inr (Or.inl hexit)
    · exact Or.inr (Or.inr (Or.inl ⟨Q, i, j, l, b, parent, next,
        hpath, hi, hj, hij, hldir, hbdir, hparent, hbsub, hcontrol,
        hnextParent, hnext⟩))
  · exact Or.inr (Or.inr (Or.inr hnormalized))

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRooted_or_rebasedNormalization
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRooted_or_strictNormalization
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardNormalizedOutcome.boundaryDeparture_rooted_or_strictNormalization
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_advances_or_rebasedNormalization
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_advances_or_backwardNormalization_or_rebased
