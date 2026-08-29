/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardClusterEntry
import ErdosProblems.Erdos599.FamilyTools

/-!
# The finite component cluster met by one forward exchange segment

The component exchange is not confined to the component containing its
first retained-forward tail.  A later part of the same selected route can
enter another reachable component.  The honest local object is therefore
the finite family of reachable finite components which meet the concrete
old-parent segment.

This file proves two facts about that family.  It is finite, by warp
disjointness and finiteness of the segment.  Moreover each member either is
the component already ending at the selected first frontier hit, or its
first segment contact is entered by a retained forward edge of the same
selected owner.  Thus iteration of the exchange is over an actual finite
component cluster, not an asserted single component.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev FiniteClusterIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev FiniteClusterControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev FiniteClusterFrontier : Set V :=
  L.splitGroundedFreshRelevantStoppingFrontier (hL := hL) (S := S)

private abbrev FiniteClusterEdges : Set (V × V) :=
  L.splitGroundedFreshRelevantSwitchedEdges
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)

private abbrev FiniteClusterSources : Set V :=
  Gamma.source \ {
    (L.splitGroundedFreshAvoidingCanonicalUnusedRecord
      hL hground hnotFresh S).record.initial}

/-- The finite members of `W` which meet the concrete exchange segment. -/
def splitGroundedFreshRelevantFiniteSegmentCluster
    (W : Set Gamma.DPath) (segment : FinitePath Gamma.graph) :
    Set (FinitePath Gamma.graph) :=
  {p | (Sum.inl p : Gamma.DPath) ∈ W ∧
    (p.support ∩ segment.support).Nonempty}

/-- The segment cluster after removing the component which already contains
the original retained-forward tail. -/
def splitGroundedFreshRelevantDisplacedFiniteSegmentCluster
    (W : Set Gamma.DPath) (segment : FinitePath Gamma.graph) (tail : V) :
    Set (FinitePath Gamma.graph) :=
  {p | p ∈ splitGroundedFreshRelevantFiniteSegmentCluster W segment ∧
    tail ∉ p.support}

/-- A warp has only finitely many finite members meeting a fixed finite
segment. -/
theorem splitGroundedFreshRelevantFiniteSegmentCluster_finite
    (W : Set Gamma.DPath) (hW : Gamma.IsWarp W)
    (segment : FinitePath Gamma.graph) :
    (splitGroundedFreshRelevantFiniteSegmentCluster W segment).Finite := by
  apply FamilyTools.finite_of_pairwiseDisjoint_of_meets
    (F := fun p : FinitePath Gamma.graph ↦ p.support)
    (S := segment.support)
  · intro p hp q hq hpq
    apply hW hp.1 hq.1
    intro hpqPath
    apply hpq
    exact Sum.inl.inj hpqPath
  · exact segment.support_finite
  · intro p hp
    obtain ⟨z, hzp, hzSegment⟩ := hp.2
    exact ⟨z, hzSegment, hzp⟩

/-- Every member of the finite reachable component cluster is either the
component containing the original conflict tail (and hence ends at the
exact selected first hit), or it has a literal same-owner retained-forward
entry at its first contact with the segment.

The hypotheses are the exact equations exported by the canonical
source-reachable component warp, rather than a component-rooting provider. -/
theorem SplitGroundedReducedForwardConflictSpliceData.finiteSegmentCluster_entry_or_currentSink
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := FiniteClusterControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (FiniteClusterFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (X : L.SplitGroundedFreshRelevantForwardFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S)
      (FiniteClusterSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) state splice)
    (owner_eq : splice.contact.owner.1 = state.control.1)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
    (segment : FinitePath Gamma.graph)
    (hsegmentStart : segment.start = splice.incomingTail)
    (hsegmentSupport : segment.support ⊆ state.parent.support)
    (hsegmentEdges : segment.edgeSet ⊆ state.parent.edgeSet)
    (W : Set Gamma.DPath) (hW : Gamma.IsWarp W)
    (hWEdges : familyEdges W =
      RootReachableRelation.edges
        (FiniteClusterEdges (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (FiniteClusterSources (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)))
    (hWInitial : Gamma.initialSet W =
      FiniteClusterSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
    (hWTerminal : Gamma.terminalFrontier W =
      L.splitGroundedFreshReachableSinkBoundary
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) :
    (splitGroundedFreshRelevantFiniteSegmentCluster W segment).Finite ∧
      ∀ old ∈ splitGroundedFreshRelevantFiniteSegmentCluster W segment,
        (splice.incomingTail ∈ old.support ∧
          old.finish = X.path.finish) ∨
        ∃ (u z : V),
          (u, z) ∈ old.edgeSet ∧
          z ∈ segment.support ∧ z ∈ old.support ∧
          GroundingCut.Before state.parent splice.incomingTail z ∧
          (u, z) ∈ retainedForwardEdgesAt
            (FiniteClusterFrontier (L := L) (hL := hL) (S := S))
            (selectedErasedCompression
              (FiniteClusterIndexed (L := L) (hL := hL)
                (hground := hground)) S
              (FiniteClusterControls (L := L) (hL := hL)
                (hground := hground) (hnotFresh := hnotFresh) (S := S))
              (chosenRequest splice.contact.owner.1)).path := by
  refine ⟨splitGroundedFreshRelevantFiniteSegmentCluster_finite W hW segment,
    ?_⟩
  intro old holdCluster
  have holdW : (Sum.inl old : Gamma.DPath) ∈ W := holdCluster.1
  have holdStart : old.start ∈ FiniteClusterSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) := by
    rw [← hWInitial]
    exact ⟨.inl old, holdW, rfl⟩
  have holdEdges : old.edgeSet ⊆ FiniteClusterEdges
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) := by
    intro e he
    apply RootReachableRelation.edges_subset
      (FiniteClusterEdges (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (FiniteClusterSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
    rw [← hWEdges]
    exact Set.mem_iUnion.2 ⟨.inl old, Set.mem_iUnion.2 ⟨holdW, he⟩⟩
  have holdFinish : old.finish ∈
      L.splitGroundedFreshReachableSinkBoundary
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) := by
    rw [← hWTerminal]
    exact ⟨.inl old, holdW, rfl⟩
  by_cases htail : splice.incomingTail ∈ old.support
  · left
    exact ⟨htail, X.displacedComponent_finish_eq_of_tail_mem
      hNoEnter state splice same_tail old holdEdges holdFinish htail⟩
  · right
    obtain ⟨u, z, huz, hzSegment, hzOld, hzAfter, huzForward⟩ :=
      splice.exists_sameOwnerForwardEntry_of_segment_meet_of_tail_not_mem
        hNoEnter state owner_eq same_tail segment old hsegmentStart
          hsegmentSupport hsegmentEdges holdStart holdEdges
          (by
            obtain ⟨z, hzOld, hzSegment⟩ := holdCluster.2
            exact ⟨z, hzSegment, hzOld⟩)
          htail
    exact ⟨u, z, huz, hzSegment, hzOld, hzAfter, huzForward⟩

/-- Distinct displaced finite components have distinct first-entry edges of
the same selected route.  This is the concrete finite recursion measure for
the owner-cluster switch: the component family injects into the literal
retained forward edges of one finite selected compression.

The chosen entry edge is retained together with its membership in the
corresponding component, so a subsequent occurrence-word construction can
recover both the selected-route occurrence and the displaced component. -/
theorem SplitGroundedReducedForwardConflictSpliceData.exists_injective_sameOwnerEntries
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := FiniteClusterControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (FiniteClusterFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (owner_eq : splice.contact.owner.1 = state.control.1)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
    (segment : FinitePath Gamma.graph)
    (hsegmentStart : segment.start = splice.incomingTail)
    (hsegmentSupport : segment.support ⊆ state.parent.support)
    (hsegmentEdges : segment.edgeSet ⊆ state.parent.edgeSet)
    (W : Set Gamma.DPath) (hW : Gamma.IsWarp W)
    (hWEdges : familyEdges W =
      RootReachableRelation.edges
        (FiniteClusterEdges (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (FiniteClusterSources (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)))
    (hWInitial : Gamma.initialSet W =
      FiniteClusterSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) :
    ∃ entry :
        splitGroundedFreshRelevantDisplacedFiniteSegmentCluster
            W segment splice.incomingTail →
          {e // e ∈ retainedForwardEdgesAt
            (FiniteClusterFrontier (L := L) (hL := hL) (S := S))
            (selectedErasedCompression
              (FiniteClusterIndexed (L := L) (hL := hL)
                (hground := hground)) S
              (FiniteClusterControls (L := L) (hL := hL)
                (hground := hground) (hnotFresh := hnotFresh) (S := S))
              (chosenRequest splice.contact.owner.1)).path},
      Function.Injective entry ∧
        ∀ p, (entry p).1 ∈ p.1.edgeSet := by
  let C := splitGroundedFreshRelevantDisplacedFiniteSegmentCluster
    W segment splice.incomingTail
  let F := retainedForwardEdgesAt
    (FiniteClusterFrontier (L := L) (hL := hL) (S := S))
    (selectedErasedCompression
      (FiniteClusterIndexed (L := L) (hL := hL) (hground := hground)) S
      (FiniteClusterControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (chosenRequest splice.contact.owner.1)).path
  have holdGeometry : ∀ p ∈ C,
      p.start ∈ FiniteClusterSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S) ∧
        p.edgeSet ⊆ FiniteClusterEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S) := by
    intro p hp
    have hpW : (Sum.inl p : Gamma.DPath) ∈ W := hp.1.1
    constructor
    · rw [← hWInitial]
      exact ⟨.inl p, hpW, rfl⟩
    · intro e he
      apply RootReachableRelation.edges_subset
        (FiniteClusterEdges (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (FiniteClusterSources (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
      rw [← hWEdges]
      exact Set.mem_iUnion.2 ⟨.inl p, Set.mem_iUnion.2 ⟨hpW, he⟩⟩
  have hentry : ∀ p : C, ∃ e : V × V, e ∈ p.1.edgeSet ∧ e ∈ F := by
    intro p
    obtain ⟨hstart, hedges⟩ := holdGeometry p.1 p.2
    obtain ⟨u, z, huz, _hzSegment, _hzOld, _hzAfter, huzForward⟩ :=
      splice.exists_sameOwnerForwardEntry_of_segment_meet_of_tail_not_mem
        hNoEnter state owner_eq same_tail segment p.1 hsegmentStart
          hsegmentSupport hsegmentEdges hstart hedges
          (by
            obtain ⟨z, hzOld, hzSegment⟩ := p.2.1.2
            exact ⟨z, hzSegment, hzOld⟩)
          p.2.2
    exact ⟨(u, z), huz, huzForward⟩
  let entry : C → {e // e ∈ F} := fun p ↦
    ⟨Classical.choose (hentry p), (Classical.choose_spec (hentry p)).2⟩
  refine ⟨entry, ?_, ?_⟩
  · intro p q hpq
    apply Subtype.ext
    by_contra hpqPath
    have hpEdge : (entry p).1 ∈ p.1.edgeSet :=
      (Classical.choose_spec (hentry p)).1
    have hqEdge : (entry q).1 ∈ q.1.edgeSet :=
      (Classical.choose_spec (hentry q)).1
    have hpHead : (entry p).1.2 ∈ p.1.support :=
      (p.1.edgeSet_subset_support_prod hpEdge).2
    have hqHead : (entry p).1.2 ∈ q.1.support := by
      have hedge : (entry p).1 = (entry q).1 :=
        congrArg Subtype.val hpq
      simpa only [hedge] using
        (q.1.edgeSet_subset_support_prod hqEdge).2
    exact Set.disjoint_left.1
      (hW p.2.1.1 q.2.1.1 (fun h ↦ hpqPath (Sum.inl.inj h)))
      hpHead hqHead
  · intro p
    exact (Classical.choose_spec (hentry p)).1

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevantFiniteSegmentCluster_finite
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.finiteSegmentCluster_entry_or_currentSink
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.exists_injective_sameOwnerEntries
