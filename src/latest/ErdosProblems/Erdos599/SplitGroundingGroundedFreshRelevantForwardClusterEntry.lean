/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantResidualPredecessor

/-!
# The next component in a same-owner forward exchange cluster

A selected route can leave one reachable component and later enter another
one through a different forward link.  Thus the component met last by the
discarded parent tail need not be the component containing the original
conflict tail.  This module records the truthful replacement for that false
one-component claim.

If a finite reachable component meets the old-parent segment but does not
contain its initial conflict tail, take its first contact with the segment.
The incoming edge of the component at that contact cannot be residual: a
residual predecessor would be an earlier contact of the same component.
Rank protection excludes every other selected route, so the incoming edge
is a retained forward edge of the same active owner.  This is the concrete
successor step used by the finite component-cluster exchange.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingSourceReachableSinkWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev ClusterIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev ClusterControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev ClusterFrontier : Set V :=
  L.splitGroundedFreshRelevantStoppingFrontier (hL := hL) (S := S)

private abbrev ClusterEdges : Set (V × V) :=
  L.splitGroundedFreshRelevantSwitchedEdges
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)

private abbrev ClusterSources : Set V :=
  Gamma.source \ {
    (L.splitGroundedFreshAvoidingCanonicalUnusedRecord
      hL hground hnotFresh S).record.initial}

/-- If the displaced finite component already contains the conflict tail,
its sink is the exact first frontier hit stored by `X`.  This uses only
right-uniqueness and the fact that both endpoints are genuine reachable
sinks; it is independent of a particular component-warp realization. -/
theorem SplitGroundedFreshRelevantForwardFirstHit.displacedComponent_finish_eq_of_tail_mem
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ClusterControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ClusterFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (X : L.SplitGroundedFreshRelevantForwardFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S)
      (ClusterSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) state splice)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
    (old : FinitePath Gamma.graph)
    (holdEdges : old.edgeSet ⊆ ClusterEdges
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (holdFinish : old.finish ∈
      L.splitGroundedFreshReachableSinkBoundary
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
    (htailOld : splice.incomingTail ∈ old.support) :
    old.finish = X.path.finish := by
  let U := ClusterIndexed (L := L) (hL := hL) (hground := hground)
  let K := ClusterControls (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  let T := ClusterFrontier (L := L) (hL := hL) (S := S)
  let E := ClusterEdges (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let A := ClusterSources (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  have htailOldFinish : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) splice.incomingTail old.finish :=
    GroundingRootedReachabilityWarp.finitePath_reaches_finish_of_mem_support
      old holdEdges htailOld
  have hheadFinish : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E)
      splice.contact.forwardEdge.2 X.path.finish := by
    have h :=
      GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
        X.path X.path_edges X.path.finish_mem_support
    simpa only [X.path_start] using h
  have hforward : splice.contact.forwardEdge ∈ E := by
    exact GroundingErasedDecode.activeRetainedForwardEdgesAt_subset_switched
      U S K T splice.contact.owner splice.contact.retained
  have htailX : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) splice.incomingTail X.path.finish := by
    have hstep : Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ E)
        splice.contact.forwardEdge.1 splice.contact.forwardEdge.2 :=
      Relation.ReflTransGen.single hforward
    simpa only [same_tail] using hstep.trans hheadFinish
  have hright : Relator.RightUnique (fun x y ↦ (x, y) ∈ E) :=
    (GroundingErasedForwardConflict.erasedSelectedSwitchedEdgesAt_biUnique
      U S K T (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)).2
  have hXBoundary : X.path.finish ∈ sourceReachableSinkBoundary E A := by
    refine ⟨?_, ?_⟩
    · refine ⟨X.source, X.source_mem, ?_⟩
      exact (X.conflictTail_rooted Set.sdiff_subset hNoEnter
        state splice same_tail).trans htailX
    · exact GroundingErasedDecode.boundary_noOutgoing_switchedAt
        U S K T X.finish_mem
  have hOldBoundary : old.finish ∈ sourceReachableSinkBoundary E A := by
    simpa only [E, A, ClusterEdges, ClusterSources,
      splitGroundedFreshRelevantSwitchedEdges,
      splitGroundedFreshReachableSinkBoundary] using holdFinish
  rcases Relation.ReflTransGen.total_of_right_unique hright
      htailOldFinish htailX with hOldX | hXOld
  · exact sourceReachableSinkBoundary_isReachabilityAntichain E A
      hOldBoundary hXBoundary hOldX
  · exact (sourceReachableSinkBoundary_isReachabilityAntichain E A
      hXBoundary hOldBoundary hXOld).symm

/-- If a reachable finite component first appears strictly after the
conflict tail on the discarded old-parent segment, it is entered by a
retained forward edge of the same selected owner.  The theorem retains the
literal component edge and contact point, so the next cluster member can be
identified without any realization or provider assumption. -/
theorem SplitGroundedReducedForwardConflictSpliceData.exists_sameOwnerForwardEntry_of_segment_meet_of_tail_not_mem
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ClusterControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ClusterFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (owner_eq : splice.contact.owner.1 = state.control.1)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
    (segment old : FinitePath Gamma.graph)
    (hsegmentStart : segment.start = splice.incomingTail)
    (hsegmentSupport : segment.support ⊆ state.parent.support)
    (hsegmentEdges : segment.edgeSet ⊆ state.parent.edgeSet)
    (holdStart : old.start ∈ ClusterSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (holdEdges : old.edgeSet ⊆ ClusterEdges
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (hmeet : ∃ z, z ∈ segment.support ∧ z ∈ old.support)
    (htailNot : splice.incomingTail ∉ old.support) :
    ∃ (u z : V),
      (u, z) ∈ old.edgeSet ∧
      z ∈ segment.support ∧ z ∈ old.support ∧
      GroundingCut.Before state.parent splice.incomingTail z ∧
      (u, z) ∈ retainedForwardEdgesAt
        (ClusterFrontier (L := L) (hL := hL) (S := S))
        (selectedErasedCompression
          (ClusterIndexed (L := L) (hL := hL) (hground := hground)) S
          (ClusterControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest splice.contact.owner.1)).path := by
  let E := ClusterEdges (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let A := ClusterSources (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let hm : segment.walk.Meets old.support := by
    obtain ⟨z, hzSegment, hzOld⟩ := hmeet
    exact ⟨z, hzSegment, hzOld⟩
  let front := segment.firstHit old.support hm
  have hzOld : front.finish ∈ old.support :=
    segment.firstHit_finish_mem old.support hm
  have hzSegment : front.finish ∈ segment.support :=
    segment.firstHit_support_subset old.support hm front.finish_mem_support
  have hzParent : front.finish ∈ state.parent.support :=
    hsegmentSupport hzSegment
  have hzNeTail : front.finish ≠ splice.incomingTail := by
    intro hz
    apply htailNot
    simpa only [hz] using hzOld
  have hafterEq : GroundingCut.BeforeEq state.parent
      splice.incomingTail front.finish := by
    have h := freshRelevantFiniteSubpath_start_beforeEq_of_mem
      state.parent segment ⟨hsegmentSupport, hsegmentEdges⟩
      hzSegment
    simpa only [hsegmentStart] using h
  have hafter : GroundingCut.Before state.parent
      splice.incomingTail front.finish := ⟨hafterEq, Ne.symm hzNeTail⟩
  have hfrontStart : front.start = segment.start := rfl
  have hzNeFrontStart : front.finish ≠ front.start := by
    intro hz
    apply hzNeTail
    exact hz.trans (hfrontStart.trans hsegmentStart)
  have hzNeOldStart : front.finish ≠ old.start := by
    intro hzStart
    obtain ⟨v, hvFront⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
        front front.finish_mem_support hzNeFrontStart
    exact hNoEnter (front.edgeSet_subset_adj hvFront) (hzStart ▸ holdStart.1)
  obtain ⟨u, huOld⟩ :=
    _root_.Erdos599.Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
      old hzOld hzNeOldStart
  have huE : (u, front.finish) ∈ E := holdEdges huOld
  rcases splice.switchedEdge_head_after_incomingTail_cases
      state owner_eq same_tail huE hzParent hafterEq with
    hresidual | hforward
  · exfalso
    have hparent : state.parent ∈
        (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths := by
      simpa only [splitGroundedPopularAuxiliaryInput, limitWarp]
        using state.parent_mem
    obtain ⟨residualOwner, hresidualOwner, huResidualOwner⟩ :=
      hresidual.1.1
    have hzResidualOwner : front.finish ∈ residualOwner.support :=
      (residualOwner.edgeSet_subset_support_prod huResidualOwner).2
    have hownerParent : residualOwner = state.parent :=
      DWeb.IsWarp.eq_of_mem_support
        (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.disjoint
        hresidualOwner hparent hzResidualOwner hzParent
    have huParent : (u, front.finish) ∈ state.parent.edgeSet := by
      simpa only [hownerParent] using huResidualOwner
    have hfrontSub : front.IsSubpathOf state.parent := ⟨
      (segment.firstHit_support_subset old.support hm).trans hsegmentSupport,
      (segment.firstHit_edgeSet_subset old.support hm).trans hsegmentEdges⟩
    have huFront : (u, front.finish) ∈ front.edgeSet :=
      FinitePath.incoming_mem_of_isSubpathOf front state.parent hfrontSub
        front.finish_mem_support hzNeFrontStart huParent
    have huDrop : u ∈ front.walk.support.dropLast := by
      have huSupport : u ∈ front.support :=
        (front.edgeSet_subset_support_prod huFront).1
      have huNeLast : u ≠ front.walk.support.getLast
          front.walk.support_ne_nil := by
        simpa only [front.walk.getLast_support] using
          (Ne.symm (_root_.Erdos599.Alternating.Walk.finish_ne_edge_source
            front.walk front.isPath huFront))
      exact List.mem_dropLast_of_mem_of_ne_getLast huSupport huNeLast
    exact (segment.firstHit_no_mem_before old.support hm huDrop)
      ((old.edgeSet_subset_support_prod huOld).1)
  · exact ⟨u, front.finish, huOld, hzSegment, hzOld, hafter, hforward⟩

/-- Exact family exchange classified by the finite same-owner component
cluster.  The exchange either trades the first-hit sink itself, meets a
later component entered by another retained forward edge of the same owner,
or replaces a ray and strictly adds the failed endpoint to the reachable
sink frontier.  No arbitrary displaced sink remains unclassified. -/
theorem SplitGroundedFreshRelevantForwardFirstHit.exists_componentExchangeWarp_to_initialFinish_with_clusterUpdate
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (initial state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ClusterControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ClusterFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (X : L.SplitGroundedFreshRelevantForwardFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S)
      (ClusterSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) state splice)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
    (owner_eq : splice.contact.owner.1 = state.control.1)
    (same_parent : state.parent = initial.parent)
    (finish_beforeEq : GroundingCut.BeforeEq initial.parent
      state.rootPath.finish initial.rootPath.finish) :
    initial.parent ∈ GroundingSimultaneousDecode.exposedLadderPaths
        (L.splitGroundedPopularAuxiliaryInput hL.legal)
        (GroundingSimultaneousDecode.strongSelectedPath
          (ClusterIndexed (L := L) (hL := hL) (hground := hground)) S
          (ClusterControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (GroundingErasedDecode.chosenRequest splice.contact.owner.1)) ∧
      ∃ (segment : FinitePath Gamma.graph) (W : Set Gamma.DPath)
          (q : FinitePath Gamma.graph),
        segment.start = splice.incomingTail ∧
        segment.finish = initial.rootPath.finish ∧
        segment.support ⊆ initial.parent.support ∧
        segment.edgeSet ⊆ initial.parent.edgeSet ∧
        Gamma.IsWarp W ∧
        Gamma.initialSet W = ClusterSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S) ∧
        (Sum.inl q : Gamma.DPath) ∈ W ∧
        q.finish = initial.rootPath.finish ∧
        q.edgeSet ⊆ ClusterEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) ∪
          initial.parent.edgeSet ∧
        initial.rootPath.finish ∈ Gamma.terminalFrontier W ∧
        ((∃ (old : FinitePath Gamma.graph) (contact : V),
            contact ∈ old.support ∧ contact ∈ initial.parent.support ∧
            contact ∈ segment.support ∧
            GroundingCut.BeforeEq initial.parent splice.incomingTail contact ∧
            old.start ∈ ClusterSources
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∧
            old.edgeSet ⊆ ClusterEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∧
            old.finish = X.path.finish ∧
            Gamma.terminalFrontier W = insert initial.rootPath.finish
              (L.splitGroundedFreshReachableSinkBoundary
                (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S) \ {X.path.finish})) ∨
          (∃ (old : FinitePath Gamma.graph) (contact u z : V),
            contact ∈ old.support ∧ contact ∈ initial.parent.support ∧
            contact ∈ segment.support ∧
            GroundingCut.BeforeEq initial.parent splice.incomingTail contact ∧
            old.start ∈ ClusterSources
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∧
            old.edgeSet ⊆ ClusterEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∧
            old.finish ∈ L.splitGroundedFreshReachableSinkBoundary
              (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∧
            (u, z) ∈ old.edgeSet ∧ z ∈ segment.support ∧
            z ∈ old.support ∧
            GroundingCut.Before state.parent splice.incomingTail z ∧
            (u, z) ∈ retainedForwardEdgesAt
              (ClusterFrontier (L := L) (hL := hL) (S := S))
              (selectedErasedCompression
                (ClusterIndexed (L := L) (hL := hL)
                  (hground := hground)) S
                (ClusterControls (L := L) (hL := hL)
                  (hground := hground) (hnotFresh := hnotFresh) (S := S))
                (chosenRequest splice.contact.owner.1)).path ∧
            Gamma.terminalFrontier W = insert initial.rootPath.finish
              (L.splitGroundedFreshReachableSinkBoundary
                (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S) \ {old.finish})) ∨
          Gamma.terminalFrontier W = insert initial.rootPath.finish
            (L.splitGroundedFreshReachableSinkBoundary
              (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S))) := by
  obtain ⟨hexposed, segment, W, q, hsegmentStart, hsegmentFinish,
      hsegmentSupport, hsegmentEdges, hW, hWInitial, hqW, hqFinish,
      hqEdges, hqTerminal, hupdate⟩ :=
    X.exists_componentExchangeWarp_to_initialFinish_with_terminalUpdate
      hNoEnter initial state splice same_tail owner_eq same_parent
        finish_beforeEq
  refine ⟨hexposed, segment, W, q, hsegmentStart, hsegmentFinish,
    hsegmentSupport, hsegmentEdges, hW, hWInitial, hqW, hqFinish,
    hqEdges, hqTerminal, ?_⟩
  rcases hupdate with hfinite | hray
  · obtain ⟨old, contact, hcontactOld, hcontactParent, hcontactSegment,
      hcontactOrder, holdStart, holdEdges, holdFinish, hterminal⟩ := hfinite
    by_cases htailOld : splice.incomingTail ∈ old.support
    · left
      have holdFinishEq : old.finish = X.path.finish :=
        X.displacedComponent_finish_eq_of_tail_mem hNoEnter state splice
          same_tail old holdEdges holdFinish htailOld
      exact ⟨old, contact, hcontactOld, hcontactParent, hcontactSegment,
        hcontactOrder, holdStart, holdEdges, holdFinishEq, by
          simpa only [holdFinishEq] using hterminal⟩
    · right
      left
      have hsegmentSupportState : segment.support ⊆ state.parent.support := by
        simpa only [same_parent] using hsegmentSupport
      have hsegmentEdgesState : segment.edgeSet ⊆ state.parent.edgeSet := by
        simpa only [same_parent] using hsegmentEdges
      obtain ⟨u, z, huOld, hzSegment, hzOld, hzAfter, huForward⟩ :=
        splice.exists_sameOwnerForwardEntry_of_segment_meet_of_tail_not_mem
          hNoEnter state owner_eq same_tail segment old hsegmentStart
          hsegmentSupportState hsegmentEdgesState holdStart holdEdges
          ⟨contact, hcontactSegment, hcontactOld⟩ htailOld
      exact ⟨old, contact, u, z, hcontactOld, hcontactParent,
        hcontactSegment, hcontactOrder, holdStart, holdEdges, holdFinish,
        huOld, hzSegment, hzOld, hzAfter, huForward, hterminal⟩
  · exact Or.inr (Or.inr hray)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantForwardFirstHit.displacedComponent_finish_eq_of_tail_mem
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReducedForwardConflictSpliceData.exists_sameOwnerForwardEntry_of_segment_meet_of_tail_not_mem
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantForwardFirstHit.exists_componentExchangeWarp_to_initialFinish_with_clusterUpdate
