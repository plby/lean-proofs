/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantBackwardNormalization
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingBackwardDescent
import ErdosProblems.Erdos599.GroundingStoppedActiveControlPrefix
import ErdosProblems.Erdos599.BlueprintSplice

/-!
# Strict descent at a same-tail selected forward splice

A terminal same-tail forward conflict is not a static obstruction.  Its
incoming tail is strictly earlier than the deleted head on the same exposed
parent.  If that tail is rooted, the retained selected forward edge roots
its head.  Otherwise the initial parent prefix ending at the tail has its
own last deleted head, strictly earlier than the old one, and therefore
enters the already established well-founded native-frontier normalizer.

This is the concrete route/parent-order step used by the simultaneous
exchange.  It changes neither the stopping frontier nor the switched
relation.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev ForwardDescentIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev ForwardDescentControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev ForwardDescentRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev ForwardDescentFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev ForwardDescentEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
    (ForwardDescentControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (ForwardDescentFrontier (L := L) (hL := hL) (S := S))

private abbrev ForwardDescentSources : Set V :=
  Gamma.source \ {
    (ForwardDescentRecord (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)).record.initial}

/-- The actual progress made by a terminal same-tail forward splice.  A
rooted incoming tail immediately roots the selected forward head.  An
unrooted tail produces a strictly smaller state and invokes the existing
well-founded normalizer on that state. -/
theorem SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRooted_or_strictDescent
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1) :
    (∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        a splice.contact.forwardEdge.2) ∨
      ∃ next : L.SplitGroundedFreshRelevantBackwardState
          (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        next.parent = state.parent ∧
          GroundingCut.BeforeEq state.parent next.rootPath.finish
            state.rootPath.finish ∧
          GroundingCut.Before state.parent next.deleted.head
            state.deleted.head ∧
          next.Precedes state ∧
          L.SplitGroundedFreshRelevantBackwardNormalizationResult next := by
  by_cases htail : ∃ a ∈ ForwardDescentSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ ForwardDescentEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      a splice.incomingTail
  · left
    obtain ⟨a, ha, hareach⟩ := htail
    refine ⟨a, ha, hareach.tail ?_⟩
    apply activeRetainedForwardEdgesAt_subset_switched
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
      splice.contact.owner
    simpa only [same_tail] using splice.contact.retained
  · right
    have htailMem : splice.incomingTail ∈ state.rootPath.support :=
      (state.rootPath.edgeSet_subset_support_prod splice.incoming_mem).1
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix
        (.inl state.rootPath : Gamma.DPath) htailMem
    have hqRoot : ∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a q.start := by
      simpa only [hqStart, Path.initial] using state.rootPath_start_rooted
    have hqNot : ¬ ∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a q.finish := by
      simpa only [hqFinish] using htail
    let R := ForwardDescentRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)
    obtain ⟨D, hDnot⟩ :=
      R.exists_unrootedLastDeletedHead_sourceFirstTotal
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        q hqRoot hqNot
    have hparentInput : state.parent ∈
        (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths := by
      simpa only [splitGroundedPopularAuxiliaryInput, limitWarp]
        using state.parent_mem
    have hqParentSupport : q.support ⊆ state.parent.support :=
      hqSupport.trans state.rootPath_support
    have hqParentEdges : q.edgeSet ⊆ state.parent.edgeSet :=
      hqEdges.trans state.rootPath_edges
    let resolution := L.splitGroundedRelevantDeletedResolutionAt
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
      state.parent hparentInput q hqParentSupport hqParentEdges D
    let next : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) := {
      control := state.control
      parent := state.parent
      parent_mem := state.parent_mem
      parent_exposed := state.parent_exposed
      rootPath := q
      rootPath_start_rooted := hqRoot
      rootPath_finish_not_rooted := hqNot
      rootPath_support := hqParentSupport
      rootPath_edges := hqParentEdges
      deleted := D
      deleted_head_not_rooted := hDnot
      resolution := resolution }
    have hDmem : D.head ∈ q.support := D.head_mem_parent
    have hDtail : GroundingCut.BeforeEq state.parent D.head
        splice.incomingTail := by
      have hqSub : q.IsSubpathOf state.parent :=
        ⟨hqParentSupport, hqParentEdges⟩
      simpa only [hqFinish] using
        splitGroundedFreshAvoiding_finiteSubpath_mem_beforeEq_finish
          state.parent q hqSub hDmem
    have htailHead : GroundingCut.Before state.parent
        splice.incomingTail state.deleted.head := by
      have hedge : (splice.incomingTail, state.deleted.head) ∈
          state.parent.edgeSet := state.rootPath_edges splice.incoming_mem
      exact ⟨GroundingCut.beforeEq_of_mem_edgeSet hedge,
        GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet hedge⟩
    have hDHead : GroundingCut.Before state.parent D.head
        state.deleted.head :=
      splitGroundedFreshAvoiding_before_of_beforeEq_before
        state.parent hDtail htailHead
    have hnext : next.Precedes state := by
      exact Prod.Lex.right _
        (freshRelevantPathPosition_lt_of_before state.parent hDHead)
    have hfinish : GroundingCut.BeforeEq state.parent
        next.rootPath.finish state.rootPath.finish := by
      have hrootSub : state.rootPath.IsSubpathOf state.parent :=
        ⟨state.rootPath_support, state.rootPath_edges⟩
      have htailFinish :=
        splitGroundedFreshAvoiding_finiteSubpath_mem_beforeEq_finish
          state.parent state.rootPath hrootSub htailMem
      simpa only [next, hqFinish] using htailFinish
    exact ⟨next, rfl, hfinish, hDHead, hnext, next.normalize⟩

/-- A finite subpath of one forward link is retained once its initial vertex
is already reached from the link start and none of its edge tails lies in the
stopping frontier. -/
private theorem finiteSubpath_edges_retainedForwardAt
    (Q : Alternating.AltPath Gamma.graph)
    (T : Set V) (l : Alternating.Link Gamma.graph)
    (hl : l ∈ Q.links) (hldir : l.direction = .forward)
    (x : V)
    (hentry : Relation.ReflTransGen
      (retainedForwardLinkStepAt T l) l.path.start x)
    (q : FinitePath Gamma.graph) (hqStart : q.start = x)
    (hqEdges : q.edgeSet ⊆ l.path.edgeSet)
    (hnoTail : ∀ e ∈ q.edgeSet, e.1 ∉ T) :
    q.edgeSet ⊆ retainedForwardEdgesAt T Q := by
  intro e he
  have heTail : e.1 ∈ q.support :=
    (q.edgeSet_subset_support_prod he).1
  have hqReach : Relation.ReflTransGen
      (fun a b ↦ (a, b) ∈ q.edgeSet) q.start e.1 :=
    GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
      q (fun _ h ↦ h) heTail
  have hqStep : Relation.ReflTransGen
      (retainedForwardLinkStepAt T l) q.start e.1 := by
    apply Relation.ReflTransGen.mono
      (r := fun a b ↦ (a, b) ∈ q.edgeSet)
      (p := retainedForwardLinkStepAt T l)
    · intro a b hab
      exact ⟨hqEdges hab, hnoTail (a, b) hab⟩
    · exact hqReach
  refine ⟨l, hl, hldir, hqEdges he, hnoTail e he, ?_⟩
  have hqStep' : Relation.ReflTransGen
      (retainedForwardLinkStepAt T l) x e.1 := by
    simpa only [hqStart] using hqStep
  exact hentry.trans hqStep'

/-- A rooted start of one active forward link either reaches its finish, or
is honestly stopped at a rooted member of the native frontier. -/
private theorem activeForwardLink_startRooted_finish_or_boundary
    {A : Set V}
    (owner : ActiveControlRequestAt
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S)))
    (l : Alternating.Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)).path.links)
    (hldir : l.direction = .forward)
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a l.path.start) :
    (∃ b ∈ ForwardDescentFrontier
          (L := L) (hL := hL) (S := S),
        ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardDescentEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a b) ∨
      ∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ForwardDescentEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a l.path.finish := by
  let C := selectedErasedCompression
    (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
    (ForwardDescentControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (chosenRequest owner.1)
  by_cases hmeet : l.path.walk.Meets
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
  · obtain ⟨P⟩ := exists_activeControlAtStoppedPrefix
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) A owner
      l hl hldir hroot hmeet
    exact Or.inl ⟨P.vertex, P.vertex_mem, P.rooted⟩
  · have hnoTail : ∀ e ∈ l.path.edgeSet,
        e.1 ∉ ForwardDescentFrontier
          (L := L) (hL := hL) (S := S) := by
      intro e he heT
      apply hmeet
      exact ⟨e.1, (l.path.edgeSet_subset_support_prod he).1, heT⟩
    have hretained : l.path.edgeSet ⊆ retainedForwardEdgesAt
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) C.path :=
      finiteSubpath_edges_retainedForwardAt C.path
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        l hl hldir l.path.start .refl l.path rfl (fun _ h ↦ h) hnoTail
    have hswitched : l.path.edgeSet ⊆ ForwardDescentEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) :=
      hretained.trans
        (activeRetainedForwardEdgesAt_subset_switched
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) owner)
    have hreach :=
      GroundingRootedReachabilityWarp.finitePath_reaches_finish_of_mem_support
        l.path hswitched l.path.start_mem_support
    obtain ⟨a, ha, haStart⟩ := hroot
    exact Or.inr ⟨a, ha, haStart.trans hreach⟩

/-- Exact selected-link prefix retained by the route-order advance when its
next forward link first meets the native stopping frontier.  Both endpoint
roots use the same ambient source; this is the component-exchange datum
which the older coarse rooted-frontier alternative discarded. -/
structure SplitGroundedFreshRelevantForwardLinkFirstHit
    (A : Set V)
    (owner : ActiveControlRequestAt
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))) where
  link : Alternating.Link Gamma.graph
  link_mem : link ∈ (selectedErasedCompression
    (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
    (ForwardDescentControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (chosenRequest owner.1)).path.links
  link_forward : link.direction = .forward
  path : FinitePath Gamma.graph
  path_start : path.start = link.path.start
  finish_mem : path.finish ∈ ForwardDescentFrontier
    (L := L) (hL := hL) (S := S)
  path_edges : path.edgeSet ⊆ ForwardDescentEdges
    (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  no_frontier_before : ∀ e ∈ path.edgeSet,
    e.1 ∉ ForwardDescentFrontier (L := L) (hL := hL) (S := S)
  source : V
  source_mem : source ∈ A
  rooted_start : Relation.ReflTransGen
    (fun x y ↦ (x, y) ∈ ForwardDescentEdges
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)) source link.path.start
  rooted_finish : Relation.ReflTransGen
    (fun x y ↦ (x, y) ∈ ForwardDescentEdges
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)) source path.finish

/-- Same-source exact form of `activeForwardLink_startRooted_finish_or_boundary`.
The stopped branch keeps the literal selected-link first-hit segment. -/
private theorem activeForwardLink_startRooted_finish_or_boundary_exact
    {A : Set V}
    (owner : ActiveControlRequestAt
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S)))
    (l : Alternating.Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)).path.links)
    (hldir : l.direction = .forward)
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a l.path.start) :
    Nonempty (L.SplitGroundedFreshRelevantForwardLinkFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) A owner) ∨
      ∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ForwardDescentEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a l.path.finish := by
  by_cases hmeet : l.path.walk.Meets
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
  · let q := l.path.firstHit
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) hmeet
    have hqStart : q.start = l.path.start := rfl
    have hqFinish : q.finish ∈ ForwardDescentFrontier
        (L := L) (hL := hL) (S := S) :=
      l.path.firstHit_finish_mem _ hmeet
    have hqEdgesLink : q.edgeSet ⊆ l.path.edgeSet :=
      l.path.firstHit_edgeSet_subset _ hmeet
    have hnoTail : ∀ e ∈ q.edgeSet,
        e.1 ∉ ForwardDescentFrontier
          (L := L) (hL := hL) (S := S) := by
      intro e he
      exact l.path.firstHit_no_mem_before _ hmeet
        (Walk.edge_fst_mem_support_dropLast q.walk he)
    have hqRetained : q.edgeSet ⊆ retainedForwardEdgesAt
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        (selectedErasedCompression
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).path :=
      finiteSubpath_edges_retainedForwardAt
        (selectedErasedCompression
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).path
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        l hl hldir l.path.start .refl q hqStart hqEdgesLink hnoTail
    have hqSwitched : q.edgeSet ⊆ ForwardDescentEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) :=
      hqRetained.trans
        (activeRetainedForwardEdgesAt_subset_switched
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) owner)
    have hpathReach :=
      GroundingRootedReachabilityWarp.finitePath_reaches_finish_of_mem_support
        q hqSwitched q.start_mem_support
    obtain ⟨a, ha, haStart⟩ := hroot
    left
    refine ⟨{
      link := l
      link_mem := hl
      link_forward := hldir
      path := q
      path_start := hqStart
      finish_mem := hqFinish
      path_edges := hqSwitched
      no_frontier_before := hnoTail
      source := a
      source_mem := ha
      rooted_start := haStart
      rooted_finish := haStart.trans ?_ }⟩
    simpa only [hqStart] using hpathReach
  · right
    have hnoTail : ∀ e ∈ l.path.edgeSet,
        e.1 ∉ ForwardDescentFrontier
          (L := L) (hL := hL) (S := S) := by
      intro e he heT
      exact hmeet ⟨e.1, (l.path.edgeSet_subset_support_prod he).1, heT⟩
    have hretained : l.path.edgeSet ⊆ retainedForwardEdgesAt
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        (selectedErasedCompression
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).path :=
      finiteSubpath_edges_retainedForwardAt
        (selectedErasedCompression
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).path
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        l hl hldir l.path.start .refl l.path rfl (fun _ h ↦ h) hnoTail
    have hswitched : l.path.edgeSet ⊆ ForwardDescentEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) :=
      hretained.trans
        (activeRetainedForwardEdgesAt_subset_switched
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) owner)
    have hreach :=
      GroundingRootedReachabilityWarp.finitePath_reaches_finish_of_mem_support
        l.path hswitched l.path.start_mem_support
    obtain ⟨a, ha, haStart⟩ := hroot
    exact ⟨a, ha, haStart.trans hreach⟩

/-- Ordered compatibility makes the link positions of a finite alternating
trace injective. -/
private theorem finiteTrace_link_injective
    (Q : Alternating.FiniteTrace Gamma.graph) : Function.Injective Q.link := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hcompat := Q.compatible i j hlt
    rw [hij] at hcompat
    cases hd : (Q.link j).direction with
    | forward =>
        simp only [CompatibleInOrder, hd] at hcompat
        rcases hcompat (Q.link j).entry_mem_support
            (Q.link j).entry_mem_support with h | h
        · exact (Q.link j).entry_ne_exit h.2
        · exact (Q.link j).entry_ne_exit h.1
    | backward =>
        simp only [CompatibleInOrder, hd] at hcompat
        rcases hcompat (Q.link j).entry_mem_support
            (Q.link j).entry_mem_support with h | h
        · exact (Q.link j).entry_ne_exit h.2
        · exact (Q.link j).entry_ne_exit h.1
  · have hji : Q.link j = Q.link i := hij.symm
    have hcompat := Q.compatible j i hlt
    rw [hji] at hcompat
    cases hd : (Q.link i).direction with
    | forward =>
        simp only [CompatibleInOrder, hd] at hcompat
        rcases hcompat (Q.link i).entry_mem_support
            (Q.link i).entry_mem_support with h | h
        · exact (Q.link i).entry_ne_exit h.2
        · exact (Q.link i).entry_ne_exit h.1
    | backward =>
        simp only [CompatibleInOrder, hd] at hcompat
        rcases hcompat (Q.link i).entry_mem_support
            (Q.link i).entry_mem_support with h | h
        · exact (Q.link i).entry_ne_exit h.2
        · exact (Q.link i).entry_ne_exit h.1

/-- Exact first-hit data retained when a rooted selected forward-link head
reaches the native stopping frontier.  Unlike the coarse rooted-frontier
alternative, this record remembers the literal selected link and the
surviving head-to-frontier segment.  It is the path input needed for the
subsequent component exchange. -/
structure SplitGroundedFreshRelevantForwardFirstHit
    (A : Set V)
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted) where
  link : Alternating.Link Gamma.graph
  link_mem : link ∈ (selectedErasedCompression
    (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
    (ForwardDescentControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (chosenRequest splice.contact.owner.1)).path.links
  link_forward : link.direction = .forward
  conflict_edge_mem : splice.contact.forwardEdge ∈ link.path.edgeSet
  path : FinitePath Gamma.graph
  path_start : path.start = splice.contact.forwardEdge.2
  finish_mem : path.finish ∈ ForwardDescentFrontier
    (L := L) (hL := hL) (S := S)
  path_edges : path.edgeSet ⊆ ForwardDescentEdges
    (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  no_frontier_before : ∀ e ∈ path.edgeSet,
    e.1 ∉ ForwardDescentFrontier (L := L) (hL := hL) (S := S)
  source : V
  source_mem : source ∈ A
  rooted_start : Relation.ReflTransGen
    (fun x y ↦ (x, y) ∈ ForwardDescentEdges
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    source splice.contact.forwardEdge.2
  rooted_finish : Relation.ReflTransGen
    (fun x y ↦ (x, y) ∈ ForwardDescentEdges
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)) source path.finish

/-- Strengthened first-hit form of
`forwardSplice_headRoot_advances`.  The frontier alternative retains the
actual selected-link segment which produced the rooted frontier point; the
other alternative is unchanged. -/
theorem SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRoot_advances_exact
    {A : Set V}
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (hhead : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        a splice.contact.forwardEdge.2) :
    Nonempty (L.SplitGroundedFreshRelevantForwardFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) A state splice) ∨
      ∃ (l : Alternating.Link Gamma.graph),
        l ∈ (selectedErasedCompression
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest splice.contact.owner.1)).path.links ∧
        l.direction = .forward ∧
        splice.contact.forwardEdge ∈ l.path.edgeSet ∧
        ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardDescentEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a l.path.finish := by
  let Q := (selectedErasedCompression
    (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
    (ForwardDescentControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (chosenRequest splice.contact.owner.1)).path
  rcases splice.contact.retained with
    ⟨l, hl, hldir, hf, htailNot, hlinkTail⟩
  have hheadMem : splice.contact.forwardEdge.2 ∈ l.path.support :=
    (l.path.edgeSet_subset_support_prod hf).2
  have hlinkHead : Relation.ReflTransGen
      (retainedForwardLinkStepAt
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) l)
      l.path.start splice.contact.forwardEdge.2 :=
    hlinkTail.tail ⟨hf, htailNot⟩
  let suffix := l.path.suffixFrom splice.contact.forwardEdge.2 hheadMem
  by_cases hmeet : suffix.walk.Meets
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
  · let q := suffix.firstHit
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) hmeet
    have hqStart : q.start = splice.contact.forwardEdge.2 := by
      change suffix.start = splice.contact.forwardEdge.2
      exact l.path.suffixFrom_start _ _
    have hqFinish : q.finish ∈ ForwardDescentFrontier
        (L := L) (hL := hL) (S := S) :=
      suffix.firstHit_finish_mem _ hmeet
    have hqEdgesLink : q.edgeSet ⊆ l.path.edgeSet :=
      (suffix.firstHit_edgeSet_subset _ hmeet).trans
        (l.path.suffixFrom_edgeSet_subset _ hheadMem)
    have hnoTail : ∀ e ∈ q.edgeSet,
        e.1 ∉ ForwardDescentFrontier
          (L := L) (hL := hL) (S := S) := by
      intro e he
      exact suffix.firstHit_no_mem_before _ hmeet
        (Walk.edge_fst_mem_support_dropLast q.walk he)
    have hqRetained : q.edgeSet ⊆ retainedForwardEdgesAt
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) Q :=
      finiteSubpath_edges_retainedForwardAt Q
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        l hl hldir splice.contact.forwardEdge.2 hlinkHead q hqStart
          hqEdgesLink hnoTail
    have hqSwitched : q.edgeSet ⊆ ForwardDescentEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) :=
      hqRetained.trans
        (activeRetainedForwardEdgesAt_subset_switched
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
          splice.contact.owner)
    have hqReach :=
      GroundingRootedReachabilityWarp.finitePath_reaches_finish_of_mem_support
        q hqSwitched q.start_mem_support
    obtain ⟨a, ha, haHead⟩ := hhead
    left
    refine ⟨{
      link := l
      link_mem := hl
      link_forward := hldir
      conflict_edge_mem := hf
      path := q
      path_start := hqStart
      finish_mem := hqFinish
      path_edges := hqSwitched
      no_frontier_before := hnoTail
      source := a
      source_mem := ha
      rooted_start := haHead
      rooted_finish := haHead.trans ?_ }⟩
    simpa only [hqStart] using hqReach
  · have hnoTail : ∀ e ∈ suffix.edgeSet,
        e.1 ∉ ForwardDescentFrontier
          (L := L) (hL := hL) (S := S) := by
      intro e he heT
      apply hmeet
      exact ⟨e.1, (suffix.edgeSet_subset_support_prod he).1, heT⟩
    have hsuffixStart : suffix.start = splice.contact.forwardEdge.2 :=
      l.path.suffixFrom_start _ _
    have hsuffixEdges : suffix.edgeSet ⊆ l.path.edgeSet :=
      l.path.suffixFrom_edgeSet_subset _ hheadMem
    have hsuffixRetained : suffix.edgeSet ⊆ retainedForwardEdgesAt
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) Q :=
      finiteSubpath_edges_retainedForwardAt Q
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        l hl hldir splice.contact.forwardEdge.2 hlinkHead suffix
          hsuffixStart hsuffixEdges hnoTail
    have hsuffixSwitched : suffix.edgeSet ⊆ ForwardDescentEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) :=
      hsuffixRetained.trans
        (activeRetainedForwardEdgesAt_subset_switched
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
          splice.contact.owner)
    have hsuffixReach :=
      GroundingRootedReachabilityWarp.finitePath_reaches_finish_of_mem_support
        suffix hsuffixSwitched suffix.start_mem_support
    obtain ⟨a, ha, haHead⟩ := hhead
    right
    refine ⟨l, hl, hldir, hf, a, ha, haHead.trans ?_⟩
    have hsuffixFinish : suffix.finish = l.path.finish :=
      l.path.suffixFrom_finish _ _
    simpa only [hsuffixStart, hsuffixFinish] using hsuffixReach

/-- In the no-source-entry setting, the exact first-hit segment pulls its
source root back to the tail of the conflicting retained forward edge.
Indeed the tail and the source both reach the same first frontier point in
the locally left-unique switched relation.  Their two ancestor chains are
therefore comparable; the alternative in which the tail reaches the source
is trivial because no nonempty switched path can enter an ambient source.

This is the genuine incidence statement needed before exchanging the
selected departure for the old parent suffix. -/
theorem SplitGroundedFreshRelevantForwardFirstHit.conflictTail_rooted
    {A : Set V} (hA : A ⊆ Gamma.source)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (X : L.SplitGroundedFreshRelevantForwardFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) A state splice)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1) :
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ ForwardDescentEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      X.source splice.incomingTail := by
  let U := ForwardDescentIndexed (L := L) (hL := hL)
    (hground := hground)
  let K := ForwardDescentControls (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  let T := ForwardDescentFrontier (L := L) (hL := hL) (S := S)
  let E := ForwardDescentEdges (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  have hforwardE : splice.contact.forwardEdge ∈ E := by
    exact activeRetainedForwardEdgesAt_subset_switched U S K T
      splice.contact.owner splice.contact.retained
  have hheadFinish : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E)
      splice.contact.forwardEdge.2 X.path.finish := by
    have hreach :=
      GroundingRootedReachabilityWarp.finitePath_reaches_finish_of_mem_support
        X.path X.path_edges X.path.start_mem_support
    simpa only [E, X.path_start] using hreach
  have htailFinish : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E)
      splice.incomingTail X.path.finish := by
    rw [same_tail]
    have hsingle : Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ E)
        splice.contact.forwardEdge.1 splice.contact.forwardEdge.2 :=
      Relation.ReflTransGen.single (r := fun x y ↦ (x, y) ∈ E)
        hforwardE
    exact hsingle.trans hheadFinish
  have hleft : Relator.LeftUnique (fun x y ↦ (x, y) ∈ E) :=
    (GroundingErasedForwardConflict.erasedSelectedSwitchedEdgesAt_biUnique
      U S K T
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)).1
  have hright : Relator.RightUnique (fun x y ↦ (y, x) ∈ E) := by
    intro z y w hzy hzw
    exact hleft hzy hzw
  have htotal := Relation.ReflTransGen.total_of_right_unique hright
    (GroundingRootedReachabilityWarp.reflTransGen_reverse X.rooted_finish)
    (GroundingRootedReachabilityWarp.reflTransGen_reverse htailFinish)
  rcases htotal with hat | hta
  · have htailA : Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ E) splice.incomingTail X.source :=
      GroundingRootedReachabilityWarp.reflTransGen_reverse hat
    have heq : splice.incomingTail = X.source := by
      rcases htailA.cases_tail with heq | ⟨z, _hz, hza⟩
      · exact heq.symm
      · exact False.elim (hNoEnter
          (erasedSelectedSwitchedEdgesAt_subset_adj U S K T hza)
          (hA X.source_mem))
    rw [heq]
  · exact GroundingRootedReachabilityWarp.reflTransGen_reverse hta

/-- The exact first-hit conflict has a literal finite component exchange.
The selected switched relation reaches the old incoming tail from the same
ambient source as the first-hit path.  Normalize that source-to-tail path at
its final contact with the remaining old-parent suffix and append the suffix
from that contact.  The result is a simple source-to-original-finish path;
its edges are precisely switched edges followed by old-parent edges.

This deliberately does not claim that the old incoming edge belongs to the
unchanged switched relation.  It is the positive path which replaces the
old component in the family-level simultaneous exchange. -/
theorem SplitGroundedFreshRelevantForwardFirstHit.exists_source_to_parent_finish_exchangePath
    {A : Set V} (hA : A ⊆ Gamma.source)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (X : L.SplitGroundedFreshRelevantForwardFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) A state splice)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1) :
    ∃ q : FinitePath Gamma.graph,
      q.start = X.source ∧ q.finish = state.rootPath.finish ∧
        q.edgeSet ⊆
          ForwardDescentEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∪
            state.rootPath.edgeSet := by
  let U := ForwardDescentIndexed (L := L) (hL := hL)
    (hground := hground)
  let K := ForwardDescentControls (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  let T := ForwardDescentFrontier (L := L) (hL := hL) (S := S)
  let E := ForwardDescentEdges (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  have htailRoot : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) X.source splice.incomingTail := by
    exact X.conflictTail_rooted hA hNoEnter state splice same_tail
  obtain ⟨P⟩ :=
    GroundingRootedReachabilityWarp.exists_rootedPath_of_reflTransGen
      (Gamma := Gamma)
      (erasedSelectedSwitchedEdgesAt_subset_adj U S K T)
      (A := ({X.source} : Set V))
      ⟨X.source, Set.mem_singleton X.source, htailRoot⟩
  have hPStart : P.path.start = X.source :=
    Set.mem_singleton_iff.mp P.start_mem
  have htailParent : splice.incomingTail ∈ state.rootPath.support :=
    (state.rootPath.edgeSet_subset_support_prod splice.incoming_mem).1
  let oldSuffix := state.rootPath.suffixFrom splice.incomingTail htailParent
  have htailSuffix : splice.incomingTail ∈ oldSuffix.support := by
    have h := oldSuffix.start_mem_support
    simpa only [oldSuffix, FinitePath.suffixFrom_start] using h
  have htailP : splice.incomingTail ∈ P.path.support := by
    have finish_mem_of_finish_eq (p : FinitePath Gamma.graph) (x : V)
        (hpx : p.finish = x) : x ∈ p.support := by
      subst x
      exact p.finish_mem_support
    exact finish_mem_of_finish_eq P.path splice.incomingTail P.finish_eq
  let hmeet : oldSuffix.walk.Meets P.path.support :=
    ⟨splice.incomingTail, htailSuffix, htailP⟩
  let tail := oldSuffix.lastHit P.path.support hmeet
  have htailStart : tail.start ∈ P.path.support :=
    oldSuffix.lastHit_start_mem P.path.support hmeet
  obtain ⟨front, hfrontStart, hfrontFinish, hfrontSupport, hfrontEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix
      (.inl P.path : Gamma.DPath) htailStart
  have hinter : front.support ∩ tail.support ⊆ {front.finish} := by
    intro z hz
    by_cases hzeq : z = tail.start
    · exact Set.mem_singleton_iff.mpr (hzeq.trans hfrontFinish.symm)
    · have hsupport : tail.walk.support =
          tail.start :: tail.walk.support.tail := by
        have h := (List.cons_head_tail tail.walk.support_ne_nil).symm
        simpa only [tail.walk.head_support] using h
      have hzTail : z ∈ tail.walk.support.tail := by
        have hzSupport : z ∈ tail.walk.support := hz.2
        rw [hsupport] at hzSupport
        rcases List.mem_cons.mp hzSupport with hzStart | hzTail
        · exact False.elim (hzeq hzStart)
        · exact hzTail
      have hzNotP : z ∉ P.path.support :=
        oldSuffix.lastHit_no_mem_after P.path.support hmeet hzTail
      exact False.elim (hzNotP (hfrontSupport hz.1))
  let q := front.appendFinite tail hfrontFinish.symm hinter
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa only [q, FinitePath.appendFinite_start, hfrontStart, hPStart]
  · have htailFinish : tail.finish = state.rootPath.finish := by
      calc
        tail.finish = oldSuffix.finish := rfl
        _ = state.rootPath.finish :=
          state.rootPath.suffixFrom_finish splice.incomingTail htailParent
    simpa only [q, FinitePath.appendFinite_finish, htailFinish]
  · rw [show q.edgeSet = front.edgeSet ∪ tail.edgeSet by
      exact Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite
        front tail hfrontFinish.symm hinter]
    intro e he
    rcases he with heFront | heTail
    · exact Or.inl (P.edgeSet_subset (hfrontEdges heFront))
    · exact Or.inr ((oldSuffix.lastHit_edgeSet_subset
        P.path.support hmeet heTail) |> (state.rootPath.suffixFrom_edgeSet_subset
          splice.incomingTail htailParent))

/-- Starting at the rooted head of the retained forward edge in a
same-tail splice, the construction makes genuine progress along that same
forward link.  It either reaches the first actual stopping-frontier vertex,
or reaches the ambient finish of the link.  All edges in the witness lie in
the unchanged canonical switched relation. -/
theorem SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRoot_advances
    {A : Set V}
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (hhead : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        a splice.contact.forwardEdge.2) :
    (∃ b ∈ ForwardDescentFrontier
          (L := L) (hL := hL) (S := S),
        ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardDescentEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a b) ∨
      ∃ (l : Alternating.Link Gamma.graph),
        l ∈ (selectedErasedCompression
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest splice.contact.owner.1)).path.links ∧
        l.direction = .forward ∧
        splice.contact.forwardEdge ∈ l.path.edgeSet ∧
        ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardDescentEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a l.path.finish := by
  let Q := (selectedErasedCompression
    (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
    (ForwardDescentControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (chosenRequest splice.contact.owner.1)).path
  rcases splice.contact.retained with
    ⟨l, hl, hldir, hf, htailNot, hlinkTail⟩
  have hheadMem : splice.contact.forwardEdge.2 ∈ l.path.support :=
    (l.path.edgeSet_subset_support_prod hf).2
  have hlinkHead : Relation.ReflTransGen
      (retainedForwardLinkStepAt
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) l)
      l.path.start splice.contact.forwardEdge.2 :=
    hlinkTail.tail ⟨hf, htailNot⟩
  let suffix := l.path.suffixFrom splice.contact.forwardEdge.2 hheadMem
  by_cases hmeet : suffix.walk.Meets
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
  · let q := suffix.firstHit
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) hmeet
    have hqStart : q.start = splice.contact.forwardEdge.2 := by
      change suffix.start = splice.contact.forwardEdge.2
      exact l.path.suffixFrom_start _ _
    have hqFinish : q.finish ∈ ForwardDescentFrontier
        (L := L) (hL := hL) (S := S) :=
      suffix.firstHit_finish_mem _ hmeet
    have hqEdgesLink : q.edgeSet ⊆ l.path.edgeSet :=
      (suffix.firstHit_edgeSet_subset _ hmeet).trans
        (l.path.suffixFrom_edgeSet_subset _ hheadMem)
    have hnoTail : ∀ e ∈ q.edgeSet,
        e.1 ∉ ForwardDescentFrontier
          (L := L) (hL := hL) (S := S) := by
      intro e he
      exact suffix.firstHit_no_mem_before _ hmeet
        (Walk.edge_fst_mem_support_dropLast q.walk he)
    have hqRetained : q.edgeSet ⊆ retainedForwardEdgesAt
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) Q :=
      finiteSubpath_edges_retainedForwardAt Q
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        l hl hldir splice.contact.forwardEdge.2 hlinkHead q hqStart
          hqEdgesLink hnoTail
    have hqSwitched : q.edgeSet ⊆ ForwardDescentEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) :=
      hqRetained.trans
        (activeRetainedForwardEdgesAt_subset_switched
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
          splice.contact.owner)
    have hqReach :=
      GroundingRootedReachabilityWarp.finitePath_reaches_finish_of_mem_support
        q hqSwitched q.start_mem_support
    obtain ⟨a, ha, haHead⟩ := hhead
    left
    refine ⟨q.finish, hqFinish, a, ha, haHead.trans ?_⟩
    simpa only [hqStart] using hqReach
  · have hnoTail : ∀ e ∈ suffix.edgeSet,
        e.1 ∉ ForwardDescentFrontier
          (L := L) (hL := hL) (S := S) := by
      intro e he heT
      apply hmeet
      exact ⟨e.1, (suffix.edgeSet_subset_support_prod he).1, heT⟩
    have hsuffixStart : suffix.start = splice.contact.forwardEdge.2 :=
      l.path.suffixFrom_start _ _
    have hsuffixEdges : suffix.edgeSet ⊆ l.path.edgeSet :=
      l.path.suffixFrom_edgeSet_subset _ hheadMem
    have hsuffixRetained : suffix.edgeSet ⊆ retainedForwardEdgesAt
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S)) Q :=
      finiteSubpath_edges_retainedForwardAt Q
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        l hl hldir splice.contact.forwardEdge.2 hlinkHead suffix
          hsuffixStart hsuffixEdges hnoTail
    have hsuffixSwitched : suffix.edgeSet ⊆ ForwardDescentEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) :=
      hsuffixRetained.trans
        (activeRetainedForwardEdgesAt_subset_switched
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
          splice.contact.owner)
    have hsuffixReach :=
      GroundingRootedReachabilityWarp.finitePath_reaches_finish_of_mem_support
        suffix hsuffixSwitched suffix.start_mem_support
    obtain ⟨a, ha, haHead⟩ := hhead
    right
    refine ⟨l, hl, hldir, hf, a, ha, haHead.trans ?_⟩
    have hsuffixFinish : suffix.finish = l.path.finish :=
      l.path.suffixFrom_finish _ _
    simpa only [hsuffixStart, hsuffixFinish] using hsuffixReach

/-- A rooted finish of a selected forward link advances to the end of the
finite selected route unless it encounters the native frontier.  The only
other possibility is the ambient start of a *strictly later* backward link,
which is returned with its concrete limiting-ladder owner and an unrooted
certificate.  This is the finite route-order descent complementary to the
parent-position descent above. -/
theorem splitGroundedFreshRelevant_forwardLinkFinish_advances
    {A : Set V}
    (owner : ActiveControlRequestAt
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S)))
    (l : Alternating.Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)).path.links)
    (hldir : l.direction = .forward)
    (hfinishRoot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a l.path.finish) :
    (∃ b ∈ ForwardDescentFrontier
          (L := L) (hL := hL) (S := S),
        ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardDescentEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a b) ∨
      (∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ForwardDescentEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          a (requestExit (chosenRequest owner.1))) ∨
      ∃ (Q : Alternating.FiniteTrace Gamma.graph)
          (i j : Fin (Q.lastIndex + 1))
          (b : Alternating.Link Gamma.graph) (parent : Gamma.DPath),
        (selectedErasedCompression
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).path = .finite Q ∧
        Q.link i = l ∧ Q.link j = b ∧ i < j ∧
        b.direction = .backward ∧
        parent ∈ (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths ∧
        b.path.IsSubpathOf parent ∧
        ¬ ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardDescentEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a b.path.start := by
  let C := selectedErasedCompression
    (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
    (ForwardDescentControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (chosenRequest owner.1)
  have hback : BackwardLinksOn
      (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths C.path :=
    selectedErasedCompression_backwardLinksOn
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)
  cases hpath : C.path with
  | trivial v =>
      have : l ∈ (∅ : Set (Alternating.Link Gamma.graph)) := by
        simpa only [C, hpath, AltPath.links] using hl
      exact False.elim (by simpa using this)
  | infinite Q =>
      have hfalse : (none : Option V) =
          some (requestExit (chosenRequest owner.1)) := by
        simpa only [C, hpath, AltPath.terminal?] using C.terminal_eq
      cases hfalse
  | finite Q =>
      have hlQ : l ∈ (AltPath.finite Q).links := by
        simpa only [C, hpath] using hl
      obtain ⟨i, hiLink⟩ := hlQ
      have hiDir : (Q.link i).direction = .forward := by
        simpa only [hiLink] using hldir
      have hterminal : Q.terminal = requestExit (chosenRequest owner.1) := by
        exact Option.some.inj (by
          simpa only [C, hpath, AltPath.terminal?] using C.terminal_eq)
      by_cases hiLast : i.1 = Q.lastIndex
      · have hi : i = ⟨Q.lastIndex, Nat.lt_succ_self _⟩ := by
          apply Fin.ext
          exact hiLast
        have hlLast : l = Q.lastLink := by
          rw [← hiLink, hi]
          rfl
        have hlastDir' : Q.lastLink.direction = .forward := by
          rw [← hlLast]
          exact hldir
        have hfinishEq : l.path.finish = Q.terminal := by
          rw [hlLast]
          simp only [FiniteTrace.terminal, Link.exit, hlastDir']
        right
        left
        simpa only [hfinishEq, hterminal] using hfinishRoot
      · have hiLt : i.1 < Q.lastIndex := by omega
        cases hlastDir : Q.lastLink.direction with
        | backward =>
            let j : Fin (Q.lastIndex + 1) :=
              ⟨Q.lastIndex, Nat.lt_succ_self _⟩
            have hjDir : (Q.link j).direction = .backward := by
              simpa only [j, FiniteTrace.lastLink] using hlastDir
            have hjMem : Q.link j ∈ C.path.links := by
              rw [hpath]
              exact ⟨j, rfl⟩
            obtain ⟨parent, hparent, hsub⟩ :=
              hback (Q.link j) hjMem hjDir
            by_cases hjRoot : ∃ a ∈ A,
                Relation.ReflTransGen
                  (fun x y ↦ (x, y) ∈ ForwardDescentEdges
                    (L := L) (hL := hL) (hground := hground)
                    (hnotFresh := hnotFresh) (S := S))
                  a (Q.link j).path.start
            · right
              left
              have hstartEq : (Q.link j).path.start = Q.terminal := by
                change (Q.link j).path.start = Q.lastLink.exit
                rw [show Q.link j = Q.lastLink by rfl]
                simp only [Link.exit, hlastDir]
              simpa only [hstartEq, hterminal] using hjRoot
            · right
              right
              exact ⟨Q, i, j, Q.link j, parent, by simpa only [C] using hpath,
                hiLink, rfl, (by show i.1 < j.1; simpa only [j] using hiLt), hjDir,
                hparent, hsub, hjRoot⟩
        | forward =>
            cases hlastIndex : Q.lastIndex with
            | zero => exact False.elim (hiLast (by omega))
            | succ n =>
                let pred : Fin (Q.lastIndex + 1) :=
                  ⟨n, by simp only [hlastIndex]; omega⟩
                let last : Fin (Q.lastIndex + 1) :=
                  ⟨n + 1, by simp only [hlastIndex]; omega⟩
                have hlastEq : Q.link last = Q.lastLink := by
                  apply congrArg Q.link
                  apply Fin.ext
                  simp only [last, FiniteTrace.lastLink, hlastIndex]
                have hlastDir' : (Q.link last).direction = .forward := by
                  rw [hlastEq]
                  exact hlastDir
                have hpredDir : (Q.link pred).direction = .backward := by
                  let p : Fin Q.lastIndex := ⟨n, by
                    rw [hlastIndex]
                    exact Nat.lt_succ_self n⟩
                  have halt := Q.alternates p
                  have hpredEq : Fin.castSucc p = pred := by
                    apply Fin.ext
                    rfl
                  have hsuccEq : p.succ = last := by
                    apply Fin.ext
                    rfl
                  rw [hsuccEq, hlastDir'] at halt
                  rw [hpredEq] at halt
                  cases hp : (Q.link pred).direction with
                  | forward => exact False.elim (halt hp)
                  | backward => rfl
                have hpredMem : Q.link pred ∈ C.path.links := by
                  rw [hpath]
                  exact ⟨pred, rfl⟩
                obtain ⟨parent, hparent, hsub⟩ :=
                  hback (Q.link pred) hpredMem hpredDir
                by_cases hpredRoot : ∃ a ∈ A,
                    Relation.ReflTransGen
                      (fun x y ↦ (x, y) ∈ ForwardDescentEdges
                        (L := L) (hL := hL) (hground := hground)
                        (hnotFresh := hnotFresh) (S := S))
                      a (Q.link pred).path.start
                · have hjoin : (Q.link pred).path.start =
                      (Q.link last).path.start := by
                    let p : Fin Q.lastIndex :=
                      ⟨n, by
                        rw [hlastIndex]
                        exact Nat.lt_succ_self n⟩
                    have hj := Q.joins p
                    have hpredEq : Fin.castSucc p = pred := by
                      apply Fin.ext
                      rfl
                    have hlastEq' : p.succ = last := by
                      apply Fin.ext
                      rfl
                    rw [hpredEq, hlastEq'] at hj
                    simpa only [Link.exit, hpredDir, Link.entry, hlastDir']
                      using hj
                  have hlastRoot : ∃ a ∈ A,
                      Relation.ReflTransGen
                        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
                          (L := L) (hL := hL) (hground := hground)
                          (hnotFresh := hnotFresh) (S := S))
                        a (Q.link last).path.start := by
                    simpa only [hjoin] using hpredRoot
                  rcases activeForwardLink_startRooted_finish_or_boundary
                      (L := L) (hL := hL) (hground := hground)
                      (hnotFresh := hnotFresh) (S := S) owner
                      (Q.link last) (by simpa only [C, hpath] using
                        (show Q.link last ∈ (AltPath.finite Q).links from
                          ⟨last, rfl⟩)) hlastDir' hlastRoot with
                    hboundary | hfinish
                  · exact Or.inl hboundary
                  · right
                    left
                    have hfinishEq : (Q.link last).path.finish =
                        Q.terminal := by
                      rw [hlastEq]
                      simp only [FiniteTrace.terminal, Link.exit, hlastDir]
                    simpa only [hfinishEq, hterminal] using hfinish
                · have hiPred : i.1 < pred.1 := by
                    have hiLe : i.1 ≤ n := by
                      omega
                    have hiNe : i.1 ≠ n := by
                      intro heq
                      have hiEq : i = pred := by
                        apply Fin.ext
                        exact heq
                      have : (Q.link pred).direction = .forward := by
                        rw [← hiEq]
                        exact hiDir
                      rw [hpredDir] at this
                      contradiction
                    simpa only [pred] using lt_of_le_of_ne hiLe hiNe
                  right
                  right
                  exact ⟨Q, i, pred, Q.link pred, parent,
                    by simpa only [C] using hpath, hiLink, rfl,
                    hiPred, hpredDir, hparent, hsub, hpredRoot⟩

/-- Exact route-order form of `splitGroundedFreshRelevant_forwardLinkFinish_advances`.
The frontier branch retains the selected last-forward-link first-hit path
and its common source, instead of returning only a detached rooted point. -/
theorem splitGroundedFreshRelevant_forwardLinkFinish_advances_exact
    {A : Set V}
    (owner : ActiveControlRequestAt
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S)))
    (l : Alternating.Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)).path.links)
    (hldir : l.direction = .forward)
    (hfinishRoot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a l.path.finish) :
    Nonempty (L.SplitGroundedFreshRelevantForwardLinkFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) A owner) ∨
      (∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ForwardDescentEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          a (requestExit (chosenRequest owner.1))) ∨
      ∃ (Q : Alternating.FiniteTrace Gamma.graph)
          (i j : Fin (Q.lastIndex + 1))
          (b : Alternating.Link Gamma.graph) (parent : Gamma.DPath),
        (selectedErasedCompression
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).path = .finite Q ∧
        Q.link i = l ∧ Q.link j = b ∧ i < j ∧
        b.direction = .backward ∧
        parent ∈ (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths ∧
        b.path.IsSubpathOf parent ∧
        ¬ ∃ a ∈ A,
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardDescentEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a b.path.start := by
  let C := selectedErasedCompression
    (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
    (ForwardDescentControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (chosenRequest owner.1)
  have hback : BackwardLinksOn
      (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths C.path :=
    selectedErasedCompression_backwardLinksOn
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)
  cases hpath : C.path with
  | trivial v =>
      have : l ∈ (∅ : Set (Alternating.Link Gamma.graph)) := by
        simpa only [C, hpath, AltPath.links] using hl
      exact False.elim (by simpa using this)
  | infinite Q =>
      have hfalse : (none : Option V) =
          some (requestExit (chosenRequest owner.1)) := by
        simpa only [C, hpath, AltPath.terminal?] using C.terminal_eq
      cases hfalse
  | finite Q =>
      have hlQ : l ∈ (AltPath.finite Q).links := by
        simpa only [C, hpath] using hl
      obtain ⟨i, hiLink⟩ := hlQ
      have hiDir : (Q.link i).direction = .forward := by
        simpa only [hiLink] using hldir
      have hterminal : Q.terminal = requestExit (chosenRequest owner.1) := by
        exact Option.some.inj (by
          simpa only [C, hpath, AltPath.terminal?] using C.terminal_eq)
      by_cases hiLast : i.1 = Q.lastIndex
      · have hi : i = ⟨Q.lastIndex, Nat.lt_succ_self _⟩ := by
          apply Fin.ext
          exact hiLast
        have hlLast : l = Q.lastLink := by
          rw [← hiLink, hi]
          rfl
        have hlastDir' : Q.lastLink.direction = .forward := by
          rw [← hlLast]
          exact hldir
        have hfinishEq : l.path.finish = Q.terminal := by
          rw [hlLast]
          simp only [FiniteTrace.terminal, Link.exit, hlastDir']
        right
        left
        simpa only [hfinishEq, hterminal] using hfinishRoot
      · have hiLt : i.1 < Q.lastIndex := by omega
        cases hlastDir : Q.lastLink.direction with
        | backward =>
            let j : Fin (Q.lastIndex + 1) :=
              ⟨Q.lastIndex, Nat.lt_succ_self _⟩
            have hjDir : (Q.link j).direction = .backward := by
              simpa only [j, FiniteTrace.lastLink] using hlastDir
            have hjMem : Q.link j ∈ C.path.links := by
              rw [hpath]
              exact ⟨j, rfl⟩
            obtain ⟨parent, hparent, hsub⟩ :=
              hback (Q.link j) hjMem hjDir
            by_cases hjRoot : ∃ a ∈ A,
                Relation.ReflTransGen
                  (fun x y ↦ (x, y) ∈ ForwardDescentEdges
                    (L := L) (hL := hL) (hground := hground)
                    (hnotFresh := hnotFresh) (S := S))
                  a (Q.link j).path.start
            · right
              left
              have hstartEq : (Q.link j).path.start = Q.terminal := by
                change (Q.link j).path.start = Q.lastLink.exit
                rw [show Q.link j = Q.lastLink by rfl]
                simp only [Link.exit, hlastDir]
              simpa only [hstartEq, hterminal] using hjRoot
            · right
              right
              exact ⟨Q, i, j, Q.link j, parent, by simpa only [C] using hpath,
                hiLink, rfl, (by show i.1 < j.1; simpa only [j] using hiLt), hjDir,
                hparent, hsub, hjRoot⟩
        | forward =>
            cases hlastIndex : Q.lastIndex with
            | zero => exact False.elim (hiLast (by omega))
            | succ n =>
                let pred : Fin (Q.lastIndex + 1) :=
                  ⟨n, by simp only [hlastIndex]; omega⟩
                let last : Fin (Q.lastIndex + 1) :=
                  ⟨n + 1, by simp only [hlastIndex]; omega⟩
                have hlastEq : Q.link last = Q.lastLink := by
                  apply congrArg Q.link
                  apply Fin.ext
                  simp only [last, FiniteTrace.lastLink, hlastIndex]
                have hlastDir' : (Q.link last).direction = .forward := by
                  rw [hlastEq]
                  exact hlastDir
                have hpredDir : (Q.link pred).direction = .backward := by
                  let p : Fin Q.lastIndex := ⟨n, by
                    rw [hlastIndex]
                    exact Nat.lt_succ_self n⟩
                  have halt := Q.alternates p
                  have hpredEq : Fin.castSucc p = pred := by
                    apply Fin.ext
                    rfl
                  have hsuccEq : p.succ = last := by
                    apply Fin.ext
                    rfl
                  rw [hsuccEq, hlastDir'] at halt
                  rw [hpredEq] at halt
                  cases hp : (Q.link pred).direction with
                  | forward => exact False.elim (halt hp)
                  | backward => rfl
                have hpredMem : Q.link pred ∈ C.path.links := by
                  rw [hpath]
                  exact ⟨pred, rfl⟩
                obtain ⟨parent, hparent, hsub⟩ :=
                  hback (Q.link pred) hpredMem hpredDir
                by_cases hpredRoot : ∃ a ∈ A,
                    Relation.ReflTransGen
                      (fun x y ↦ (x, y) ∈ ForwardDescentEdges
                        (L := L) (hL := hL) (hground := hground)
                        (hnotFresh := hnotFresh) (S := S))
                      a (Q.link pred).path.start
                · have hjoin : (Q.link pred).path.start =
                      (Q.link last).path.start := by
                    let p : Fin Q.lastIndex :=
                      ⟨n, by
                        rw [hlastIndex]
                        exact Nat.lt_succ_self n⟩
                    have hj := Q.joins p
                    have hpredEq : Fin.castSucc p = pred := by
                      apply Fin.ext
                      rfl
                    have hlastEq' : p.succ = last := by
                      apply Fin.ext
                      rfl
                    rw [hpredEq, hlastEq'] at hj
                    simpa only [Link.exit, hpredDir, Link.entry, hlastDir']
                      using hj
                  have hlastRoot : ∃ a ∈ A,
                      Relation.ReflTransGen
                        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
                          (L := L) (hL := hL) (hground := hground)
                          (hnotFresh := hnotFresh) (S := S))
                        a (Q.link last).path.start := by
                    simpa only [hjoin] using hpredRoot
                  rcases activeForwardLink_startRooted_finish_or_boundary_exact
                      (L := L) (hL := hL) (hground := hground)
                      (hnotFresh := hnotFresh) (S := S) owner
                      (Q.link last) (by simpa only [C, hpath] using
                        (show Q.link last ∈ (AltPath.finite Q).links from
                          ⟨last, rfl⟩)) hlastDir' hlastRoot with
                    hboundary | hfinish
                  · exact Or.inl hboundary
                  · right
                    left
                    have hfinishEq : (Q.link last).path.finish =
                        Q.terminal := by
                      rw [hlastEq]
                      simp only [FiniteTrace.terminal, Link.exit, hlastDir]
                    simpa only [hfinishEq, hterminal] using hfinish
                · have hiPred : i.1 < pred.1 := by
                    have hiLe : i.1 ≤ n := by
                      omega
                    have hiNe : i.1 ≠ n := by
                      intro heq
                      have hiEq : i = pred := by
                        apply Fin.ext
                        exact heq
                      have : (Q.link pred).direction = .forward := by
                        rw [← hiEq]
                        exact hiDir
                      rw [hpredDir] at this
                      contradiction
                    simpa only [pred] using lt_of_le_of_ne hiLe hiNe
                  right
                  right
                  exact ⟨Q, i, pred, Q.link pred, parent,
                    by simpa only [C] using hpath, hiLink, rfl,
                    hiPred, hpredDir, hparent, hsub, hpredRoot⟩



/-- The strictly later backward-link branch above is not a terminal
obstruction.  Its concrete limiting-ladder owner has the canonical
allowed-source prefix, so the native-frontier last-deleted-head
construction produces an actual backward-normalization state.  The route
indices are retained in the conclusion: this is the route-order advance
used by the simultaneous exchange, not an abstract provider premise. -/
theorem splitGroundedFreshRelevant_forwardLinkFinish_advances_or_backwardNormalization
    (owner : ActiveControlRequestAt
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S)))
    (l : Alternating.Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)).path.links)
    (hldir : l.direction = .forward)
    (hfinishRoot : ∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a l.path.finish) :
    (∃ b ∈ ForwardDescentFrontier
          (L := L) (hL := hL) (S := S),
        ∃ a ∈ ForwardDescentSources
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S),
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardDescentEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a b) ∨
      (∃ a ∈ ForwardDescentSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ForwardDescentEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          a (requestExit (chosenRequest owner.1))) ∨
      ∃ (Q : Alternating.FiniteTrace Gamma.graph)
          (i j : Fin (Q.lastIndex + 1))
          (b : Alternating.Link Gamma.graph) (parent : Gamma.DPath)
          (state : L.SplitGroundedFreshRelevantBackwardState
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)),
        (selectedErasedCompression
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).path = .finite Q ∧
        Q.link i = l ∧ Q.link j = b ∧ i < j ∧
        b.direction = .backward ∧
        parent ∈ (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths ∧
        b.path.IsSubpathOf parent ∧
        state.control = owner ∧ state.parent = parent ∧
        L.SplitGroundedFreshRelevantBackwardNormalizationResult state := by
  rcases splitGroundedFreshRelevant_forwardLinkFinish_advances
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) owner l hl hldir hfinishRoot with
    hboundary | hexit | ⟨Q, i, j, b, parent, hpath, hi, hj, hij,
      hbdir, hparent, hbsub, hbnot⟩
  · exact Or.inl hboundary
  · exact Or.inr (Or.inl hexit)
  · have hbmem : b ∈ (selectedErasedCompression
        (ForwardDescentIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (ForwardDescentControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path.links := by
      rw [hpath]
      exact ⟨j, hj⟩
    have hparentLimit : parent ∈ L.limitWarp := by
      simpa only [splitGroundedPopularAuxiliaryInput, limitWarp] using hparent
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      L.splitGroundedFreshAvoidingCanonicalBackwardOwner_rootPrefix
        hL hground hnotFresh S (chosenRequest owner.1) b hbmem hbdir
          parent hparentLimit hbsub
    have hqRoot : ∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a q.start :=
      ⟨q.start, hqStart, .refl⟩
    have hqNot : ¬ ∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a q.finish := by
      intro hroot
      apply hbnot
      simpa only [hqFinish] using hroot
    let R := ForwardDescentRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)
    obtain ⟨D, hDnot⟩ :=
      R.exists_unrootedLastDeletedHead_sourceFirstTotal
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        q hqRoot hqNot
    have hexposed : parent ∈ exposedLadderPaths
        (L.splitGroundedPopularAuxiliaryInput hL.legal)
        (strongSelectedPath
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)) :=
      L.splitGroundedBackwardLink_parent_exposedAt
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        owner b hbmem hbdir parent hparent hbsub
    let resolution := L.splitGroundedRelevantDeletedResolutionAt
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
      parent hparent q hqSupport hqEdges D
    let state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) := {
      control := owner
      parent := parent
      parent_mem := hparentLimit
      parent_exposed := hexposed
      rootPath := q
      rootPath_start_rooted := hqRoot
      rootPath_finish_not_rooted := hqNot
      rootPath_support := hqSupport
      rootPath_edges := hqEdges
      deleted := D
      deleted_head_not_rooted := hDnot
      resolution := resolution }
    exact Or.inr (Or.inr ⟨Q, i, j, b, parent, state, hpath, hi, hj,
      hij, hbdir, hparent, hbsub, rfl, rfl, state.normalize⟩)

/-- Exact native-frontier route-order advance.  The first alternative keeps
the selected forward-link first-hit segment and its common allowed source;
the backward alternative is still converted immediately to its concrete
normalization state. -/
theorem splitGroundedFreshRelevant_forwardLinkFinish_advances_or_backwardNormalization_exact
    (owner : ActiveControlRequestAt
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S)))
    (l : Alternating.Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)).path.links)
    (hldir : l.direction = .forward)
    (hfinishRoot : ∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a l.path.finish) :
    Nonempty (L.SplitGroundedFreshRelevantForwardLinkFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S)
      (ForwardDescentSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) owner) ∨
      (∃ a ∈ ForwardDescentSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ForwardDescentEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          a (requestExit (chosenRequest owner.1))) ∨
      ∃ (Q : Alternating.FiniteTrace Gamma.graph)
          (i j : Fin (Q.lastIndex + 1))
          (b : Alternating.Link Gamma.graph) (parent : Gamma.DPath)
          (state : L.SplitGroundedFreshRelevantBackwardState
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)),
        (selectedErasedCompression
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).path = .finite Q ∧
        Q.link i = l ∧ Q.link j = b ∧ i < j ∧
        b.direction = .backward ∧
        parent ∈ (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths ∧
        b.path.IsSubpathOf parent ∧
        state.control = owner ∧ state.parent = parent ∧
        L.SplitGroundedFreshRelevantBackwardNormalizationResult state := by
  rcases splitGroundedFreshRelevant_forwardLinkFinish_advances_exact
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S) owner l hl hldir hfinishRoot with
    hboundary | hexit | ⟨Q, i, j, b, parent, hpath, hi, hj, hij,
      hbdir, hparent, hbsub, hbnot⟩
  · exact Or.inl hboundary
  · exact Or.inr (Or.inl hexit)
  · have hbmem : b ∈ (selectedErasedCompression
        (ForwardDescentIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (ForwardDescentControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (chosenRequest owner.1)).path.links := by
      rw [hpath]
      exact ⟨j, hj⟩
    have hparentLimit : parent ∈ L.limitWarp := by
      simpa only [splitGroundedPopularAuxiliaryInput, limitWarp] using hparent
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      L.splitGroundedFreshAvoidingCanonicalBackwardOwner_rootPrefix
        hL hground hnotFresh S (chosenRequest owner.1) b hbmem hbdir
          parent hparentLimit hbsub
    have hqRoot : ∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a q.start :=
      ⟨q.start, hqStart, .refl⟩
    have hqNot : ¬ ∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a q.finish := by
      intro hroot
      apply hbnot
      simpa only [hqFinish] using hroot
    let R := ForwardDescentRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)
    obtain ⟨D, hDnot⟩ :=
      R.exists_unrootedLastDeletedHead_sourceFirstTotal
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        q hqRoot hqNot
    have hexposed : parent ∈ exposedLadderPaths
        (L.splitGroundedPopularAuxiliaryInput hL.legal)
        (strongSelectedPath
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)) :=
      L.splitGroundedBackwardLink_parent_exposedAt
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        owner b hbmem hbdir parent hparent hbsub
    let resolution := L.splitGroundedRelevantDeletedResolutionAt
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
      parent hparent q hqSupport hqEdges D
    let state : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) := {
      control := owner
      parent := parent
      parent_mem := hparentLimit
      parent_exposed := hexposed
      rootPath := q
      rootPath_start_rooted := hqRoot
      rootPath_finish_not_rooted := hqNot
      rootPath_support := hqSupport
      rootPath_edges := hqEdges
      deleted := D
      deleted_head_not_rooted := hDnot
      resolution := resolution }
    exact Or.inr (Or.inr ⟨Q, i, j, b, parent, state, hpath, hi, hj,
      hij, hbdir, hparent, hbsub, rfl, rfl, state.normalize⟩)



/-- A terminal residual departure at the native frontier is also genuine
progress, rather than a stranded obstruction.  If its frontier tail is not
already rooted, the initial segment ending at that tail has a last deleted
head strictly before the old one.  This produces the same-parent state used
by the established well-founded normalizer. -/
theorem SplitGroundedFreshRelevantBackwardNormalizedOutcome.boundaryDeparture_rooted_or_strictDescent
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (tail : V)
    (incoming_mem : (tail, state.deleted.head) ∈ state.rootPath.edgeSet)
    (_residual : (tail, state.deleted.head) ∈ residualLadderEdges
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S)
    (tail_mem : tail ∈ ForwardDescentFrontier
      (L := L) (hL := hL) (S := S)) :
    (∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a tail) ∨
      ∃ next : L.SplitGroundedFreshRelevantBackwardState
          (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        next.parent = state.parent ∧
          GroundingCut.BeforeEq state.parent next.rootPath.finish
            state.rootPath.finish ∧
          GroundingCut.Before state.parent next.deleted.head
            state.deleted.head ∧
          next.Precedes state ∧
          L.SplitGroundedFreshRelevantBackwardNormalizationResult next := by
  by_cases htail : ∃ a ∈ ForwardDescentSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ ForwardDescentEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) a tail
  · exact Or.inl htail
  · right
    have htailSupport : tail ∈ state.rootPath.support :=
      (state.rootPath.edgeSet_subset_support_prod incoming_mem).1
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix
        (.inl state.rootPath : Gamma.DPath) htailSupport
    have hqRoot : ∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a q.start := by
      simpa only [hqStart, Path.initial] using state.rootPath_start_rooted
    have hqNot : ¬ ∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a q.finish := by
      simpa only [hqFinish] using htail
    let R := ForwardDescentRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)
    obtain ⟨D, hDnot⟩ :=
      R.exists_unrootedLastDeletedHead_sourceFirstTotal
        (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
        q hqRoot hqNot
    have hparentInput : state.parent ∈
        (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths := by
      simpa only [splitGroundedPopularAuxiliaryInput, limitWarp]
        using state.parent_mem
    have hqParentSupport : q.support ⊆ state.parent.support :=
      hqSupport.trans state.rootPath_support
    have hqParentEdges : q.edgeSet ⊆ state.parent.edgeSet :=
      hqEdges.trans state.rootPath_edges
    let resolution := L.splitGroundedRelevantDeletedResolutionAt
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S))
      state.parent hparentInput q hqParentSupport hqParentEdges D
    let next : L.SplitGroundedFreshRelevantBackwardState
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) := {
      control := state.control
      parent := state.parent
      parent_mem := state.parent_mem
      parent_exposed := state.parent_exposed
      rootPath := q
      rootPath_start_rooted := hqRoot
      rootPath_finish_not_rooted := hqNot
      rootPath_support := hqParentSupport
      rootPath_edges := hqParentEdges
      deleted := D
      deleted_head_not_rooted := hDnot
      resolution := resolution }
    have hDmem : D.head ∈ q.support := D.head_mem_parent
    have hDtail : GroundingCut.BeforeEq state.parent D.head tail := by
      have hqSub : q.IsSubpathOf state.parent :=
        ⟨hqParentSupport, hqParentEdges⟩
      simpa only [hqFinish] using
        splitGroundedFreshAvoiding_finiteSubpath_mem_beforeEq_finish
          state.parent q hqSub hDmem
    have htailHead : GroundingCut.Before state.parent tail
        state.deleted.head := by
      have hedge : (tail, state.deleted.head) ∈ state.parent.edgeSet :=
        state.rootPath_edges incoming_mem
      exact ⟨GroundingCut.beforeEq_of_mem_edgeSet hedge,
        GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet hedge⟩
    have hDHead : GroundingCut.Before state.parent D.head
        state.deleted.head :=
      splitGroundedFreshAvoiding_before_of_beforeEq_before
        state.parent hDtail htailHead
    have hnext : next.Precedes state := by
      exact Prod.Lex.right _
        (freshRelevantPathPosition_lt_of_before state.parent hDHead)
    have hfinish : GroundingCut.BeforeEq state.parent
        next.rootPath.finish state.rootPath.finish := by
      have hrootSub : state.rootPath.IsSubpathOf state.parent :=
        ⟨state.rootPath_support, state.rootPath_edges⟩
      have htailFinish :=
        splitGroundedFreshAvoiding_finiteSubpath_mem_beforeEq_finish
          state.parent state.rootPath hrootSub htailSupport
      simpa only [next, hqFinish] using htailFinish
    exact ⟨next, rfl, hfinish, hDHead, hnext, next.normalize⟩

/-- A rooted selected backward-link exit advances along the immediately
following forward link of the same finite selected route.  It reaches the
actual stopping frontier, reaches the request exit, or exposes a strictly
later backward link already converted to a native-frontier normalization
state. -/
theorem splitGroundedFreshRelevant_backwardLinkStart_advances_or_backwardNormalization
    (owner : ActiveControlRequestAt
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ForwardDescentFrontier (L := L) (hL := hL) (S := S)))
    (link : Alternating.Link Gamma.graph)
    (hlink : link ∈ (selectedErasedCompression
      (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
      (ForwardDescentControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (chosenRequest owner.1)).path.links)
    (hdir : link.direction = .backward)
    (hroot : ∃ a ∈ ForwardDescentSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ForwardDescentEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a link.path.start) :
    (∃ b ∈ ForwardDescentFrontier
          (L := L) (hL := hL) (S := S),
        ∃ a ∈ ForwardDescentSources
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S),
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardDescentEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S)) a b) ∨
      (∃ a ∈ ForwardDescentSources
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ ForwardDescentEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          a (requestExit (chosenRequest owner.1))) ∨
      ∃ (Q : Alternating.FiniteTrace Gamma.graph)
          (i j : Fin (Q.lastIndex + 1))
          (b : Alternating.Link Gamma.graph) (parent : Gamma.DPath)
          (state : L.SplitGroundedFreshRelevantBackwardState
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)),
        (selectedErasedCompression
          (ForwardDescentIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (ForwardDescentControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (chosenRequest owner.1)).path = .finite Q ∧
        Q.link i = link ∧ Q.link j = b ∧ i < j ∧
        b.direction = .backward ∧
        parent ∈ (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths ∧
        b.path.IsSubpathOf parent ∧
        state.control = owner ∧ state.parent = parent ∧
        L.SplitGroundedFreshRelevantBackwardNormalizationResult state := by
  let C := selectedErasedCompression
    (ForwardDescentIndexed (L := L) (hL := hL) (hground := hground)) S
    (ForwardDescentControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (chosenRequest owner.1)
  cases hpath : C.path with
  | trivial v =>
      have : link ∈ (∅ : Set (Alternating.Link Gamma.graph)) := by
        simpa only [C, hpath, AltPath.links] using hlink
      exact False.elim (by simpa using this)
  | infinite Q =>
      have hfalse : (none : Option V) =
          some (requestExit (chosenRequest owner.1)) := by
        simpa only [C, hpath, AltPath.terminal?] using C.terminal_eq
      cases hfalse
  | finite Q =>
      have hlinkQ : link ∈ (AltPath.finite Q).links := by
        simpa only [C, hpath] using hlink
      obtain ⟨i, hiLink⟩ := hlinkQ
      have hiDir : (Q.link i).direction = .backward := by
        simpa only [hiLink] using hdir
      have hterminal : Q.terminal = requestExit (chosenRequest owner.1) := by
        exact Option.some.inj (by
          simpa only [C, hpath, AltPath.terminal?] using C.terminal_eq)
      by_cases hiLast : i.1 = Q.lastIndex
      · have hi : i = ⟨Q.lastIndex, Nat.lt_succ_self _⟩ := by
          apply Fin.ext
          exact hiLast
        have hlinkLast : link = Q.lastLink := by
          rw [← hiLink, hi]
          rfl
        have hlastDir : Q.lastLink.direction = .backward := by
          rw [← hlinkLast]
          exact hdir
        have hstartEq : link.path.start = Q.terminal := by
          rw [hlinkLast]
          simp only [FiniteTrace.terminal, Link.exit, hlastDir]
        exact Or.inr (Or.inl (by
          simpa only [hstartEq, hterminal] using hroot))
      · have hiLt : i.1 < Q.lastIndex := by omega
        let k : Fin (Q.lastIndex + 1) := ⟨i.1 + 1, by omega⟩
        let p : Fin Q.lastIndex := ⟨i.1, hiLt⟩
        have hcast : Fin.castSucc p = i := by
          apply Fin.ext
          rfl
        have hsucc : p.succ = k := by
          apply Fin.ext
          rfl
        have hkDir : (Q.link k).direction = .forward := by
          have halt := Q.alternates p
          rw [hcast, hiDir, hsucc] at halt
          cases hk : (Q.link k).direction with
          | forward => rfl
          | backward => exact False.elim (halt hk.symm)
        have hjoin : link.path.start = (Q.link k).path.start := by
          have hj := Q.joins p
          rw [hcast, hsucc, hiLink, Link.exit, hdir,
            Link.entry, hkDir] at hj
          exact hj
        have hkRoot : ∃ a ∈ ForwardDescentSources
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S),
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ ForwardDescentEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S))
            a (Q.link k).path.start := by
          simpa only [← hjoin] using hroot
        have hkMem : Q.link k ∈ C.path.links := by
          rw [hpath]
          exact ⟨k, rfl⟩
        rcases activeForwardLink_startRooted_finish_or_boundary
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) owner (Q.link k)
            hkMem hkDir hkRoot with hboundary | hkFinish
        · exact Or.inl hboundary
        · rcases L.splitGroundedFreshRelevant_forwardLinkFinish_advances_or_backwardNormalization
              (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
              (S := S) owner (Q.link k) hkMem hkDir hkFinish with
            hboundary | hexit | ⟨Q', i', j, b, parent, state,
              hpath', hi', hj, hij, hbdir, hparent, hbsub,
              hcontrol, hstateParent, hstate⟩
          · exact Or.inl hboundary
          · exact Or.inr (Or.inl hexit)
          · have hQQ : Q' = Q := by
              rw [hpath] at hpath'
              exact AltPath.finite.inj hpath'.symm
            subst Q'
            have hi'k : i' = k := finiteTrace_link_injective Q hi'
            have hij' : i < j := by
              rw [hi'k] at hij
              exact lt_trans (by show i.1 < k.1; simp only [k]; omega) hij
            exact Or.inr (Or.inr ⟨Q, i, j, b, parent, state,
              by simpa only [C] using hpath, hiLink, hj, hij', hbdir,
              hparent, hbsub, hcontrol, hstateParent, hstate⟩)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRooted_or_strictDescent
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRoot_advances_exact
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantForwardFirstHit.conflictTail_rooted
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantForwardFirstHit.exists_source_to_parent_finish_exchangePath
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardNormalizedOutcome.forwardSplice_headRoot_advances
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_forwardLinkFinish_advances
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_forwardLinkFinish_advances_exact
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_forwardLinkFinish_advances_or_backwardNormalization
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_forwardLinkFinish_advances_or_backwardNormalization_exact
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardNormalizedOutcome.boundaryDeparture_rooted_or_strictDescent
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_backwardLinkStart_advances_or_backwardNormalization
