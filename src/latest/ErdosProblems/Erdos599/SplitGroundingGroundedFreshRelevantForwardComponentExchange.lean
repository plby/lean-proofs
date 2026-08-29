/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardSpliceDescent
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshReachableSinkWarp
import ErdosProblems.Erdos599.RootReachablePathRetention
import ErdosProblems.Erdos599.BlueprintSplice

/-!
# Component exchange at an exact selected first hit

The exact same-tail first-hit branch is not a rootedness proof in the old
switched relation: its old incoming edge was deleted.  This module performs
the corresponding genuine component exchange.  In the full source-reachable
component warp, take the final point at which the discarded old-parent
suffix still meets the reachable carrier.  Retain the reachable component
prefix through that point and append the remaining old-parent suffix.  The
new suffix is disjoint from every other reachable component by construction,
so replacing the unique old member gives an honest warp with unchanged
initial set and with the original failed endpoint as an actual terminal.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingErasedSwitchRelation GroundingSourceReachableSinkWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev ExchangeIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev ExchangeControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev ExchangeRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev ExchangeFrontier : Set V :=
  L.splitGroundedFreshRelevantStoppingFrontier (hL := hL) (S := S)

private abbrev ExchangeEdges : Set (V × V) :=
  L.splitGroundedFreshRelevantSwitchedEdges
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)

private abbrev ExchangeSources : Set V :=
  Gamma.source \ {
    (ExchangeRecord (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)).record.initial}

private abbrev ExchangeSinkBoundary : Set V :=
  L.splitGroundedFreshReachableSinkBoundary
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)

/-- Replace the unique source-reachable component meeting the start of a
finite segment by its prefix through the final carrier contact followed by
the remaining segment.  This is the family-level exchange underlying all
of the more specialized forward-conflict repairs: it preserves the exact
allowed initial set and makes the segment endpoint an actual terminal. -/
theorem exists_splitGroundedFreshRelevantComponentExchangeWarp_of_segment_with_terminalUpdate
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (segment : FinitePath Gamma.graph)
    (hroot : ∃ a ∈ ExchangeSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ExchangeEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a segment.start) :
    ∃ (W : Set Gamma.DPath) (q : FinitePath Gamma.graph),
      Gamma.IsWarp W ∧
        Gamma.initialSet W =
          ExchangeSources (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) ∧
        (Sum.inl q : Gamma.DPath) ∈ W ∧
        q.finish = segment.finish ∧
        q.edgeSet ⊆
          ExchangeEdges (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∪
            segment.edgeSet ∧
        segment.finish ∈ Gamma.terminalFrontier W ∧
        ((∃ (old : FinitePath Gamma.graph) (contact : V),
            contact ∈ old.support ∧ contact ∈ segment.support ∧
            old.start ∈ ExchangeSources
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∧
            old.edgeSet ⊆
              ExchangeEdges (L := L) (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S) ∧
            old.finish ∈ ExchangeSinkBoundary
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∧
            Gamma.terminalFrontier W = insert segment.finish
              (ExchangeSinkBoundary
                (L := L) (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S) \ {old.finish})) ∨
          Gamma.terminalFrontier W = insert segment.finish
            (ExchangeSinkBoundary
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S))) := by
  let E := ExchangeEdges (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let A := ExchangeSources (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  obtain ⟨W, hW, hWEdges, hWVertex, hWInitial, hWTerminal⟩ :=
    L.exists_splitGroundedFreshReachableComponentWarp
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) hNoEnter
  obtain ⟨a, ha, haStart⟩ := hroot
  have hstartCarrier : segment.start ∈ RootReachableRelation.carrier E A :=
    RootReachableRelation.carrier_of_reflTransGen E A ha haStart
  have hstartW : segment.start ∈ Gamma.vertexSet W := by
    rw [hWVertex]
    exact hstartCarrier
  let hmeet : segment.walk.Meets (Gamma.vertexSet W) :=
    ⟨segment.start, segment.start_mem_support, hstartW⟩
  let tail := segment.lastHit (Gamma.vertexSet W) hmeet
  have htailStartW : tail.start ∈ Gamma.vertexSet W :=
    segment.lastHit_start_mem (Gamma.vertexSet W) hmeet
  obtain ⟨p, hpW, hpTail⟩ := htailStartW
  obtain ⟨front, hfrontStart, hfrontFinish, hfrontSupport, hfrontEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix p hpTail
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
      have hzNotW : z ∉ Gamma.vertexSet W :=
        segment.lastHit_no_mem_after (Gamma.vertexSet W) hmeet hzTail
      exact False.elim (hzNotW ⟨p, hpW, hfrontSupport hz.1⟩)
  let q := front.appendFinite tail hfrontFinish.symm hinter
  let W' : Set Gamma.DPath := insert (.inl q : Gamma.DPath) (W \ {p})
  have hqDisjoint : Disjoint q.support (Gamma.vertexSet (W \ {p})) := by
    rw [Set.disjoint_left]
    intro z hzq hzRest
    rw [show q.support = front.support ∪ tail.support by
      exact front.support_appendFinite_eq_union tail hfrontFinish.symm hinter]
      at hzq
    obtain ⟨r, hrRest, hzR⟩ := hzRest
    rcases hzq with hzFront | hzTail
    · have hne : p ≠ r := by
        intro hpr
        subst r
        exact hrRest.2 (Set.mem_singleton p)
      exact Set.disjoint_left.mp (hW hpW hrRest.1 hne)
        (hfrontSupport hzFront) hzR
    · by_cases hzeq : z = tail.start
      · exact Set.disjoint_left.mp (hW hpW hrRest.1 (by
          intro hpr
          subst r
          exact hrRest.2 (Set.mem_singleton p)))
          (hzeq ▸ hpTail) hzR
      · have hsupport : tail.walk.support =
            tail.start :: tail.walk.support.tail := by
          have h := (List.cons_head_tail tail.walk.support_ne_nil).symm
          simpa only [tail.walk.head_support] using h
        have hzAfter : z ∈ tail.walk.support.tail := by
          have hzSupport : z ∈ tail.walk.support := hzTail
          rw [hsupport] at hzSupport
          rcases List.mem_cons.mp hzSupport with hzStart | hzAfter
          · exact False.elim (hzeq hzStart)
          · exact hzAfter
        exact (segment.lastHit_no_mem_after
          (Gamma.vertexSet W) hmeet hzAfter) ⟨r, hrRest.1, hzR⟩
  have hW' : Gamma.IsWarp W' := by
    exact DWeb.IsWarp.insert_finite_of_disjoint Gamma
      (DWeb.IsWarp.sdiff_singleton Gamma hW p) q hqDisjoint
  have hpInitialA : p.initial ∈ A := by
    have hpInitial : p.initial ∈ Gamma.initialSet W := ⟨p, hpW, rfl⟩
    have hpAllowed := hWInitial ▸ hpInitial
    simpa only [A, ExchangeSources] using hpAllowed
  have hqStart : q.start = p.initial := by
    simpa only [q, FinitePath.appendFinite_start, hfrontStart]
  have hqFinish : q.finish = segment.finish := by
    have htailFinish : tail.finish = segment.finish := rfl
    simpa only [q, FinitePath.appendFinite_finish, htailFinish]
  have hqEdges : q.edgeSet ⊆ E ∪ segment.edgeSet := by
    rw [show q.edgeSet = front.edgeSet ∪ tail.edgeSet by
      exact Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite
        front tail hfrontFinish.symm hinter]
    intro e he
    rcases he with heFront | heTail
    · left
      have hpFamily : e ∈ familyEdges W := by
        exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2
          ⟨hpW, hfrontEdges heFront⟩⟩
      exact RootReachableRelation.edges_subset E A (hWEdges ▸ hpFamily)
    · right
      exact segment.lastHit_edgeSet_subset
        (Gamma.vertexSet W) hmeet heTail
  have hW'Initial : Gamma.initialSet W' = A := by
    change Gamma.initialSet (insert (.inl q : Gamma.DPath) (W \ {p})) = A
    rw [Gamma.initialSet_insert_finite,
      DWeb.IsWarp.initialSet_sdiff_singleton Gamma hW hpW, hqStart,
      hWInitial]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | hx)
      · exact hpInitialA
      · exact hx.1
    · intro hx
      by_cases hxp : x = p.initial
      · exact Or.inl hxp
      · exact Or.inr ⟨hx, hxp⟩
  have hterminalUpdate :
      ((∃ (old : FinitePath Gamma.graph) (contact : V),
          contact ∈ old.support ∧ contact ∈ segment.support ∧
          old.start ∈ ExchangeSources
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) ∧
          old.edgeSet ⊆
            ExchangeEdges (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∧
          old.finish ∈ ExchangeSinkBoundary
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) ∧
          Gamma.terminalFrontier W' = insert segment.finish
            (ExchangeSinkBoundary
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) \ {old.finish})) ∨
        Gamma.terminalFrontier W' = insert segment.finish
          (ExchangeSinkBoundary
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))) := by
    cases p with
    | inl old =>
        left
        refine ⟨old, tail.start, hpTail, ?_, hpInitialA, ?_, ?_, ?_⟩
        · exact segment.lastHit_support_subset
            (Gamma.vertexSet W) hmeet tail.start_mem_support
        · intro e he
          apply RootReachableRelation.edges_subset E A
          rw [← hWEdges]
          exact Set.mem_iUnion.2 ⟨.inl old,
            Set.mem_iUnion.2 ⟨hpW, he⟩⟩
        · change old.finish ∈ L.splitGroundedFreshReachableSinkBoundary
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)
          rw [← hWTerminal]
          exact ⟨.inl old, hpW, rfl⟩
        · change Gamma.terminalFrontier
            (insert (.inl q : Gamma.DPath) (W \ {Sum.inl old})) = _
          rw [Gamma.terminalFrontier_insert_finite,
            DWeb.IsWarp.terminalFrontier_sdiff_singleton Gamma hW hpW rfl,
            hWTerminal]
          simpa only [ExchangeSinkBoundary, hqFinish]
    | inr ray =>
        right
        have hremove : Gamma.terminalFrontier (W \ {Sum.inr ray}) =
            Gamma.terminalFrontier W := by
          ext x
          constructor
          · rintro ⟨r, hr, hrx⟩
            exact ⟨r, hr.1, hrx⟩
          · rintro ⟨r, hr, hrx⟩
            refine ⟨r, ⟨hr, ?_⟩, hrx⟩
            intro hre
            have hre' : r = Sum.inr ray := Set.mem_singleton_iff.mp hre
            subst r
            cases hrx
        change Gamma.terminalFrontier
            (insert (.inl q : Gamma.DPath) (W \ {Sum.inr ray})) = _
        rw [Gamma.terminalFrontier_insert_finite, hremove, hWTerminal]
        simpa only [ExchangeSinkBoundary, hqFinish]
  refine ⟨W', q, hW', hW'Initial, Set.mem_insert _ _, hqFinish,
    hqEdges, ?_, hterminalUpdate⟩
  exact ⟨.inl q, Set.mem_insert _ _, congrArg some hqFinish⟩

/-- Endpoint/edge projection of the terminal-update exchange. -/
theorem exists_splitGroundedFreshRelevantComponentExchangeWarp_of_segment
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (segment : FinitePath Gamma.graph)
    (hroot : ∃ a ∈ ExchangeSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ExchangeEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a segment.start) :
    ∃ (W : Set Gamma.DPath) (q : FinitePath Gamma.graph),
      Gamma.IsWarp W ∧
        Gamma.initialSet W =
          ExchangeSources (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) ∧
        (Sum.inl q : Gamma.DPath) ∈ W ∧
        q.finish = segment.finish ∧
        q.edgeSet ⊆
          ExchangeEdges (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∪
            segment.edgeSet ∧
        segment.finish ∈ Gamma.terminalFrontier W := by
  obtain ⟨W, q, hW, hinitial, hqW, hfinish, hedges, hterminal, _hupdate⟩ :=
    L.exists_splitGroundedFreshRelevantComponentExchangeWarp_of_segment_with_terminalUpdate
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) hNoEnter segment hroot
  exact ⟨W, q, hW, hinitial, hqW, hfinish, hedges, hterminal⟩

/-- A rooted point weakly before `z` on one limiting component can be
exchanged all the way to `z`.  The equality case uses the trivial segment;
otherwise the actual finite parent segment is retained in the replacement
component. -/
theorem exists_splitGroundedFreshRelevantComponentExchangeWarp_of_rooted_beforeEq
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (parent : Gamma.DPath) {x z : V}
    (hroot : ∃ a ∈ ExchangeSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ ExchangeEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a x)
    (hxz : GroundingCut.BeforeEq parent x z) :
    ∃ (W : Set Gamma.DPath) (q : FinitePath Gamma.graph),
      Gamma.IsWarp W ∧
        Gamma.initialSet W =
          ExchangeSources (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) ∧
        (Sum.inl q : Gamma.DPath) ∈ W ∧
        q.finish = z ∧
        q.edgeSet ⊆
          ExchangeEdges (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∪
            parent.edgeSet ∧
        z ∈ Gamma.terminalFrontier W := by
  obtain ⟨segment, hstart, hfinish, hsegmentEdges⟩ :
      ∃ segment : FinitePath Gamma.graph,
        segment.start = x ∧ segment.finish = z ∧
          segment.edgeSet ⊆ parent.edgeSet := by
    by_cases h : x = z
    · subst z
      refine ⟨FinitePath.trivial Gamma.graph x, ?_, ?_, ?_⟩
      · exact FinitePath.trivial_start Gamma.graph x
      · exact FinitePath.trivial_finish Gamma.graph x
      · intro e he
        simp [FinitePath.edgeSet, FinitePath.trivial] at he
    · exact GroundingCutDecoder.exists_forward_segment_of_before ⟨hxz, h⟩
  have hsegmentRoot : ∃ a ∈ ExchangeSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ ExchangeEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a segment.start := by
    simpa only [hstart] using hroot
  obtain ⟨W, q, hW, hWInitial, hqW, hqFinish, hqEdges, hqTerminal⟩ :=
    L.exists_splitGroundedFreshRelevantComponentExchangeWarp_of_segment
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) hNoEnter segment hsegmentRoot
  refine ⟨W, q, hW, hWInitial, hqW, hqFinish.trans hfinish,
    hqEdges.trans ?_, ?_⟩
  · exact Set.union_subset_union Subset.rfl hsegmentEdges
  · simpa only [hfinish] using hqTerminal

/-- A concrete family-level exchange for the exact first-hit branch.  The
replacement family has the same allowed initial set as the canonical
source-reachable component warp and contains a finite component ending at
the original failed endpoint.  Its new edges use only the canonical switched
relation and the old failed root path. -/
theorem SplitGroundedFreshRelevantForwardFirstHit.exists_componentExchangeWarp
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ExchangeControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ExchangeFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (X : L.SplitGroundedFreshRelevantForwardFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S)
      (ExchangeSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) state splice)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1) :
    ∃ (W : Set Gamma.DPath) (q : FinitePath Gamma.graph),
      Gamma.IsWarp W ∧
        Gamma.initialSet W =
          ExchangeSources (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) ∧
        (Sum.inl q : Gamma.DPath) ∈ W ∧
        q.finish = state.rootPath.finish ∧
        q.edgeSet ⊆
          ExchangeEdges (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∪
            state.rootPath.edgeSet ∧
        state.rootPath.finish ∈ Gamma.terminalFrontier W := by
  let U := ExchangeIndexed (L := L) (hL := hL) (hground := hground)
  let K := ExchangeControls (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  let T := ExchangeFrontier (L := L) (hL := hL) (S := S)
  let E := ExchangeEdges (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let A := ExchangeSources (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  obtain ⟨W, hW, hWEdges, hWVertex, hWInitial, _hWTerminal⟩ :=
    L.exists_splitGroundedFreshReachableComponentWarp
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) hNoEnter
  have htailRoot : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) X.source splice.incomingTail := by
    exact X.conflictTail_rooted Set.sdiff_subset hNoEnter state splice same_tail
  have htailCarrier : splice.incomingTail ∈
      RootReachableRelation.carrier E A :=
    RootReachableRelation.carrier_of_reflTransGen E A X.source_mem htailRoot
  have htailW : splice.incomingTail ∈ Gamma.vertexSet W := by
    rw [hWVertex]
    exact htailCarrier
  have htailParent : splice.incomingTail ∈ state.rootPath.support :=
    (state.rootPath.edgeSet_subset_support_prod splice.incoming_mem).1
  let oldSuffix := state.rootPath.suffixFrom splice.incomingTail htailParent
  have htailSuffix : splice.incomingTail ∈ oldSuffix.support := by
    have h := oldSuffix.start_mem_support
    simpa only [oldSuffix, FinitePath.suffixFrom_start] using h
  let hmeet : oldSuffix.walk.Meets (Gamma.vertexSet W) :=
    ⟨splice.incomingTail, htailSuffix, htailW⟩
  let tail := oldSuffix.lastHit (Gamma.vertexSet W) hmeet
  have htailStartW : tail.start ∈ Gamma.vertexSet W :=
    oldSuffix.lastHit_start_mem (Gamma.vertexSet W) hmeet
  obtain ⟨p, hpW, hpTail⟩ := htailStartW
  obtain ⟨front, hfrontStart, hfrontFinish, hfrontSupport, hfrontEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix p hpTail
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
      have hzNotW : z ∉ Gamma.vertexSet W :=
        oldSuffix.lastHit_no_mem_after (Gamma.vertexSet W) hmeet hzTail
      exact False.elim (hzNotW ⟨p, hpW, hfrontSupport hz.1⟩)
  let q := front.appendFinite tail hfrontFinish.symm hinter
  let W' : Set Gamma.DPath := insert (.inl q : Gamma.DPath) (W \ {p})
  have hqDisjoint : Disjoint q.support (Gamma.vertexSet (W \ {p})) := by
    rw [Set.disjoint_left]
    intro z hzq hzRest
    rw [show q.support = front.support ∪ tail.support by
      exact front.support_appendFinite_eq_union tail hfrontFinish.symm hinter]
      at hzq
    obtain ⟨r, hrRest, hzR⟩ := hzRest
    rcases hzq with hzFront | hzTail
    · have hne : p ≠ r := by
        intro hpr
        subst r
        exact hrRest.2 (Set.mem_singleton p)
      exact Set.disjoint_left.mp (hW hpW hrRest.1 hne)
        (hfrontSupport hzFront) hzR
    · by_cases hzeq : z = tail.start
      · exact Set.disjoint_left.mp (hW hpW hrRest.1 (by
          intro hpr
          subst r
          exact hrRest.2 (Set.mem_singleton p)))
          (hzeq ▸ hpTail) hzR
      · have hsupport : tail.walk.support =
            tail.start :: tail.walk.support.tail := by
          have h := (List.cons_head_tail tail.walk.support_ne_nil).symm
          simpa only [tail.walk.head_support] using h
        have hzAfter : z ∈ tail.walk.support.tail := by
          have hzSupport : z ∈ tail.walk.support := hzTail
          rw [hsupport] at hzSupport
          rcases List.mem_cons.mp hzSupport with hzStart | hzAfter
          · exact False.elim (hzeq hzStart)
          · exact hzAfter
        exact (oldSuffix.lastHit_no_mem_after
          (Gamma.vertexSet W) hmeet hzAfter) ⟨r, hrRest.1, hzR⟩
  have hW' : Gamma.IsWarp W' := by
    exact DWeb.IsWarp.insert_finite_of_disjoint Gamma
      (DWeb.IsWarp.sdiff_singleton Gamma hW p) q hqDisjoint
  have hpInitialA : p.initial ∈ A := by
    have hpInitial : p.initial ∈ Gamma.initialSet W := ⟨p, hpW, rfl⟩
    have hpAllowed := hWInitial ▸ hpInitial
    simpa only [A, ExchangeSources] using hpAllowed
  have hqStart : q.start = p.initial := by
    simpa only [q, FinitePath.appendFinite_start, hfrontStart]
  have hqFinish : q.finish = state.rootPath.finish := by
    have htailFinish : tail.finish = state.rootPath.finish := by
      calc
        tail.finish = oldSuffix.finish := rfl
        _ = state.rootPath.finish :=
          state.rootPath.suffixFrom_finish splice.incomingTail htailParent
    simpa only [q, FinitePath.appendFinite_finish, htailFinish]
  have hqEdges : q.edgeSet ⊆ E ∪ state.rootPath.edgeSet := by
    rw [show q.edgeSet = front.edgeSet ∪ tail.edgeSet by
      exact Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite
        front tail hfrontFinish.symm hinter]
    intro e he
    rcases he with heFront | heTail
    · left
      have hpFamily : e ∈ familyEdges W := by
        exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2
          ⟨hpW, hfrontEdges heFront⟩⟩
      exact RootReachableRelation.edges_subset E A (hWEdges ▸ hpFamily)
    · right
      exact (oldSuffix.lastHit_edgeSet_subset
        (Gamma.vertexSet W) hmeet heTail) |> (state.rootPath.suffixFrom_edgeSet_subset
          splice.incomingTail htailParent)
  have hW'Initial : Gamma.initialSet W' = A := by
    change Gamma.initialSet (insert (.inl q : Gamma.DPath) (W \ {p})) = A
    rw [Gamma.initialSet_insert_finite,
      DWeb.IsWarp.initialSet_sdiff_singleton Gamma hW hpW, hqStart,
      hWInitial]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | hx)
      · exact hpInitialA
      · exact hx.1
    · intro hx
      by_cases hxp : x = p.initial
      · exact Or.inl hxp
      · exact Or.inr ⟨hx, hxp⟩
  refine ⟨W', q, hW', hW'Initial, Set.mem_insert _ _, hqFinish,
    hqEdges, ?_⟩
  exact ⟨.inl q, Set.mem_insert _ _, congrArg some hqFinish⟩

/-- In every full source-reachable component realization of the canonical
stopped relation, the component containing the conflict tail is finite and
ends at the exact first frontier hit stored by `X`.  Thus the forward
exchange does not merely produce an arbitrary rooted frontier vertex: it
identifies the currently occupied sink which the exchange must trade. -/
theorem SplitGroundedFreshRelevantForwardFirstHit.exists_currentComponent_ending_at_finish
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ExchangeControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ExchangeFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (X : L.SplitGroundedFreshRelevantForwardFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S)
      (ExchangeSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) state splice)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1) :
    ∃ (W : Set Gamma.DPath) (old : FinitePath Gamma.graph),
      Gamma.IsWarp W ∧
      familyEdges W = RootReachableRelation.edges
        (ExchangeEdges (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (ExchangeSources (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∧
      Gamma.vertexSet W = RootReachableRelation.carrier
        (ExchangeEdges (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (ExchangeSources (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∧
      (Sum.inl old : Gamma.DPath) ∈ W ∧
      splice.incomingTail ∈ old.support ∧
      old.finish = X.path.finish := by
  let E := ExchangeEdges (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let A := ExchangeSources (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  obtain ⟨W, hW, hWEdges, hWVertex, _hWInitial, _hWTerminal⟩ :=
    L.exists_splitGroundedFreshReachableComponentWarp
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) hNoEnter
  have htailRoot : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) X.source splice.incomingTail := by
    exact X.conflictTail_rooted Set.sdiff_subset hNoEnter
      state splice same_tail
  have htailCarrier : splice.incomingTail ∈
      RootReachableRelation.carrier E A :=
    RootReachableRelation.carrier_of_reflTransGen E A X.source_mem htailRoot
  have htailW : splice.incomingTail ∈ Gamma.vertexSet W := by
    rw [hWVertex]
    exact htailCarrier
  obtain ⟨p, hpW, htailP⟩ := htailW
  have hforward : splice.contact.forwardEdge ∈ E := by
    exact GroundingErasedDecode.activeRetainedForwardEdgesAt_subset_switched
      (ExchangeIndexed (L := L) (hL := hL) (hground := hground)) S
      (ExchangeControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (ExchangeFrontier (L := L) (hL := hL) (S := S))
      splice.contact.owner splice.contact.retained
  have hheadFinish : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) splice.contact.forwardEdge.2 X.path.finish := by
    have h := GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
      X.path X.path_edges X.path.finish_mem_support
    simpa only [X.path_start] using h
  have htailFinish : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) splice.incomingTail X.path.finish := by
    have hstep : Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ E)
        splice.contact.forwardEdge.1 splice.contact.forwardEdge.2 :=
      Relation.ReflTransGen.single hforward
    simpa only [same_tail] using hstep.trans hheadFinish
  have toReachable : ∀ {z : V},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
        splice.incomingTail z →
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ RootReachableRelation.edges E A)
        splice.incomingTail z := by
    intro z hz
    induction hz with
    | refl => exact .refl
    | @tail y z hyz hyzEdge ih =>
        have hyCarrier : y ∈ RootReachableRelation.carrier E A :=
          RootReachableRelation.carrier_of_reflTransGen_of_mem E A
            htailCarrier hyz
        exact ih.tail ⟨hyzEdge, hyCarrier⟩
  have htailFinishReachable : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ RootReachableRelation.edges E A)
      splice.incomingTail X.path.finish :=
    toReachable htailFinish
  have hfinishP : X.path.finish ∈ p.support := by
    have hstay : ∀ {z : V},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RootReachableRelation.edges E A)
          splice.incomingTail z → z ∈ p.support := by
      intro z hz
      induction hz with
      | refl => exact htailP
      | @tail y z _hyz hyz ih =>
          have hyzFamily : (y, z) ∈ familyEdges W := by
            rw [hWEdges]
            exact hyz
          simp only [familyEdges, Set.mem_iUnion] at hyzFamily
          obtain ⟨q, hqW, hyzQ⟩ := hyzFamily
          have hyQ : y ∈ q.support :=
            (q.edgeSet_subset_support_prod hyzQ).1
          have hzQ : z ∈ q.support :=
            (q.edgeSet_subset_support_prod hyzQ).2
          have hpq : p = q := by
            by_contra hpq
            exact Set.disjoint_left.mp (hW hpW hqW hpq) ih hyQ
          simpa only [hpq] using hzQ
    exact hstay htailFinishReachable
  have hnoFinish : ¬ HasOutgoing E X.path.finish := by
    exact GroundingErasedDecode.boundary_noOutgoing_switchedAt
      (ExchangeIndexed (L := L) (hL := hL) (hground := hground)) S
      (ExchangeControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (ExchangeFrontier (L := L) (hL := hL) (S := S)) X.finish_mem
  cases p with
  | inl old =>
      have hfinish : old.finish = X.path.finish := by
        by_contra hne
        obtain ⟨y, hxy⟩ :=
          _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            old hfinishP (Ne.symm hne)
        apply hnoFinish
        refine ⟨y, RootReachableRelation.edges_subset E A ?_⟩
        rw [← hWEdges]
        exact Set.mem_iUnion.2 ⟨.inl old,
          Set.mem_iUnion.2 ⟨hpW, hxy⟩⟩
      exact ⟨W, old, hW, hWEdges, hWVertex, hpW,
        htailP, hfinish⟩
  | inr ray =>
      obtain ⟨n, hn⟩ := hfinishP
      exfalso
      apply hnoFinish
      refine ⟨ray (n + 1), RootReachableRelation.edges_subset E A ?_⟩
      rw [← hWEdges]
      have hedge : (X.path.finish, ray (n + 1)) ∈ ray.edgeSet := by
        simpa only [hn] using (show (ray n, ray (n + 1)) ∈ ray.edgeSet from
          ⟨n, rfl⟩)
      exact Set.mem_iUnion.2 ⟨.inr ray,
        Set.mem_iUnion.2 ⟨hpW, hedge⟩⟩

/-- The exact first-hit exchange extends through the normalization ancestry
to the original failed endpoint.  In particular, this does not count the
intermediate frontier hit as coverage: the replacement component really
ends at `initial.rootPath.finish`. -/
theorem SplitGroundedFreshRelevantForwardFirstHit.exists_componentExchangeWarp_to_initialFinish
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (initial state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ExchangeControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ExchangeFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (X : L.SplitGroundedFreshRelevantForwardFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S)
      (ExchangeSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) state splice)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
    (same_parent : state.parent = initial.parent)
    (finish_beforeEq : GroundingCut.BeforeEq initial.parent
      state.rootPath.finish initial.rootPath.finish) :
    ∃ (W : Set Gamma.DPath) (q : FinitePath Gamma.graph),
      Gamma.IsWarp W ∧
        Gamma.initialSet W =
          ExchangeSources (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) ∧
        (Sum.inl q : Gamma.DPath) ∈ W ∧
        q.finish = initial.rootPath.finish ∧
        q.edgeSet ⊆
          ExchangeEdges (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∪
            initial.parent.edgeSet ∧
        initial.rootPath.finish ∈ Gamma.terminalFrontier W := by
  have htailRoot : ∃ a ∈ ExchangeSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ExchangeEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a splice.incomingTail := by
    refine ⟨X.source, X.source_mem, ?_⟩
    exact X.conflictTail_rooted Set.sdiff_subset hNoEnter
      state splice same_tail
  have htailMem : splice.incomingTail ∈ state.rootPath.support :=
    (state.rootPath.edgeSet_subset_support_prod splice.incoming_mem).1
  have htailBeforeState : GroundingCut.BeforeEq state.parent
      splice.incomingTail state.rootPath.finish :=
    freshRelevantFiniteSubpath_mem_beforeEq_finish
      state.parent state.rootPath
      ⟨state.rootPath_support, state.rootPath_edges⟩ htailMem
  have htailBeforeInitial : GroundingCut.BeforeEq initial.parent
      splice.incomingTail state.rootPath.finish := by
    simpa only [same_parent] using htailBeforeState
  have htailBeforeFinish : GroundingCut.BeforeEq initial.parent
      splice.incomingTail initial.rootPath.finish :=
    GroundingFragmentResidualOrder.beforeEq_trans
      htailBeforeInitial finish_beforeEq
  exact
    L.exists_splitGroundedFreshRelevantComponentExchangeWarp_of_rooted_beforeEq
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) hNoEnter initial.parent htailRoot htailBeforeFinish

/-- The terminal-update form of the exact first-hit exchange, specialized
to the selected exposed parent which caused the conflict.  Besides the new
warp, it retains the literal old-parent segment inserted by the exchange.
Consequently, in the finite displaced-component case the final carrier
contact is certified to lie on the selected owner's exposed parent.  This
is the provenance needed by the route-order protection argument; it is not
available from the generic segment exchange alone. -/
theorem SplitGroundedFreshRelevantForwardFirstHit.exists_componentExchangeWarp_to_initialFinish_with_terminalUpdate
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (initial state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (splice : SplitGroundedReducedForwardConflictSpliceData
      (L := L) (hL := hL) (hground := hground) (S := S)
      (K := ExchangeControls (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S))
      (ExchangeFrontier (L := L) (hL := hL) (S := S))
      state.parent state.rootPath state.deleted)
    (X : L.SplitGroundedFreshRelevantForwardFirstHit
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S)
      (ExchangeSources (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) state splice)
    (same_tail : splice.incomingTail = splice.contact.forwardEdge.1)
    (owner_eq : splice.contact.owner.1 = state.control.1)
    (same_parent : state.parent = initial.parent)
    (finish_beforeEq : GroundingCut.BeforeEq initial.parent
      state.rootPath.finish initial.rootPath.finish) :
    initial.parent ∈ GroundingSimultaneousDecode.exposedLadderPaths
        (L.splitGroundedPopularAuxiliaryInput hL.legal)
        (GroundingSimultaneousDecode.strongSelectedPath
          (ExchangeIndexed (L := L) (hL := hL) (hground := hground)) S
          (ExchangeControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S))
          (GroundingErasedDecode.chosenRequest splice.contact.owner.1)) ∧
      ∃ (segment : FinitePath Gamma.graph) (W : Set Gamma.DPath)
          (q : FinitePath Gamma.graph),
        segment.start = splice.incomingTail ∧
        segment.finish = initial.rootPath.finish ∧
        segment.support ⊆ initial.parent.support ∧
        segment.edgeSet ⊆ initial.parent.edgeSet ∧
        Gamma.IsWarp W ∧
        Gamma.initialSet W =
          ExchangeSources (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) ∧
        (Sum.inl q : Gamma.DPath) ∈ W ∧
        q.finish = initial.rootPath.finish ∧
        q.edgeSet ⊆
          ExchangeEdges (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∪
            initial.parent.edgeSet ∧
        initial.rootPath.finish ∈ Gamma.terminalFrontier W ∧
        ((∃ (old : FinitePath Gamma.graph) (contact : V),
            contact ∈ old.support ∧ contact ∈ initial.parent.support ∧
            contact ∈ segment.support ∧
            GroundingCut.BeforeEq initial.parent splice.incomingTail contact ∧
            old.start ∈ ExchangeSources
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∧
            old.edgeSet ⊆
              ExchangeEdges (L := L) (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S) ∧
            old.finish ∈ ExchangeSinkBoundary
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∧
            Gamma.terminalFrontier W = insert initial.rootPath.finish
              (ExchangeSinkBoundary
                (L := L) (hL := hL) (hground := hground)
                (hnotFresh := hnotFresh) (S := S) \ {old.finish})) ∨
          Gamma.terminalFrontier W = insert initial.rootPath.finish
            (ExchangeSinkBoundary
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S))) := by
  have howner : state.control = splice.contact.owner := by
    exact Subtype.ext owner_eq.symm
  have hexposed : initial.parent ∈
      GroundingSimultaneousDecode.exposedLadderPaths
      (L.splitGroundedPopularAuxiliaryInput hL.legal)
      (GroundingSimultaneousDecode.strongSelectedPath
        (ExchangeIndexed (L := L) (hL := hL) (hground := hground)) S
        (ExchangeControls (L := L) (hL := hL)
          (hground := hground) (hnotFresh := hnotFresh) (S := S))
        (GroundingErasedDecode.chosenRequest splice.contact.owner.1)) := by
    simpa only [← howner, ← same_parent] using state.parent_exposed
  have htailRoot : ∃ a ∈ ExchangeSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ExchangeEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a splice.incomingTail := by
    refine ⟨X.source, X.source_mem, ?_⟩
    exact X.conflictTail_rooted Set.sdiff_subset hNoEnter
      state splice same_tail
  have htailMem : splice.incomingTail ∈ state.rootPath.support :=
    (state.rootPath.edgeSet_subset_support_prod splice.incoming_mem).1
  have htailBeforeState : GroundingCut.BeforeEq state.parent
      splice.incomingTail state.rootPath.finish :=
    freshRelevantFiniteSubpath_mem_beforeEq_finish
      state.parent state.rootPath
      ⟨state.rootPath_support, state.rootPath_edges⟩ htailMem
  have htailBeforeInitial : GroundingCut.BeforeEq initial.parent
      splice.incomingTail state.rootPath.finish := by
    simpa only [same_parent] using htailBeforeState
  have htailBeforeFinish : GroundingCut.BeforeEq initial.parent
      splice.incomingTail initial.rootPath.finish :=
    GroundingFragmentResidualOrder.beforeEq_trans
      htailBeforeInitial finish_beforeEq
  obtain ⟨segment, hsegmentStart, hsegmentFinish, hsegmentEdges⟩ :
      ∃ segment : FinitePath Gamma.graph,
        segment.start = splice.incomingTail ∧
          segment.finish = initial.rootPath.finish ∧
          segment.edgeSet ⊆ initial.parent.edgeSet := by
    by_cases h : splice.incomingTail = initial.rootPath.finish
    · refine ⟨FinitePath.trivial Gamma.graph splice.incomingTail,
        FinitePath.trivial_start Gamma.graph splice.incomingTail, ?_, ?_⟩
      · simpa only [FinitePath.trivial_finish, h]
      · intro e he
        simp [FinitePath.edgeSet, FinitePath.trivial] at he
    · exact GroundingCutDecoder.exists_forward_segment_of_before
        ⟨htailBeforeFinish, h⟩
  have hfinishParent : initial.rootPath.finish ∈ initial.parent.support := by
    obtain ⟨_m, _n, _hm, hn, _hmn⟩ := htailBeforeFinish
    exact GroundingCut.occursAt_mem_support hn
  have hsegmentSupport : segment.support ⊆ initial.parent.support := by
    intro z hz
    by_cases hzFinish : z = segment.finish
    · simpa only [hzFinish, hsegmentFinish] using hfinishParent
    · obtain ⟨y, hzy⟩ :=
        _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          segment hz hzFinish
      exact (initial.parent.edgeSet_subset_support_prod
        (hsegmentEdges hzy)).1
  have hsegmentRoot : ∃ a ∈ ExchangeSources
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ExchangeEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a segment.start := by
    simpa only [hsegmentStart] using htailRoot
  obtain ⟨W, q, hW, hWInitial, hqW, hqFinish, hqEdges,
      hqTerminal, hterminalUpdate⟩ :=
    L.exists_splitGroundedFreshRelevantComponentExchangeWarp_of_segment_with_terminalUpdate
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) hNoEnter segment hsegmentRoot
  refine ⟨hexposed, segment, W, q, hsegmentStart, hsegmentFinish,
    hsegmentSupport, hsegmentEdges, hW, hWInitial, hqW,
    hqFinish.trans hsegmentFinish, hqEdges.trans ?_, ?_, ?_⟩
  · exact Set.union_subset_union Subset.rfl hsegmentEdges
  · simpa only [hsegmentFinish] using hqTerminal
  · rcases hterminalUpdate with hfinite | hray
    · left
      obtain ⟨old, contact, hcontactOld, hcontactSegment,
        holdInitial, holdEdges, holdFinish, hterminal⟩ := hfinite
      have hcontactOrder : GroundingCut.BeforeEq initial.parent
          splice.incomingTail contact := by
        simpa only [hsegmentStart] using
          freshRelevantFiniteSubpath_start_beforeEq_of_mem
            initial.parent segment ⟨hsegmentSupport, hsegmentEdges⟩
              hcontactSegment
      exact ⟨old, contact, hcontactOld, hsegmentSupport hcontactSegment,
        hcontactSegment, hcontactOrder, holdInitial, holdEdges, holdFinish, by
          simpa only [hsegmentFinish] using hterminal⟩
    · right
      simpa only [hsegmentFinish] using hray

/-- The native-frontier boundary-departure branch performs the same genuine
family exchange.  Its rooted incoming tail is retained, while the old
deleted edge is replaced by the parent suffix through the original failed
endpoint recorded by the normalization ancestry. -/
theorem exists_splitGroundedFreshRelevantBoundaryComponentExchangeWarp_to_initialFinish
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (initial state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (tail : V)
    (incoming_mem : (tail, state.deleted.head) ∈ state.rootPath.edgeSet)
    (rooted : ∃ a ∈ ExchangeSources
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ ExchangeEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a tail)
    (same_parent : state.parent = initial.parent)
    (finish_beforeEq : GroundingCut.BeforeEq initial.parent
      state.rootPath.finish initial.rootPath.finish) :
    ∃ (W : Set Gamma.DPath) (q : FinitePath Gamma.graph),
      Gamma.IsWarp W ∧
        Gamma.initialSet W =
          ExchangeSources (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S) ∧
        (Sum.inl q : Gamma.DPath) ∈ W ∧
        q.finish = initial.rootPath.finish ∧
        q.edgeSet ⊆
          ExchangeEdges (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S) ∪
            initial.parent.edgeSet ∧
        initial.rootPath.finish ∈ Gamma.terminalFrontier W := by
  have htailMem : tail ∈ state.rootPath.support :=
    (state.rootPath.edgeSet_subset_support_prod incoming_mem).1
  have htailBeforeState : GroundingCut.BeforeEq state.parent
      tail state.rootPath.finish :=
    freshRelevantFiniteSubpath_mem_beforeEq_finish
      state.parent state.rootPath
      ⟨state.rootPath_support, state.rootPath_edges⟩ htailMem
  have htailBeforeInitial : GroundingCut.BeforeEq initial.parent
      tail state.rootPath.finish := by
    simpa only [same_parent] using htailBeforeState
  have htailBeforeFinish : GroundingCut.BeforeEq initial.parent
      tail initial.rootPath.finish :=
    GroundingFragmentResidualOrder.beforeEq_trans
      htailBeforeInitial finish_beforeEq
  exact
    L.exists_splitGroundedFreshRelevantComponentExchangeWarp_of_rooted_beforeEq
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) hNoEnter initial.parent rooted htailBeforeFinish

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.exists_splitGroundedFreshRelevantComponentExchangeWarp_of_segment_with_terminalUpdate
#print axioms
  Erdos599.DWeb.KappaLadder.exists_splitGroundedFreshRelevantComponentExchangeWarp_of_segment
#print axioms
  Erdos599.DWeb.KappaLadder.exists_splitGroundedFreshRelevantComponentExchangeWarp_of_rooted_beforeEq
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantForwardFirstHit.exists_componentExchangeWarp
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantForwardFirstHit.exists_currentComponent_ending_at_finish
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantForwardFirstHit.exists_componentExchangeWarp_to_initialFinish
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantForwardFirstHit.exists_componentExchangeWarp_to_initialFinish_with_terminalUpdate
#print axioms
  Erdos599.DWeb.KappaLadder.exists_splitGroundedFreshRelevantBoundaryComponentExchangeWarp_to_initialFinish
