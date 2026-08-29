/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingAnchors
import ErdosProblems.Erdos599.GroundingErasedCarrierRank

/-!
# Owner orientation for fresh-avoiding root anchors

The fresh-avoiding anchor module produces a literal last deleted edge on a
limiting-ladder parent.  The strong request recursion orders every selected
route which can own that deletion.  This file records the resulting four
positive cases: a represented-cut edge, a backward owner, a same-tail
forward divergence, or a retained forward head.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev FreshOwnerInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev FreshOwnerIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev FreshOwnerControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev FreshOwnerEdges :=
  L.splitGroundedFreshAvoidingCanonicalEdges hL hground hnotFresh S

/-- Owner-oriented form of a deleted edge on a parent exposed by one
active fresh-avoiding request. -/
inductive SplitGroundedFreshAvoidingDeletedOwnerOutcome
    (c : ActiveControlRequestAt
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (Y : Gamma.DPath) {p : FinitePath Gamma.graph}
    (D : LastDeletedHead p
      (FreshOwnerEdges (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))) : Prop
  | cut
      (u : V) (parent_edge : (u, D.head) ∈ p.edgeSet)
      (cut_edge : (u, D.head) ∈ GroundingCut.CE
        (FreshOwnerInput (L := L) (hL := hL)) S.cut)
  | backward
      (u : V)
      (d : ActiveControlRequestAt
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅)
      (l : Link Gamma.graph) (parent : Gamma.DPath)
      (parent_edge : (u, D.head) ∈ p.edgeSet)
      (selected_edge : (u, D.head) ∈ erasedSelectedDirectionEdgesAt
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅ .backward)
      (link_mem : l ∈ (selectedErasedCompression
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest d.1)).path.links)
      (direction : l.direction = .backward)
      (link_edge : (u, D.head) ∈ l.path.edgeSet)
      (parent_mem : parent ∈
        (FreshOwnerInput (L := L) (hL := hL)).ladder.paths)
      (subpath : l.path.IsSubpathOf parent)
      (parent_eq : parent = Y)
      (owner_rank : d.1 = c.1 ∨
        controlRank
          (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
          d.1 < controlRank
            (FreshOwnerIndexed (L := L) (hL := hL)
              (hground := hground)) S c.1)
  | forwardTail
      (u : V)
      (d : ActiveControlRequestAt
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅)
      (f : V × V)
      (parent_edge : (u, D.head) ∈ p.edgeSet)
      (conflict : (u, D.head) ∈ forwardConflictCutEdgesAt
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅)
      (retained : f ∈ retainedForwardEdgesAt ∅
        (selectedErasedCompression
          (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (chosenRequest d.1)).path)
      (same_tail : u = f.1)
      (owner_rank : d.1 = c.1 ∨
        controlRank
          (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
          d.1 < controlRank
            (FreshOwnerIndexed (L := L) (hL := hL)
              (hground := hground)) S c.1)
  | retainedHead
      (u : V)
      (d : ActiveControlRequestAt
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅)
      (f : V × V)
      (parent_edge : (u, D.head) ∈ p.edgeSet)
      (conflict : (u, D.head) ∈ forwardConflictCutEdgesAt
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅)
      (retained : f ∈ retainedForwardEdgesAt ∅
        (selectedErasedCompression
          (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (chosenRequest d.1)).path)
      (head_eq : D.head = f.2)

/-- A later request cannot own a backward link on a component exposed by
an earlier request.  This is the only rank fact needed by the recursive
backward-anchor normalization; same-tail forward divergence is a terminal
exchange outcome and deliberately carries no recursive rank premise. -/
private theorem later_no_backward_on_exposed
    (r s : Request (FreshOwnerInput (L := L) (hL := hL)) S.cut)
    (hrs : GroundingAssembly.requestRank
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S r <
      GroundingAssembly.requestRank
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S s)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (FreshOwnerInput (L := L) (hL := hL))
      (strongSelectedPath
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) r))
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) s).path.links)
    (hldir : l.direction = .backward) :
    ¬ l.path.IsSubpathOf Y := by
  intro hsub
  have hnonempty : l.path.edgeSet.Nonempty := by
    obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        l.path l.path.start_mem_support l.nontrivial
    exact ⟨(l.path.start, y), hy⟩
  obtain ⟨e, heLink⟩ := hnonempty
  have heDirection : e ∈ (selectedErasedCompression
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) s).path.directionEdges
          .backward := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, heLink⟩
  obtain ⟨hePath, heOffApex⟩ :=
    selectedBackwardEdge_auxContact_offApex_split
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) s heDirection
  have heTrace : (PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2 :
      (FreshOwnerInput (L := L) (hL := hL)).LV) ∈
      metLadderTrace
        (FreshOwnerInput (L := L) (hL := hL))
        (strongSelectedPath
          (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) r) := by
    apply (mem_metLadderTrace_iff
      (FreshOwnerInput (L := L) (hL := hL))
      (strongSelectedPath
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) r)
      (.edge e.1 e.2)).2
    exact ⟨Y, hY, Or.inr ⟨e, hsub.2 heLink, rfl⟩⟩
  exact Set.disjoint_left.1
    (strongSelectedPath_avoids_earlier_components
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) r s hrs)
    hePath ⟨heTrace, by
      simpa only [Set.mem_singleton_iff] using heOffApex⟩

/-- A later fresh-avoiding request cannot retain a forward edge whose tail
lies on a ladder component exposed by an earlier request. -/
private theorem later_no_forwardTail_on_exposed
    (r s : Request (FreshOwnerInput (L := L) (hL := hL)) S.cut)
    (hrs : GroundingAssembly.requestRank
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S r <
      GroundingAssembly.requestRank
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S s)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (FreshOwnerInput (L := L) (hL := hL))
      (strongSelectedPath
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) r))
    {b y : V}
    (hby : (b, y) ∈
      (selectedErasedCompression
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) s).path.directionEdges .forward)
    (hbY : b ∈ Y.support) : False := by
  let U := FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)
  let K := FreshOwnerControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let J := FreshOwnerInput (L := L) (hL := hL)
  let p := strongSelectedPath U S K s
  let q := strongSelectedPath U S K r
  have hpFan : p ∈
      (GroundingControlledAssembly.controlledRequestFan S K s).paths :=
    strongSelectedPath_mem_controlledRequestFan U S K s
  have hpStart : p.start ∈ J.lambda.source :=
    (GroundingControlledAssembly.controlledRequestFan S K s).starts_in_source
      hpFan
  have hYL : Y ∈ J.ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL) q hY
  have hnoExit : b ≠ requestExit s := by
    intro hb
    exact selectedErasedCompression_noOutgoing_forward_at_requestExit
      U S K s ⟨y, by simpa only [hb] using hby⟩
  have holdOffApex : (PopularAuxiliary.Input.LambdaVertex.old b : J.LV) ≠
      requestAuxVertex s := by
    intro hApex
    apply hnoExit
    have hentry := congrArg J.gadgetEntry hApex
    simpa using hentry
  rcases
      GroundingForwardTailClassification.selectedForwardTail_old_or_edge_or_startingProxy
        U S K s hby with hold | hedge | hproxy
  · obtain ⟨d, hbd⟩ := hold
    have hbSupport : (PopularAuxiliary.Input.LambdaVertex.old b : J.LV) ∈
        p.support := (p.edgeSet_subset_support_prod hbd).1
    have hbTrace : (PopularAuxiliary.Input.LambdaVertex.old b : J.LV) ∈
        metLadderTrace J q :=
      (mem_metLadderTrace_iff J q (.old b)).2
        ⟨Y, hY, Or.inl ⟨b, hbY, rfl⟩⟩
    exact Set.disjoint_left.1
      (strongSelectedPath_avoids_earlier_components U S K r s hrs)
        hbSupport ⟨hbTrace, by
          simpa only [Set.mem_singleton_iff] using holdOffApex⟩
  · obtain ⟨v, d, hvd⟩ := hedge
    have hedgeSupport :
        (PopularAuxiliary.Input.LambdaVertex.edge b v : J.LV) ∈ p.support :=
      (p.edgeSet_subset_support_prod hvd).1
    have hbvFamily : (b, v) ∈ J.familyEdges :=
      J.edgeNode_mem_familyEdges_of_start_in_source p hpStart hedgeSupport
    obtain ⟨Z, hZL, hbvZ⟩ := hbvFamily
    have hZY : Z = Y :=
      Alternating.DWeb.IsWarp.eq_of_mem_support J.ladder.disjoint
        hZL hYL (Z.edgeSet_subset_support_prod hbvZ).1 hbY
    have hbvY : (b, v) ∈ Y.edgeSet := hZY ▸ hbvZ
    have hedgeTrace :
        (PopularAuxiliary.Input.LambdaVertex.edge b v : J.LV) ∈
          metLadderTrace J q :=
      (mem_metLadderTrace_iff J q (.edge b v)).2
        ⟨Y, hY, Or.inr ⟨(b, v), hbvY, rfl⟩⟩
    have hedgeOffApex :
        (PopularAuxiliary.Input.LambdaVertex.edge b v : J.LV) ≠
          requestAuxVertex s := by
      intro hApex
      have hfinish : p.finish = requestAuxVertex s :=
        strongSelectedPath_finish U S K s
      exact (Alternating.FinitePath.source_ne_finish_of_mem_edgeSet p hvd)
        (hApex.trans hfinish.symm)
    exact Set.disjoint_left.1
      (strongSelectedPath_avoids_earlier_components U S K r s hrs)
        hedgeSupport ⟨hedgeTrace, by
          simpa only [Set.mem_singleton_iff] using hedgeOffApex⟩
  · obtain ⟨i, d, hstart, hid, hbi⟩ := hproxy
    have hproxyY : J.proxyPath i = Y :=
      Alternating.DWeb.IsWarp.eq_of_mem_support J.ladder.disjoint
        ((L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL).1 i)
        hYL hbi hbY
    have hbTrace : (PopularAuxiliary.Input.LambdaVertex.old b : J.LV) ∈
        metLadderTrace J q :=
      (mem_metLadderTrace_iff J q (.old b)).2
        ⟨Y, hY, Or.inl ⟨b, hbY, rfl⟩⟩
    have hbProxyTrace : (PopularAuxiliary.Input.LambdaVertex.old b : J.LV) ∈
        startingProxyTrace J p := by
      change (PopularAuxiliary.Input.LambdaVertex.old b : J.LV) ∈
        startingProxyTrace J (strongSelectedPath U S K s)
      simp [startingProxyTrace, hstart, hproxyY,
        PopularSwitching.ladderTrace, hbY]
    apply strongSelectedPath_proxy_avoids_earlier_components U S K r s hrs
    rw [certifiedProxyComponentCollidingPaths,
      dif_pos (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)]
    exact ⟨hpFan, .old b, ⟨hbTrace, by
      simpa only [Set.mem_singleton_iff] using holdOffApex⟩, hbProxyTrace⟩

/-- Public control-rank orientation for a retained forward edge departing
from a component exposed by another active fresh-avoiding control. -/
theorem splitGroundedFreshAvoiding_forwardTailOwner_eq_or_rank_lt
    (c d : ActiveControlRequestAt
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (FreshOwnerInput (L := L) (hL := hL))
      (strongSelectedPath
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) (chosenRequest c.1)))
    {f : V × V}
    (hf : f ∈ retainedForwardEdgesAt ∅
      (selectedErasedCompression
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest d.1)).path)
    (hftail : f.1 ∈ Y.support) :
    d.1 = c.1 ∨
      controlRank
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        d.1 < controlRank
          (FreshOwnerIndexed (L := L) (hL := hL)
            (hground := hground)) S c.1 := by
  rcases lt_trichotomy
      (controlRank
        (FreshOwnerIndexed (L := L) (hL := hL)
          (hground := hground)) S d.1)
      (controlRank
        (FreshOwnerIndexed (L := L) (hL := hL)
          (hground := hground)) S c.1) with hdc | heq | hcd
  · exact Or.inr hdc
  · exact Or.inl ((controlRank
      (FreshOwnerIndexed (L := L) (hL := hL)
        (hground := hground)) S).injective heq)
  · exfalso
    exact later_no_forwardTail_on_exposed
      (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)
      (chosenRequest c.1) (chosenRequest d.1) hcd Y hY
      (retainedForwardEdgesAt_subset_directionEdges ∅ _ hf) hftail

/-- Generic owner orientation, specialized only to the grounded split input
and the fresh-avoiding controls. -/
theorem splitGroundedFreshAvoiding_deletedOwnerOutcome
    (c : ActiveControlRequestAt
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (FreshOwnerInput (L := L) (hL := hL))
      (strongSelectedPath
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) (chosenRequest c.1)))
    {p : FinitePath Gamma.graph} (hpY : p.edgeSet ⊆ Y.edgeSet)
    (D : LastDeletedHead p
      (FreshOwnerEdges (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)))
    (hclass :
      (∃ u, (u, D.head) ∈ p.edgeSet ∧
        (u, D.head) ∈ GroundingCut.CE
          (FreshOwnerInput (L := L) (hL := hL)) S.cut) ∨
      (∃ u, (u, D.head) ∈ p.edgeSet ∧
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) ∅ .backward) ∨
      (∃ u, (u, D.head) ∈ p.edgeSet ∧
        (u, D.head) ∈ forwardConflictCutEdgesAt
          (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) ∅)) :
    L.SplitGroundedFreshAvoidingDeletedOwnerOutcome
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      c Y D := by
  rcases hclass with hcut | hbackward | hconflict
  · obtain ⟨u, huParent, huCut⟩ := hcut
    exact .cut u huParent huCut
  · obtain ⟨u, huParent, huBackward⟩ := hbackward
    simp only [erasedSelectedDirectionEdgesAt, Set.mem_iUnion] at huBackward
    obtain ⟨d, hed⟩ := huBackward
    simp only [AltPath.directionEdges, Set.mem_iUnion] at hed
    obtain ⟨l, hl, hldir, hel⟩ := hed
    obtain ⟨parent, hparent, hsub⟩ :=
      selectedErasedCompression_backwardLinksOn
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest d.1) l hl hldir
    have huBackward : (u, D.head) ∈ erasedSelectedDirectionEdgesAt
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅ .backward := by
      simp only [erasedSelectedDirectionEdgesAt, Set.mem_iUnion]
      exact ⟨d, by
        simp only [AltPath.directionEdges, Set.mem_iUnion]
        exact ⟨l, hl, hldir, hel⟩⟩
    have hYL : Y ∈ (FreshOwnerInput (L := L) (hL := hL)).ladder.paths :=
      GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
        (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL) _ hY
    have heParent : (u, D.head) ∈ parent.edgeSet := hsub.2 hel
    have hparentY : parent = Y :=
      Alternating.DWeb.IsWarp.eq_of_mem_support
        (FreshOwnerInput (L := L) (hL := hL)).ladder.disjoint
        hparent hYL
        (parent.edgeSet_subset_support_prod heParent).1
        (Y.edgeSet_subset_support_prod (hpY huParent)).1
    have hrank : d.1 = c.1 ∨
        controlRank
          (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
          d.1 < controlRank
            (FreshOwnerIndexed (L := L) (hL := hL)
              (hground := hground)) S c.1 := by
      rcases lt_trichotomy
          (controlRank
            (FreshOwnerIndexed (L := L) (hL := hL)
              (hground := hground)) S d.1)
          (controlRank
            (FreshOwnerIndexed (L := L) (hL := hL)
              (hground := hground)) S c.1) with hdc | heq | hcd
      · exact Or.inr hdc
      · exact Or.inl ((controlRank
          (FreshOwnerIndexed (L := L) (hL := hL)
            (hground := hground)) S).injective heq)
      · exfalso
        apply later_no_backward_on_exposed
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)
          (chosenRequest c.1) (chosenRequest d.1) hcd Y hY l hl hldir
        simpa only [hparentY] using hsub
    exact .backward u d l parent huParent huBackward hl hldir hel
      hparent hsub hparentY hrank
  · obtain ⟨u, huParent, huConflict⟩ := hconflict
    obtain ⟨_huResidual, f, hf, htail | hhead⟩ := huConflict
    · simp only [erasedSelectedRetainedForwardEdgesAt, Set.mem_iUnion] at hf
      obtain ⟨d, hfd⟩ := hf
      have hrank :=
        L.splitGroundedFreshAvoiding_forwardTailOwner_eq_or_rank_lt
          (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) c d Y hY hfd (by
            rw [← htail]
            exact (Y.edgeSet_subset_support_prod (hpY huParent)).1)
      exact .forwardTail u d f huParent
        ⟨_huResidual, f, by
          simp only [erasedSelectedRetainedForwardEdgesAt, Set.mem_iUnion]
          exact ⟨d, hfd⟩, Or.inl htail⟩
        hfd htail hrank
    · simp only [erasedSelectedRetainedForwardEdgesAt, Set.mem_iUnion] at hf
      obtain ⟨d, hfd⟩ := hf
      exact .retainedHead u d f huParent
        ⟨_huResidual, f, by
          simp only [erasedSelectedRetainedForwardEdgesAt, Set.mem_iUnion]
          exact ⟨d, hfd⟩, Or.inr hhead⟩
        hfd hhead

/-- The parent supporting an initial fresh-avoiding anchor is one of the
ladder components exposed by that selected request. -/
theorem SplitGroundedFreshAvoidingInitialDeletedData.parent_exposed
    (c : ActiveControlRequestAt
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (data : L.SplitGroundedFreshAvoidingInitialDeletedData
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (chosenRequest c.1)) :
    data.parent ∈ exposedLadderPaths
      (FreshOwnerInput (L := L) (hL := hL))
      (strongSelectedPath
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) (chosenRequest c.1)) := by
  let U := FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)
  let K := FreshOwnerControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let r := chosenRequest c.1
  have hpStart : (strongSelectedPath U S K r).start ∈
      (FreshOwnerInput (L := L) (hL := hL)).lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩
  have hinitialCarrier : (selectedRequestTrace U S K r).initial ∈
      (FreshOwnerInput (L := L) (hL := hL)).decodedVertexCarrier
        (strongSelectedPath U S K r) := by
    apply GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      U S K r
    exact Set.mem_of_eq_of_mem
      (selectedErasedCompression U S K r).initial_eq.symm
      (selectedErasedCompression U S K r).path.initial_mem_vertexSet
  have hinitialParent : (selectedRequestTrace U S K r).initial ∈
      data.parent.support := by
    rw [← data.rootPath_finish]
    exact data.rootPath_support data.rootPath.finish_mem_support
  exact (FreshOwnerInput (L := L) (hL := hL))
    |>.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
      (strongSelectedPath U S K r) hpStart data.parent_inessential.1
      hinitialCarrier hinitialParent

/-- Owner orientation of the deleted edge on an active selected-initial
prefix. -/
theorem SplitGroundedFreshAvoidingInitialDeletedData.ownerOutcome
    (c : ActiveControlRequestAt
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (data : L.SplitGroundedFreshAvoidingInitialDeletedData
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (chosenRequest c.1)) :
    L.SplitGroundedFreshAvoidingDeletedOwnerOutcome
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      c data.parent data.deleted := by
  exact L.splitGroundedFreshAvoiding_deletedOwnerOutcome c data.parent
    (data.parent_exposed c) data.rootPath_edges
    data.deleted data.deleted_class

/-- A limiting-ladder parent supporting a selected backward link is exposed
by the request which contains that link. -/
theorem splitGroundedFreshAvoiding_backwardParent_exposed
    (c : ActiveControlRequestAt
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (chosenRequest c.1)).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent) :
    parent ∈ exposedLadderPaths
      (FreshOwnerInput (L := L) (hL := hL))
      (strongSelectedPath
        (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) (chosenRequest c.1)) := by
  have hnonempty : l.path.edgeSet.Nonempty := by
    obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        l.path l.path.start_mem_support l.nontrivial
    exact ⟨(l.path.start, y), hy⟩
  obtain ⟨e, heLink⟩ := hnonempty
  have heDirection : e ∈ (selectedErasedCompression
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (chosenRequest c.1)).path.directionEdges .backward := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, heLink⟩
  have hePath := (selectedBackwardEdge_auxContact_offApex_split
    (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
    (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (chosenRequest c.1) heDirection).1
  left
  refine ⟨?_, PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2,
    hePath, Or.inr ⟨e, hsub.2 heLink, rfl⟩⟩
  simpa only [splitGroundedPopularAuxiliaryInput, limitWarp] using hparent

/-- Owner orientation of the deleted edge on an active backward-owner
prefix. -/
theorem SplitGroundedFreshAvoidingBackwardDeletedData.ownerOutcome
    (c : ActiveControlRequestAt
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅)
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (FreshOwnerIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshOwnerControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (chosenRequest c.1)).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath)
    (hsub : l.path.IsSubpathOf parent)
    (data : L.SplitGroundedFreshAvoidingBackwardDeletedData
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (chosenRequest c.1) l parent) :
    L.SplitGroundedFreshAvoidingDeletedOwnerOutcome
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      c parent data.deleted := by
  exact L.splitGroundedFreshAvoiding_deletedOwnerOutcome c parent
    (L.splitGroundedFreshAvoiding_backwardParent_exposed c l hl hldir
      parent data.parent_mem hsub)
    data.rootPath_edges data.deleted data.deleted_class

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshAvoidingInitialDeletedData.ownerOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshAvoidingBackwardDeletedData.ownerOutcome
