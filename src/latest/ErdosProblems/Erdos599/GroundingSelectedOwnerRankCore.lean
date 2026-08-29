/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReservedControls
import ErdosProblems.Erdos599.GroundingForwardTailClassification
import ErdosProblems.Erdos599.GroundingErasedCarrierRank

/-!
# Lightweight selected-owner rank orientation

This is the controls-generic incidence part of the selected-owner argument.
It deliberately avoids the legacy pre-stopped root-classification import:
the private-priority selector can therefore reuse the same chronological
orientation after adding one more countable avoidance requirement.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open Alternating PopularGroundingBridge PopularAuxiliary.Input
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- A route selected later in the request chronology has no backward link
on a limiting-ladder component exposed by an earlier selected route. -/
theorem selectedOwnerCore_later_no_backward
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r s : Request L S.cut)
    (hrs : GroundingAssembly.requestRank U S r <
      GroundingAssembly.requestRank U S s)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths L (strongSelectedPath U S K r))
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression U S K s).path.links)
    (hldir : l.direction = .backward) :
    ¬ l.path.IsSubpathOf Y := by
  intro hsub
  have hnonempty : l.path.edgeSet.Nonempty := by
    obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        l.path l.path.start_mem_support l.nontrivial
    exact ⟨(l.path.start, y), hy⟩
  obtain ⟨e, heLink⟩ := hnonempty
  have heDirection : e ∈
      (selectedErasedCompression U S K s).path.directionEdges .backward := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, heLink⟩
  obtain ⟨hePath, heOffApex⟩ :=
    DWeb.KappaLadder.selectedBackwardEdge_auxContact_offApex_split
      U S K s heDirection
  have heTrace : (LambdaVertex.edge e.1 e.2 : L.LV) ∈
      metLadderTrace L (strongSelectedPath U S K r) := by
    apply (mem_metLadderTrace_iff L
      (strongSelectedPath U S K r) (.edge e.1 e.2)).2
    exact ⟨Y, hY, Or.inr ⟨e, hsub.2 heLink, rfl⟩⟩
  exact Set.disjoint_left.1
    (strongSelectedPath_avoids_earlier_components U S K r s hrs)
    hePath ⟨heTrace, by
      simpa only [Set.mem_singleton_iff] using heOffApex⟩

/-- Control-rank form of `selectedOwnerCore_later_no_backward`. -/
theorem selectedOwnerCore_activeBackward_eq_or_rank_lt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V)
    (c d : ActiveControlRequestAt U S K T)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths L
      (strongSelectedPath U S K (chosenRequest c.1)))
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression U S K
      (chosenRequest d.1)).path.links)
    (hldir : l.direction = .backward)
    (hsub : l.path.IsSubpathOf Y) :
    d.1 = c.1 ∨ controlRank U S d.1 < controlRank U S c.1 := by
  rcases lt_trichotomy (controlRank U S d.1)
      (controlRank U S c.1) with hdc | heq | hcd
  · exact Or.inr hdc
  · exact Or.inl ((controlRank U S).injective heq)
  · exfalso
    exact selectedOwnerCore_later_no_backward
      U S K (chosenRequest c.1) (chosenRequest d.1) hcd
        Y hY l hl hldir hsub

/-- A forward edge of a later selected route cannot depart from a component
exposed by an earlier selected route. -/
theorem selectedOwnerCore_later_no_forwardTail
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful L)
    (r s : Request L S.cut)
    (hrs : GroundingAssembly.requestRank U S r <
      GroundingAssembly.requestRank U S s)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths L (strongSelectedPath U S K r))
    {b y : V}
    (hby : (b, y) ∈
      (selectedErasedCompression U S K s).path.directionEdges .forward)
    (hbY : b ∈ Y.support) : False := by
  let p := strongSelectedPath U S K s
  let q := strongSelectedPath U S K r
  have hpFan : p ∈
      (GroundingControlledAssembly.controlledRequestFan S K s).paths :=
    strongSelectedPath_mem_controlledRequestFan U S K s
  have hpStart : p.start ∈ L.lambda.source :=
    (GroundingControlledAssembly.controlledRequestFan S K s).starts_in_source
      hpFan
  have hYL : Y ∈ L.ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      hfaith q hY
  have hnoExit : b ≠ requestExit s := by
    intro hb
    exact selectedErasedCompression_noOutgoing_forward_at_requestExit
      U S K s ⟨y, by simpa only [hb] using hby⟩
  have holdOffApex : (LambdaVertex.old b : L.LV) ≠ requestAuxVertex s := by
    intro hApex
    apply hnoExit
    have hentry := congrArg L.gadgetEntry hApex
    simpa using hentry
  rcases
      GroundingForwardTailClassification.selectedForwardTail_old_or_edge_or_startingProxy
        U S K s hby with hold | hedge | hproxy
  · obtain ⟨d, hbd⟩ := hold
    have hbSupport : (LambdaVertex.old b : L.LV) ∈ p.support :=
      (p.edgeSet_subset_support_prod hbd).1
    have hbTrace : (LambdaVertex.old b : L.LV) ∈ metLadderTrace L q :=
      (mem_metLadderTrace_iff L q (.old b)).2
        ⟨Y, hY, Or.inl ⟨b, hbY, rfl⟩⟩
    exact Set.disjoint_left.1
      (strongSelectedPath_avoids_earlier_components U S K r s hrs)
      hbSupport ⟨hbTrace, by
        simpa only [Set.mem_singleton_iff] using holdOffApex⟩
  · obtain ⟨v, d, hvd⟩ := hedge
    have hedgeSupport : (LambdaVertex.edge b v : L.LV) ∈ p.support :=
      (p.edgeSet_subset_support_prod hvd).1
    have hbvFamily : (b, v) ∈ L.familyEdges :=
      L.edgeNode_mem_familyEdges_of_start_in_source p hpStart hedgeSupport
    obtain ⟨Z, hZL, hbvZ⟩ := hbvFamily
    have hZY : Z = Y :=
      Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
        hZL hYL (Z.edgeSet_subset_support_prod hbvZ).1 hbY
    have hbvY : (b, v) ∈ Y.edgeSet := hZY ▸ hbvZ
    have hedgeTrace : (LambdaVertex.edge b v : L.LV) ∈ metLadderTrace L q :=
      (mem_metLadderTrace_iff L q (.edge b v)).2
        ⟨Y, hY, Or.inr ⟨(b, v), hbvY, rfl⟩⟩
    have hedgeOffApex :
        (LambdaVertex.edge b v : L.LV) ≠ requestAuxVertex s := by
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
    have hproxyY : L.proxyPath i = Y :=
      Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
        (hfaith.1 i) hYL hbi hbY
    have hbTrace : (LambdaVertex.old b : L.LV) ∈ metLadderTrace L q :=
      (mem_metLadderTrace_iff L q (.old b)).2
        ⟨Y, hY, Or.inl ⟨b, hbY, rfl⟩⟩
    have hbProxyTrace : (LambdaVertex.old b : L.LV) ∈
        startingProxyTrace L p := by
      change (LambdaVertex.old b : L.LV) ∈
        startingProxyTrace L (strongSelectedPath U S K s)
      simp [startingProxyTrace, hstart, hproxyY,
        PopularSwitching.ladderTrace, hbY]
    apply strongSelectedPath_proxy_avoids_earlier_components
      U S K r s hrs
    rw [certifiedProxyComponentCollidingPaths, dif_pos hfaith]
    exact ⟨hpFan, .old b, ⟨hbTrace, by
      simpa only [Set.mem_singleton_iff] using holdOffApex⟩,
      hbProxyTrace⟩

/-- Rank orientation for a retained forward edge departing from an exposed
component, for an arbitrary control refinement. -/
theorem selectedOwnerCore_activeForwardTail_eq_or_rank_lt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V)
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful L)
    (c d : ActiveControlRequestAt U S K T)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths L
      (strongSelectedPath U S K (chosenRequest c.1)))
    {f : V × V}
    (hf : f ∈ retainedForwardEdgesAt T
      (selectedErasedCompression U S K (chosenRequest d.1)).path)
    (hftail : f.1 ∈ Y.support) :
    d.1 = c.1 ∨ controlRank U S d.1 < controlRank U S c.1 := by
  rcases lt_trichotomy (controlRank U S d.1)
      (controlRank U S c.1) with hdc | heq | hcd
  · exact Or.inr hdc
  · exact Or.inl ((controlRank U S).injective heq)
  · exfalso
    exact selectedOwnerCore_later_no_forwardTail
      U S K hfaith (chosenRequest c.1) (chosenRequest d.1) hcd
      Y hY (retainedForwardEdgesAt_subset_directionEdges T _ hf) hftail

end Erdos599

#print axioms Erdos599.selectedOwnerCore_activeBackward_eq_or_rank_lt
#print axioms Erdos599.selectedOwnerCore_activeForwardTail_eq_or_rank_lt
