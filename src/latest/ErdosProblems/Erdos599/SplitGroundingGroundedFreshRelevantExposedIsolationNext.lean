/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantBackwardNormalization
import ErdosProblems.Erdos599.GroundingSelectedOwnerRankCore

/-!
# Directional isolation of an exposed component

An exposed component need not be disjoint from every later selected route:
a later route may enter it at its own request apex.  The chronological
selector instead gives the exact directional isolation needed by the
last-contact exchange.  Earlier routes cannot meet a component from which
the current route has a retained forward departure.  Later routes cannot
depart forward from, or run backward along, a component exposed by the
current route.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open Alternating DirectedPath PopularGroundingBridge
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

private abbrev IsolationInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev IsolationIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev IsolationControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

/-- The exact component-attachment form of source condition (a).  If a
later selected route meets a limiting-ladder component exposed by an
earlier route, then that contact is the later route's own request apex.
Thus distinct selected routes can join their component clusters only by a
rank-oriented apex attachment; an off-apex contact with an already exposed
component is impossible. -/
theorem splitGroundedFreshRelevant_laterRoute_exposedContact_eq_apex
    (T : Set V)
    (c d : ActiveControlRequestAt
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) T)
    (hcd : controlRank
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S c.1 <
      controlRank
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S d.1)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (IsolationInput (L := L) (hL := hL))
      (strongSelectedPath
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)))
    {a : (IsolationInput (L := L) (hL := hL)).LV}
    (haRoute : a ∈ (strongSelectedPath
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (chosenRequest d.1)).support)
    (haY : a ∈ PopularSwitching.ladderTrace
      (IsolationInput (L := L) (hL := hL)) Y) :
    a = requestAuxVertex (chosenRequest d.1) := by
  let J := IsolationInput (L := L) (hL := hL)
  let U := IsolationIndexed (L := L) (hL := hL) (hground := hground)
  let K := IsolationControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  have haTrace : a ∈ metLadderTrace J
      (strongSelectedPath U S K (chosenRequest c.1)) :=
    (mem_metLadderTrace_iff J
      (strongSelectedPath U S K (chosenRequest c.1)) a).2
      ⟨Y, hY, haY⟩
  by_contra hne
  exact Set.disjoint_left.1
    (strongSelectedPath_avoids_earlier_components U S K
      (chosenRequest c.1) (chosenRequest d.1) hcd)
    haRoute ⟨haTrace, by
      simpa only [Set.mem_singleton_iff] using hne⟩

/-- Original-web form of the rank-ordered attachment rule.  Every vertex
where a later compressed selected route meets a component exposed by an
earlier route lies in the gadget carrier of the later route's own apex.
The proxy case uses the separately selected hidden starting component, so
the statement includes contacts not represented by a visible auxiliary
vertex of the compressed route. -/
theorem splitGroundedFreshRelevant_laterRoute_contact_exposedParent_mem_apexCarrier
    (T : Set V)
    (c d : ActiveControlRequestAt
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) T)
    (hcd : controlRank
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S c.1 <
      controlRank
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S d.1)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (IsolationInput (L := L) (hL := hL))
      (strongSelectedPath
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)))
    {x : V}
    (hxRoute : x ∈ (selectedErasedCompression
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (chosenRequest d.1)).path.vertexSet)
    (hxY : x ∈ Y.support) :
    x ∈ (IsolationInput (L := L) (hL := hL)).gadgetCarrier
      (requestAuxVertex (chosenRequest d.1)) := by
  let J := IsolationInput (L := L) (hL := hL)
  let U := IsolationIndexed (L := L) (hL := hL) (hground := hground)
  let K := IsolationControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let p := strongSelectedPath U S K (chosenRequest d.1)
  let q := strongSelectedPath U S K (chosenRequest c.1)
  have hfaith := L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL
  have hpFan : p ∈
      (GroundingControlledAssembly.controlledRequestFan S K
        (chosenRequest d.1)).paths :=
    strongSelectedPath_mem_controlledRequestFan U S K (chosenRequest d.1)
  have hpStart : p.start ∈ J.lambda.source :=
    (GroundingControlledAssembly.controlledRequestFan S K
      (chosenRequest d.1)).starts_in_source hpFan
  have hYL : Y ∈ J.ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      hfaith q hY
  have hxDecoded : x ∈ J.decodedVertexCarrier p :=
    GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      U S K (chosenRequest d.1) hxRoute
  simp only [PopularAuxiliary.Input.decodedVertexCarrier,
    Set.mem_iUnion] at hxDecoded
  obtain ⟨a, haPath, hxa⟩ := hxDecoded
  have apex_of_trace
      (haTrace : a ∈ PopularSwitching.ladderTrace J Y) :
      a = requestAuxVertex (chosenRequest d.1) := by
    exact L.splitGroundedFreshRelevant_laterRoute_exposedContact_eq_apex
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
      T c d hcd Y hY haPath haTrace
  cases a with
  | old z =>
      have hxz : x = z := by simpa [J, PopularAuxiliary.Input.gadgetCarrier] using hxa
      have haTrace : (PopularAuxiliary.Input.LambdaVertex.old z : J.LV) ∈
          PopularSwitching.ladderTrace J Y :=
        Or.inl ⟨z, hxz ▸ hxY, rfl⟩
      rw [apex_of_trace haTrace] at hxa
      exact hxa
  | edge z w =>
      have hzw : (z, w) ∈ J.familyEdges :=
        J.edgeNode_mem_familyEdges_of_start_in_source p hpStart haPath
      obtain ⟨Z, hZL, hzwZ⟩ := hzw
      have hxEnds : x = z ∨ x = w := by
        simpa [J, PopularAuxiliary.Input.gadgetCarrier, eq_comm] using hxa
      have hxZ : x ∈ Z.support := hxEnds.elim
        (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod hzwZ).1)
        (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod hzwZ).2)
      have hZY : Z = Y :=
        Alternating.DWeb.IsWarp.eq_of_mem_support J.ladder.disjoint
          hZL hYL hxZ hxY
      have haTrace : (PopularAuxiliary.Input.LambdaVertex.edge z w : J.LV) ∈
          PopularSwitching.ladderTrace J Y :=
        Or.inr ⟨(z, w), hZY ▸ hzwZ, rfl⟩
      rw [apex_of_trace haTrace] at hxa
      exact hxa
  | proxy i =>
      have hproxyL : J.proxyPath i ∈ J.ladder.paths := hfaith.1 i
      have hproxyY : J.proxyPath i = Y :=
        Alternating.DWeb.IsWarp.eq_of_mem_support J.ladder.disjoint
          hproxyL hYL (by
            simpa [J, PopularAuxiliary.Input.gadgetCarrier] using hxa) hxY
      have hxTrace : (PopularAuxiliary.Input.LambdaVertex.old x : J.LV) ∈
          metLadderTrace J q :=
        (mem_metLadderTrace_iff J q (.old x)).2
          ⟨Y, hY, Or.inl ⟨x, hxY, rfl⟩⟩
      have hxProxyTrace :
          (PopularAuxiliary.Input.LambdaVertex.old x : J.LV) ∈
            startingProxyTrace J p := by
        have hpStartProxy : p.start = PopularAuxiliary.Input.LambdaVertex.proxy i :=
          J.proxy_mem_support_eq_start p hpStart haPath
        simpa [startingProxyTrace, hpStartProxy,
          PopularSwitching.ladderTrace, hproxyY] using hxY
      by_cases hxApex :
          (PopularAuxiliary.Input.LambdaVertex.old x : J.LV) =
            requestAuxVertex (chosenRequest d.1)
      · rw [← hxApex]
        simp [PopularAuxiliary.Input.gadgetCarrier]
      · exfalso
        apply strongSelectedPath_proxy_avoids_earlier_components U S K
          (chosenRequest c.1) (chosenRequest d.1) hcd
        rw [certifiedProxyComponentCollidingPaths, dif_pos hfaith]
        exact ⟨hpFan, .old x, ⟨hxTrace, by
          simpa only [Set.mem_singleton_iff] using hxApex⟩, hxProxyTrace⟩

/-- On a ladder component carrying a request apex, every original vertex
represented by that apex gadget occurs weakly before the request vertex.
For an edge request this is precisely the represented ladder edge from its
tail to its head. -/
theorem requestApexCarrier_beforeEq_requestVertex_on_tracedPath
    (r : Request (IsolationInput (L := L) (hL := hL)) S.cut)
    (Y : Gamma.DPath)
    (hApex : requestAuxVertex r ∈ PopularSwitching.ladderTrace
      (IsolationInput (L := L) (hL := hL)) Y)
    {x : V}
    (hx : x ∈ (IsolationInput (L := L) (hL := hL)).gadgetCarrier
      (requestAuxVertex r)) :
    GroundingCut.BeforeEq Y x (requestVertex r) := by
  cases r with
  | inl old =>
      rcases hApex with hOld | hEdge
      · obtain ⟨z, hzY, hz⟩ := hOld
        have holdz : old.1 = z :=
          (PopularAuxiliary.Input.LambdaVertex.old.inj hz).symm
        have hxo : x = old.1 := by
          simpa [requestAuxVertex, PopularAuxiliary.Input.gadgetCarrier] using hx
        simpa [requestVertex, hxo, holdz] using
          (GroundingCut.beforeEq_refl hzY)
      · obtain ⟨e, _heY, he⟩ := hEdge
        cases he
  | inr edge =>
      rcases hApex with hOld | hEdge
      · obtain ⟨z, _hzY, hz⟩ := hOld
        cases hz
      · obtain ⟨e, heY, he⟩ := hEdge
        have htail : e.1 = edge.1.1 :=
          (PopularAuxiliary.Input.LambdaVertex.edge.inj he).1
        have hhead : e.2 = edge.1.2 :=
          (PopularAuxiliary.Input.LambdaVertex.edge.inj he).2
        have hxEnds : x = edge.1.1 ∨ x = edge.1.2 := by
          simpa [requestAuxVertex, PopularAuxiliary.Input.gadgetCarrier,
            eq_comm] using hx
        rcases hxEnds with hxtail | hxhead
        · simpa [requestVertex, hxtail, htail, hhead] using
            (GroundingCut.beforeEq_of_mem_edgeSet heY)
        · have hheadY : edge.1.2 ∈ Y.support := by
            simpa only [← hhead] using
              (Y.edgeSet_subset_support_prod heY).2
          simpa [requestVertex, hxhead] using
            (GroundingCut.beforeEq_refl hheadY)

/-- If the carrier of a request apex meets a genuine limiting-ladder path,
then that apex belongs to the path's ladder trace.  The edge-request case
uses the fact that an edge gadget on a source-starting auxiliary path names
an actual edge of the limiting warp. -/
theorem requestAuxVertex_mem_ladderTrace_of_apexCarrier_meets_ladderPath
    (r : Request (IsolationInput (L := L) (hL := hL)) S.cut)
    (p : FinitePath
      (IsolationInput (L := L) (hL := hL)).lambda.graph)
    (hpStart : p.start ∈
      (IsolationInput (L := L) (hL := hL)).lambda.source)
    (hApexPath : requestAuxVertex r ∈ p.support)
    (Y : Gamma.DPath)
    (hYL : Y ∈ (IsolationInput (L := L) (hL := hL)).ladder.paths)
    {x : V}
    (hxApex : x ∈
      (IsolationInput (L := L) (hL := hL)).gadgetCarrier
        (requestAuxVertex r))
    (hxY : x ∈ Y.support) :
    requestAuxVertex r ∈ PopularSwitching.ladderTrace
      (IsolationInput (L := L) (hL := hL)) Y := by
  let J := IsolationInput (L := L) (hL := hL)
  cases r with
  | inl old =>
      have hxo : x = old.1 := by
        simpa [requestAuxVertex, PopularAuxiliary.Input.gadgetCarrier] using
          hxApex
      exact Or.inl ⟨old.1, hxo ▸ hxY, rfl⟩
  | inr edge =>
      have heFamily : (edge.1.1, edge.1.2) ∈ J.familyEdges :=
        J.edgeNode_mem_familyEdges_of_start_in_source p hpStart
          (by simpa [requestAuxVertex] using hApexPath)
      obtain ⟨Z, hZL, heZ⟩ := heFamily
      have hxEnds : x = edge.1.1 ∨ x = edge.1.2 := by
        simpa [requestAuxVertex, PopularAuxiliary.Input.gadgetCarrier,
          eq_comm] using hxApex
      have hxZ : x ∈ Z.support := hxEnds.elim
        (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod heZ).1)
        (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod heZ).2)
      have hZY : Z = Y :=
        Alternating.DWeb.IsWarp.eq_of_mem_support J.ladder.disjoint
          hZL hYL hxZ hxY
      exact Or.inr ⟨(edge.1.1, edge.1.2), hZY ▸ heZ, rfl⟩

/-- Every actual original-web contact of a later selected route with an
earlier exposed parent supplies the literal later-apex attachment witness.
-/
theorem splitGroundedFreshRelevant_laterRoute_contact_exposedParent_apexTrace
    (T : Set V)
    (c d : ActiveControlRequestAt
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) T)
    (hcd : controlRank
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S c.1 <
      controlRank
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S d.1)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (IsolationInput (L := L) (hL := hL))
      (strongSelectedPath
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)))
    {x : V}
    (hxRoute : x ∈ (selectedErasedCompression
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (chosenRequest d.1)).path.vertexSet)
    (hxY : x ∈ Y.support) :
    requestAuxVertex (chosenRequest d.1) ∈
      PopularSwitching.ladderTrace
        (IsolationInput (L := L) (hL := hL)) Y := by
  let J := IsolationInput (L := L) (hL := hL)
  let U := IsolationIndexed (L := L) (hL := hL) (hground := hground)
  let K := IsolationControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let p := strongSelectedPath U S K (chosenRequest d.1)
  have hpStart : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source
      ⟨chosenRequest d.1, rfl⟩
  have hApexPath : requestAuxVertex (chosenRequest d.1) ∈ p.support := by
    rw [← strongSelectedPath_finish U S K (chosenRequest d.1)]
    exact p.finish_mem_support
  have hYL : Y ∈ J.ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
      (strongSelectedPath U S K (chosenRequest c.1)) hY
  have hxApex :=
    L.splitGroundedFreshRelevant_laterRoute_contact_exposedParent_mem_apexCarrier
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
      T c d hcd Y hY hxRoute hxY
  exact requestAuxVertex_mem_ladderTrace_of_apexCarrier_meets_ladderPath
    (L := L) (hL := hL) (S := S) (chosenRequest d.1) p hpStart
      hApexPath Y hYL hxApex hxY

/-- An active later route can attach at its apex to a component exposed by
an earlier active route only *before* every retained forward contact of the
earlier route on that component.  A weakly earlier retained contact would
make the later control inactive by definition.  This is the path-position
decrease paired with the control-rank decrease in the simultaneous
component forest. -/
theorem splitGroundedFreshRelevant_activeLaterApex_before_retainedForward
    (T : Set V)
    (c d : ActiveControlRequestAt
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) T)
    (hcd : controlRank
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S c.1 <
      controlRank
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S d.1)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (IsolationInput (L := L) (hL := hL))
      (strongSelectedPath
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)))
    (hApex : requestAuxVertex (chosenRequest d.1) ∈
      PopularSwitching.ladderTrace
        (IsolationInput (L := L) (hL := hL)) Y)
    {x : V}
    (hxRetained : x ∈ retainedForwardVerticesAt T
      (selectedErasedCompression
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)).path)
    (hxY : x ∈ Y.support) :
    GroundingCut.Before Y d.1.1 x := by
  let J := IsolationInput (L := L) (hL := hL)
  let U := IsolationIndexed (L := L) (hL := hL) (hground := hground)
  let K := IsolationControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  have hdY : d.1.1 ∈ Y.support := by
    simpa only [requestVertex_chosenRequest] using
      requestVertex_mem_support_of_requestAuxVertex_mem_ladderTrace
        (chosenRequest d.1) Y hApex
  have hnotBefore : ¬ GroundingCut.BeforeEq Y x d.1.1 := by
    intro hbefore
    exact (activeAt_not_hits_of_rank_lt U S K T c.2 d.2 hcd)
      ⟨Y, hY, hdY, x, hxRetained, hxY, hbefore⟩
  rcases GroundingCut.beforeEq_total hdY hxY with hdx | hxd
  · refine ⟨hdx, ?_⟩
    intro heq
    apply hnotBefore
    subst x
    exact GroundingCut.beforeEq_refl hdY
  · exact False.elim (hnotBefore hxd)

/-- The strict apex order persists along the exposed component after the
earlier retained contact.  Hence a suffix exchange beginning at such a
contact cannot delete a later active route's attachment point: that apex is
strictly on the retained prefix side of the cut. -/
theorem splitGroundedFreshRelevant_activeLaterApex_before_of_retainedForward_beforeEq
    (T : Set V)
    (c d : ActiveControlRequestAt
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) T)
    (hcd : controlRank
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S c.1 <
      controlRank
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S d.1)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (IsolationInput (L := L) (hL := hL))
      (strongSelectedPath
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)))
    (hApex : requestAuxVertex (chosenRequest d.1) ∈
      PopularSwitching.ladderTrace
        (IsolationInput (L := L) (hL := hL)) Y)
    {x z : V}
    (hxRetained : x ∈ retainedForwardVerticesAt T
      (selectedErasedCompression
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)).path)
    (hxY : x ∈ Y.support)
    (hxz : GroundingCut.BeforeEq Y x z) :
    GroundingCut.Before Y d.1.1 z := by
  have hdx := L.splitGroundedFreshRelevant_activeLaterApex_before_retainedForward
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
    T c d hcd Y hY hApex hxRetained hxY
  refine ⟨GroundingFragmentResidualOrder.beforeEq_trans hdx.1 hxz, ?_⟩
  intro hdz
  subst z
  exact hdx.2
    (GroundingCutDecoder.beforeEq_antisymm hdx.1 hxz)

/-- Every original vertex in a later active route's apex gadget lies
strictly before an earlier active route's retained forward contact on the
shared exposed component.  This is the original-web cut-side statement
used by the simultaneous switch. -/
theorem splitGroundedFreshRelevant_laterApexCarrier_before_retainedForward
    (T : Set V)
    (c d : ActiveControlRequestAt
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) T)
    (hcd : controlRank
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S c.1 <
      controlRank
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S d.1)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (IsolationInput (L := L) (hL := hL))
      (strongSelectedPath
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)))
    (hApex : requestAuxVertex (chosenRequest d.1) ∈
      PopularSwitching.ladderTrace
        (IsolationInput (L := L) (hL := hL)) Y)
    {x y : V}
    (hxApex : x ∈ (IsolationInput (L := L) (hL := hL)).gadgetCarrier
      (requestAuxVertex (chosenRequest d.1)))
    (hyRetained : y ∈ retainedForwardVerticesAt T
      (selectedErasedCompression
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)).path)
    (hyY : y ∈ Y.support) :
    GroundingCut.Before Y x y := by
  have hxd := requestApexCarrier_beforeEq_requestVertex_on_tracedPath
    (L := L) (hL := hL) (S := S) (chosenRequest d.1) Y hApex hxApex
  have hxd' : GroundingCut.BeforeEq Y x d.1.1 := by
    simpa only [requestVertex_chosenRequest] using hxd
  have hdy := L.splitGroundedFreshRelevant_activeLaterApex_before_retainedForward
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
    T c d hcd Y hY hApex hyRetained hyY
  refine ⟨GroundingFragmentResidualOrder.beforeEq_trans hxd' hdy.1, ?_⟩
  intro hxy
  subst y
  exact hdy.2 (GroundingCutDecoder.beforeEq_antisymm hdy.1 hxd')

/-- If the current route has a retained forward departure from an exposed
component, every strictly earlier active route has decoded carrier disjoint
from that component. -/
theorem splitGroundedFreshRelevant_earlierRoute_disjoint_forwardExposedParent
    (T : Set V)
    (c d : ActiveControlRequestAt
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) T)
    (hdc : controlRank
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S d.1 <
      controlRank
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S c.1)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (IsolationInput (L := L) (hL := hL))
      (strongSelectedPath
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)))
    {f : V × V}
    (hf : f ∈ retainedForwardEdgesAt T
      (selectedErasedCompression
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)).path)
    (hftail : f.1 ∈ Y.support) :
    Disjoint
      ((IsolationInput (L := L) (hL := hL)).decodedVertexCarrier
        (strongSelectedPath
          (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
          (IsolationControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (chosenRequest d.1)))
      Y.support := by
  let J := IsolationInput (L := L) (hL := hL)
  let U := IsolationIndexed (L := L) (hL := hL) (hground := hground)
  let K := IsolationControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let pd := strongSelectedPath U S K (chosenRequest d.1)
  have hdStart : pd.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨chosenRequest d.1, rfl⟩
  have hYL : Y ∈ J.ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
      (strongSelectedPath U S K (chosenRequest c.1)) hY
  rw [Set.disjoint_left]
  intro x hxd hxY
  have hYd : Y ∈ exposedLadderPaths J pd :=
    J.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
      pd hdStart hYL hxd hxY
  rcases selectedOwnerCore_activeForwardTail_eq_or_rank_lt
      U S K T (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
      d c Y hYd hf hftail with heq | hcd
  · exact (ne_of_lt hdc) (congrArg (controlRank U S) heq.symm)
  · exact (not_lt_of_ge (le_of_lt hdc)) hcd

/-- A later active route cannot have a retained forward departure from a
component exposed by the current route. -/
theorem splitGroundedFreshRelevant_laterRoute_no_forwardTail_exposedParent
    (T : Set V)
    (c d : ActiveControlRequestAt
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) T)
    (hcd : controlRank
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S c.1 <
      controlRank
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S d.1)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (IsolationInput (L := L) (hL := hL))
      (strongSelectedPath
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)))
    {b y : V}
    (hby : (b, y) ∈
      (selectedErasedCompression
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest d.1)).path.directionEdges .forward)
    (hbY : b ∈ Y.support) : False := by
  exact selectedOwnerCore_later_no_forwardTail
    (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
    (IsolationControls (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
    (chosenRequest c.1) (chosenRequest d.1) hcd Y hY hby hbY

/-- A later active route cannot contain a backward link on a component
exposed by the current route. -/
theorem splitGroundedFreshRelevant_laterRoute_no_backward_exposedParent
    (T : Set V)
    (c d : ActiveControlRequestAt
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) T)
    (hcd : controlRank
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S c.1 <
      controlRank
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S d.1)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths
      (IsolationInput (L := L) (hL := hL))
      (strongSelectedPath
        (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
        (IsolationControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)))
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
      (IsolationControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S))
      (chosenRequest d.1)).path.links)
    (hldir : l.direction = .backward)
    (hsub : l.path.IsSubpathOf Y) : False := by
  exact selectedOwnerCore_later_no_backward
    (IsolationIndexed (L := L) (hL := hL) (hground := hground)) S
    (IsolationControls (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (chosenRequest c.1) (chosenRequest d.1) hcd Y hY l hl hldir hsub

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_laterRoute_exposedContact_eq_apex
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_laterRoute_contact_exposedParent_mem_apexCarrier
#print axioms
  Erdos599.DWeb.KappaLadder.requestApexCarrier_beforeEq_requestVertex_on_tracedPath
#print axioms
  Erdos599.DWeb.KappaLadder.requestAuxVertex_mem_ladderTrace_of_apexCarrier_meets_ladderPath
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_laterRoute_contact_exposedParent_apexTrace
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_activeLaterApex_before_retainedForward
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_activeLaterApex_before_of_retainedForward_beforeEq
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_laterApexCarrier_before_retainedForward
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_earlierRoute_disjoint_forwardExposedParent
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_laterRoute_no_forwardTail_exposedParent
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_laterRoute_no_backward_exposedParent
