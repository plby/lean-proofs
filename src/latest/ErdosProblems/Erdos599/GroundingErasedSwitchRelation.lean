/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedDecode
import ErdosProblems.Erdos599.GroundingDecodedCarrier

/-!
# Vertex provenance for the erased Section 8 switch

Loop erasure only deletes signed steps.  Consequently every endpoint of an
edge retained by an erased compression still comes from a gadget visited by
the underlying auxiliary path.  This file records that fact without making
the false stronger claim that two equal projected vertices must come from
the same raw signed edge.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath Alternating

universe u

namespace PopularAuxiliary.Input

variable {V I : Type u} {Gamma : DWeb V}
variable (L : PopularAuxiliary.Input Gamma I)

theorem mem_gadgetCarrier_of_gadgetEntry
    {a : L.LV} {x : V} (h : L.gadgetEntry a = some x) :
    x ∈ L.gadgetCarrier a := by
  cases a <;> simp_all [gadgetCarrier]

theorem mem_gadgetCarrier_of_gadgetExit
    {a : L.LV} {x : V} (h : L.gadgetExit a = some x) :
    x ∈ L.gadgetCarrier a := by
  cases a <;> simp_all [gadgetCarrier]

theorem ForwardConnector.endpoints_mem_gadgetCarrier
    {a b : L.LV} {x y : V} (h : L.ForwardConnector a b x y) :
    x ∈ L.gadgetCarrier a ∧ y ∈ L.gadgetCarrier b := by
  constructor
  · rcases h.1 with hExit | ⟨i, rfl, hx⟩
    · exact L.mem_gadgetCarrier_of_gadgetExit hExit
    · simpa using hx
  · exact L.mem_gadgetCarrier_of_gadgetEntry h.2.1

theorem gadgetCarrier_subset_decodedVertexCarrier
    (p : FinitePath L.lambda.graph) {a : L.LV}
    (ha : a ∈ p.support) :
    L.gadgetCarrier a ⊆ L.decodedVertexCarrier p := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hx⟩⟩

/-- Both endpoints of every raw decoded edge are represented by gadgets of
the auxiliary path.  This is the collision-classification interface used by
the simultaneous switch: it is endpoint based and therefore remains valid
after chronological loop erasure. -/
theorem decodedRouteEdge_endpoints_mem_decodedVertexCarrier
    (p : FinitePath L.lambda.graph) {e : V × V}
    (he : e ∈ L.decodedRouteEdges p) :
    e.1 ∈ L.decodedVertexCarrier p ∧
      e.2 ∈ L.decodedVertexCarrier p := by
  rcases he with he | he
  · have hedge : (LambdaVertex.edge e.1 e.2 : L.LV) ∈ p.support := he.1
    constructor
    · apply L.gadgetCarrier_subset_decodedVertexCarrier p hedge
      simp [gadgetCarrier]
    · apply L.gadgetCarrier_subset_decodedVertexCarrier p hedge
      simp [gadgetCarrier]
  · rcases he with ⟨a, b, hab, hchosen⟩
    have hforward := L.chosenConnector?_eq_some hchosen
    have hend := hforward.endpoints_mem_gadgetCarrier L
    have habSupport := p.edgeSet_subset_support_prod hab
    exact ⟨L.gadgetCarrier_subset_decodedVertexCarrier p habSupport.1 hend.1,
      L.gadgetCarrier_subset_decodedVertexCarrier p habSupport.2 hend.2⟩

theorem decodedRouteIncidentCarrier_subset_decodedVertexCarrier
    (p : FinitePath L.lambda.graph) :
    L.decodedRouteIncidentCarrier p ⊆ L.decodedVertexCarrier p := by
  rintro x (⟨e, he, rfl | rfl⟩ | ⟨a, ha, hentry⟩)
  · exact (L.decodedRouteEdge_endpoints_mem_decodedVertexCarrier p he).1
  · exact (L.decodedRouteEdge_endpoints_mem_decodedVertexCarrier p he).2
  · apply L.gadgetCarrier_subset_decodedVertexCarrier p ha
    exact L.mem_gadgetCarrier_of_gadgetEntry hentry

/-- A represented carrier vertex is either explicitly present as an old
gadget or lies on a limiting-ladder component exposed by the auxiliary
path.  Edge gadgets and the possible initial proxy are accounted for in the
second alternative. -/
theorem mem_old_support_or_exposedLadderPath_of_mem_decodedVertexCarrier
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source) {x : V}
    (hx : x ∈ L.decodedVertexCarrier p) :
    LambdaVertex.old x ∈ p.support ∨
      ∃ Y ∈ GroundingSimultaneousDecode.exposedLadderPaths L p,
        x ∈ Y.support := by
  simp only [decodedVertexCarrier, Set.mem_iUnion] at hx
  obtain ⟨a, ha, hx⟩ := hx
  cases a with
  | old y =>
      have hxy : x = y := by simpa [gadgetCarrier] using hx
      subst x
      exact Or.inl ha
  | edge y z =>
      have hyz : (y, z) ∈ L.familyEdges :=
        L.edgeNode_mem_familyEdges_of_start_in_source p hstart ha
      have hyz' : (y, z) ∈ Alternating.familyEdges L.ladder.paths := by
        simpa [PopularAuxiliary.Input.familyEdges,
          Alternating.familyEdges] using hyz
      simp only [Alternating.familyEdges, Set.mem_iUnion] at hyz'
      obtain ⟨Y, hYL, hyzY⟩ := hyz'
      have hYexposed :
          Y ∈ GroundingSimultaneousDecode.exposedLadderPaths L p := by
        left
        refine ⟨hYL, ?_⟩
        refine ⟨LambdaVertex.edge y z, ha, ?_⟩
        right
        exact ⟨(y, z), hyzY, rfl⟩
      have hxEnds : x = y ∨ x = z := by
        simpa [gadgetCarrier, eq_comm] using hx
      exact Or.inr ⟨Y, hYexposed, hxEnds.elim
        (fun h ↦ h.symm ▸ (Y.edgeSet_subset_support_prod hyzY).1)
        (fun h ↦ h.symm ▸ (Y.edgeSet_subset_support_prod hyzY).2)⟩
  | proxy i =>
      have hstartProxy : p.start = LambdaVertex.proxy i :=
        L.proxy_mem_support_eq_start p hstart ha
      exact Or.inr ⟨L.proxyPath i, by
        right
        simp [hstartProxy],
        by simpa [gadgetCarrier] using hx⟩

/-- If a carrier vertex lies on a genuine limiting-ladder component, that
component is one of the finitely many components exposed by the auxiliary
path.  Faithfulness is needed only for the hidden initial-proxy case. -/
theorem mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful L)
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    {Y : Gamma.DPath} (hYL : Y ∈ L.ladder.paths)
    {x : V} (hx : x ∈ L.decodedVertexCarrier p)
    (hxY : x ∈ Y.support) :
    Y ∈ GroundingSimultaneousDecode.exposedLadderPaths L p := by
  simp only [decodedVertexCarrier, Set.mem_iUnion] at hx
  obtain ⟨a, ha, hx⟩ := hx
  cases a with
  | old y =>
      have hxy : x = y := by simpa [gadgetCarrier] using hx
      subst x
      left
      refine ⟨hYL, ?_⟩
      exact ⟨LambdaVertex.old y, ha, Or.inl ⟨y, hxY, rfl⟩⟩
  | edge y z =>
      have hyz : (y, z) ∈ L.familyEdges :=
        L.edgeNode_mem_familyEdges_of_start_in_source p hstart ha
      have hyz' : (y, z) ∈ Alternating.familyEdges L.ladder.paths := by
        simpa [PopularAuxiliary.Input.familyEdges,
          Alternating.familyEdges] using hyz
      simp only [Alternating.familyEdges, Set.mem_iUnion] at hyz'
      obtain ⟨Z, hZL, hyzZ⟩ := hyz'
      have hxZ : x ∈ Z.support := by
        have hxEnds : x = y ∨ x = z := by
          simpa [gadgetCarrier, eq_comm] using hx
        exact hxEnds.elim
          (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod hyzZ).1)
          (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod hyzZ).2)
      have hZY : Z = Y :=
        Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
          hZL hYL hxZ hxY
      have hyzY : (y, z) ∈ Y.edgeSet := hZY ▸ hyzZ
      subst Z
      left
      refine ⟨hYL, ?_⟩
      exact ⟨LambdaVertex.edge y z, ha,
        Or.inr ⟨(y, z), hyzZ, rfl⟩⟩
  | proxy i =>
      have hstartProxy : p.start = LambdaVertex.proxy i :=
        L.proxy_mem_support_eq_start p hstart ha
      have hproxyY : L.proxyPath i = Y :=
        Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
          (hfaith.1 i) hYL (by simpa [gadgetCarrier] using hx) hxY
      right
      simpa [GroundingSimultaneousDecode.exposedLadderPaths,
        hstartProxy] using hproxyY.symm

/-- Classify the particular gadget responsible for a carrier contact with a
limiting-ladder component.  Ordinary and edge gadgets belong to that
component's full Lambda trace; the only invisible case is the initial proxy,
which is returned explicitly with its represented component. -/
theorem gadget_mem_ladderTrace_or_proxy_eq_of_mem_carrier_of_mem_support
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful L)
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    {a : L.LV} (ha : a ∈ p.support)
    {Y : Gamma.DPath} (hYL : Y ∈ L.ladder.paths)
    {x : V} (hxa : x ∈ L.gadgetCarrier a) (hxY : x ∈ Y.support) :
    a ∈ PopularSwitching.ladderTrace L Y ∨
      ∃ i : I, a = LambdaVertex.proxy i ∧ L.proxyPath i = Y := by
  cases a with
  | old y =>
      have hxy : x = y := by simpa [gadgetCarrier] using hxa
      left
      exact Or.inl ⟨y, hxy ▸ hxY, rfl⟩
  | edge y z =>
      have hyz : (y, z) ∈ L.familyEdges :=
        L.edgeNode_mem_familyEdges_of_start_in_source p hstart ha
      have hyz' : (y, z) ∈ Alternating.familyEdges L.ladder.paths := by
        simpa [PopularAuxiliary.Input.familyEdges,
          Alternating.familyEdges] using hyz
      simp only [Alternating.familyEdges, Set.mem_iUnion] at hyz'
      obtain ⟨Z, hZL, hyzZ⟩ := hyz'
      have hxZ : x ∈ Z.support := by
        have hxEnds : x = y ∨ x = z := by
          simpa [gadgetCarrier, eq_comm] using hxa
        exact hxEnds.elim
          (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod hyzZ).1)
          (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod hyzZ).2)
      have hZY : Z = Y :=
        Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
          hZL hYL hxZ hxY
      left
      right
      exact ⟨(y, z), hZY ▸ hyzZ, rfl⟩
  | proxy i =>
      right
      refine ⟨i, rfl, ?_⟩
      exact Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
        (hfaith.1 i) hYL (by simpa [gadgetCarrier] using hxa) hxY

end PopularAuxiliary.Input

namespace GroundingErasedSwitchRelation

open PopularAuxiliary.Input PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

variable {V I : Type u} {Gamma : DWeb V}

/-- The represented vertex of an edge request which is not its
head-stopping exit.  An old request has no extra carrier vertex. -/
def requestTailSet
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV} :
    Request L C → Set V
  | .inl _ => ∅
  | .inr e => {e.1.1}

@[simp] theorem requestTailSet_inl
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (x : oldRequests L C) :
    requestTailSet (.inl x : Request L C) = ∅ := rfl

@[simp] theorem requestTailSet_inr
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (e : edgeRequests L C) :
    requestTailSet (.inr e : Request L C) = {e.1.1} := rfl

/-- For an old request the gadget carrier is its exit singleton.  For an
edge request `u → v`, head-stopping leaves just one possible extra carrier
point, the tail `u`. -/
theorem gadgetCarrier_requestAuxVertex_eq_exit_union_tail
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (r : Request L C) :
    L.gadgetCarrier (requestAuxVertex r) =
      {requestExit r} ∪ requestTailSet r := by
  cases r with
  | inl x =>
      ext z
      simp [requestAuxVertex, requestExit, requestTailSet,
        PopularAuxiliary.Input.gadgetCarrier]
  | inr e =>
      ext z
      simp [requestAuxVertex, requestExit, requestTailSet,
        PopularAuxiliary.Input.gadgetCarrier_edge]

/-- Exact own-gadget contact dichotomy for a compressed selected route.
The singleton-exit conclusion is automatic for an old request; in the
edge-request case the only unresolved possibility is an earlier occurrence
of the represented cut edge's tail. -/
theorem selectedErasedCompression_ownCarrierContact
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    (selectedErasedCompression U S K r).path.vertexSet ∩
        L.gadgetCarrier (requestAuxVertex r) ⊆
      {requestExit r} ∪ requestTailSet r := by
  intro x hx
  rw [gadgetCarrier_requestAuxVertex_eq_exit_union_tail] at hx
  exact hx.2

/-- Every retained erased route edge has both endpoints in the concrete
gadget carrier of its selected auxiliary path. -/
theorem selectedErasedRouteEdge_endpoints_mem
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) {e : V × V}
    (he : e ∈ (selectedErasedCompression U S K r).path.edgeSet) :
    e.1 ∈ L.decodedVertexCarrier (strongSelectedPath U S K r) ∧
      e.2 ∈ L.decodedVertexCarrier
        (strongSelectedPath U S K r) := by
  let p := strongSelectedPath U S K r
  let T := selectedRequestTrace U S K r
  have heT : e ∈ T.erasedCompression.path.edgeSet := he
  have heRaw : e ∈ signedEdgeSet T.steps :=
    PopularAuxiliary.Input.EndpointTrace.erasedCompression_edgeSet_subset_raw
      (L := L) T heT
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hstart : p.start ∈ L.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  have heRawFull : e ∈ signedEdgeSet (L.decodeWalkSteps p.walk) := by
    obtain ⟨s, hs, hse⟩ := heRaw
    exact ⟨s,
      (selectedRequestTrace_steps_sublist U S K r).subset hs, hse⟩
  have heDecoded : e ∈ L.decodedRouteEdges p := by
    rw [L.signedEdgeSet_decodeWalkSteps p hstart] at heRawFull
    exact heRawFull
  exact L.decodedRouteEdge_endpoints_mem_decodedVertexCarrier p heDecoded

/-- Every retained erased-route edge has both endpoints in the exact raw
decoded-route incident carrier.  In particular, a starting proxy contributes
only its actual attachment endpoint, not its entire represented path. -/
theorem selectedErasedRouteEdge_endpoints_mem_decodedRouteIncidentCarrier
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) {e : V × V}
    (he : e ∈ (selectedErasedCompression U S K r).path.edgeSet) :
    e.1 ∈ L.decodedRouteIncidentCarrier (strongSelectedPath U S K r) ∧
      e.2 ∈ L.decodedRouteIncidentCarrier
        (strongSelectedPath U S K r) := by
  let p := strongSelectedPath U S K r
  let T := selectedRequestTrace U S K r
  have heT : e ∈ T.erasedCompression.path.edgeSet := he
  have heRaw : e ∈ signedEdgeSet T.steps :=
    PopularAuxiliary.Input.EndpointTrace.erasedCompression_edgeSet_subset_raw
      (L := L) T heT
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hstart : p.start ∈ L.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  have heRawFull : e ∈ signedEdgeSet (L.decodeWalkSteps p.walk) := by
    obtain ⟨s, hs, hse⟩ := heRaw
    exact ⟨s,
      (selectedRequestTrace_steps_sublist U S K r).subset hs, hse⟩
  have heDecoded : e ∈ L.decodedRouteEdges p := by
    rw [L.signedEdgeSet_decodeWalkSteps p hstart] at heRawFull
    exact heRawFull
  exact L.decodedRouteEdge_endpoints_mem_decodedRouteIncidentCarrier
    p heDecoded

/-- The active untagged control which owns an edge in the simultaneous
erased-route union.  Keeping the subtype witness is essential downstream:
its proof component is the grounded no-earlier-contact certificate. -/
theorem erasedSelectedRouteEdge_activeOwner
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {e : V × V}
    (he : e ∈ erasedSelectedRouteEdges U S K) :
    ∃ c : ActiveControlRequest U S K,
      e ∈ (selectedErasedCompression U S K
        (chosenRequest c.1)).path.edgeSet := by
  simpa only [erasedSelectedRouteEdges, Set.mem_iUnion] using he

/-- Endpoint provenance for an arbitrary edge of the simultaneous erased
route union, with the responsible request made explicit. -/
theorem erasedSelectedRouteEdge_endpoints_mem
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {e : V × V}
    (he : e ∈ erasedSelectedRouteEdges U S K) :
    ∃ r : Request L S.cut,
      e.1 ∈ L.decodedVertexCarrier (strongSelectedPath U S K r) ∧
        e.2 ∈ L.decodedVertexCarrier
          (strongSelectedPath U S K r) := by
  simp only [erasedSelectedRouteEdges, Set.mem_iUnion] at he
  obtain ⟨c, he⟩ := he
  exact ⟨chosenRequest c,
    selectedErasedRouteEdge_endpoints_mem U S K (chosenRequest c) he⟩

/-- Direction-sensitive endpoint provenance, retaining both the responsible
request and membership in that request's compressed direction class. -/
theorem erasedSelectedDirectionEdge_endpoints_mem
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (d : Alternating.Direction) {e : V × V}
    (he : e ∈ erasedSelectedDirectionEdges U S K d) :
    ∃ r : Request L S.cut,
      e ∈ (selectedErasedCompression U S K r).path.directionEdges d ∧
        e.1 ∈ L.decodedVertexCarrier (strongSelectedPath U S K r) ∧
          e.2 ∈ L.decodedVertexCarrier
            (strongSelectedPath U S K r) := by
  simp only [erasedSelectedDirectionEdges, Set.mem_iUnion] at he
  obtain ⟨c, he⟩ := he
  have heEdge : e ∈ (selectedErasedCompression U S K
      (chosenRequest c)).path.edgeSet := by
    rw [(selectedErasedCompression U S K
      (chosenRequest c)).path.edgeSet_eq_directionEdges_union]
    cases d with
    | forward => exact Or.inl he
    | backward => exact Or.inr he
  exact ⟨chosenRequest c, he,
    selectedErasedRouteEdge_endpoints_mem U S K (chosenRequest c) heEdge⟩

/-- Direction-sensitive owner provenance without forgetting that the
owning control survived the greedy active-control recursion. -/
theorem erasedSelectedDirectionEdge_activeOwner
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (d : Alternating.Direction) {e : V × V}
    (he : e ∈ erasedSelectedDirectionEdges U S K d) :
    ∃ c : ActiveControlRequest U S K,
      e ∈ (selectedErasedCompression U S K
        (chosenRequest c.1)).path.directionEdges d := by
  simpa only [erasedSelectedDirectionEdges, Set.mem_iUnion] using he

/-- Attachment deletions retain their responsible request explicitly. -/
theorem attachmentCutEdge_request
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {e : V × V}
    (he : e ∈ attachmentCutEdges U S K) :
    e ∈ residualLadderEdges U S ∧
      ∃ r : Request L S.cut,
        e.1 = (selectedRequestTrace U S K r).initial := by
  exact ⟨he.1, chosenRequest he.2.choose, he.2.choose_spec⟩

/-- The CE-residual base inherits local bi-uniqueness from the limiting
ladder warp. -/
theorem residualLadderEdges_biUnique
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ residualLadderEdges U S) := by
  have hfull := Alternating.IsWarp.familyEdges_biUnique L.ladder.disjoint
  constructor
  · intro x y z hxz hyz
    apply hfull.1
    · simpa [PopularAuxiliary.Input.familyEdges,
        Alternating.familyEdges] using hxz.1
    · simpa [PopularAuxiliary.Input.familyEdges,
        Alternating.familyEdges] using hyz.1
  · intro x y z hxy hxz
    apply hfull.2
    · simpa [PopularAuxiliary.Input.familyEdges,
        Alternating.familyEdges] using hxy.1
    · simpa [PopularAuxiliary.Input.familyEdges,
        Alternating.familyEdges] using hxz.1

/-- Each one-request forward relation is locally bi-unique before taking
the simultaneous union. -/
theorem selectedErasedForwardEdges_biUnique
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ (selectedErasedCompression U S K r).path.directionEdges
        .forward) :=
  Alternating.AltPath.forwardEdges_biUnique
    (selectedErasedCompression U S K r).path

/-- Connector-conflict deletion makes the residual/forward cross terms
automatically locally unique.  Consequently local bi-uniqueness of the
whole switched relation reduces exactly to local bi-uniqueness of the
simultaneous forward union. -/
theorem erasedSelectedSwitchedEdges_biUnique_of_forward_biUnique
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hforward : Relator.BiUnique (fun x y ↦
      (x, y) ∈ erasedSelectedRetainedForwardEdges U S K)) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ erasedSelectedSwitchedEdges U S K) := by
  have hbase : Relator.BiUnique (fun x y ↦
      (x, y) ∈ residualLadderEdges U S \
        erasedSelectedToggleEdges U S K) := by
    constructor
    · intro x y z hxz hyz
      exact (residualLadderEdges_biUnique U S).1 hxz.1 hyz.1
    · intro x y z hxy hxz
      exact (residualLadderEdges_biUnique U S).2 hxy.1 hxz.1
  constructor
  · intro x y z hxz hyz
    change (x, z) ∈
      (residualLadderEdges U S \ erasedSelectedToggleEdges U S K) ∪
        (erasedSelectedDirectionEdges U S K .forward \
          oldRequestOutgoingForwardCutEdges U S K) at hxz
    change (y, z) ∈
      (residualLadderEdges U S \ erasedSelectedToggleEdges U S K) ∪
        (erasedSelectedDirectionEdges U S K .forward \
          oldRequestOutgoingForwardCutEdges U S K) at hyz
    rw [forward_diff_oldRequestOutgoingForwardCutEdges_eq_retained
      U S K] at hxz hyz
    rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
    · exact hbase.1 hxz hyz
    · exact survivingResidual_forward_incoming_unique U S K hxz hyz
    · exact (survivingResidual_forward_incoming_unique U S K hyz hxz).symm
    · exact hforward.1 hxz hyz
  · intro x y z hxy hxz
    change (x, y) ∈
      (residualLadderEdges U S \ erasedSelectedToggleEdges U S K) ∪
        (erasedSelectedDirectionEdges U S K .forward \
          oldRequestOutgoingForwardCutEdges U S K) at hxy
    change (x, z) ∈
      (residualLadderEdges U S \ erasedSelectedToggleEdges U S K) ∪
        (erasedSelectedDirectionEdges U S K .forward \
          oldRequestOutgoingForwardCutEdges U S K) at hxz
    rw [forward_diff_oldRequestOutgoingForwardCutEdges_eq_retained
      U S K] at hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hbase.2 hxy hxz
    · exact survivingResidual_forward_outgoing_unique U S K hxy hxz
    · exact (survivingResidual_forward_outgoing_unique U S K hxz hxy).symm
    · exact hforward.2 hxy hxz

/-- For the repaired switch data, isolated-vertex compatibility is built
into the definition of the surviving isolated set.  Thus only the three
genuine edge-relation obligations remain for a `Compatible` certificate. -/
theorem compatible_of_core
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hunique : Relator.BiUnique
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K))
    (hcycle : ¬ Alternating.ContainsDirectedCycle
      (erasedSelectedSwitchedEdges U S K))
    (hray : ¬ Alternating.ContainsReverseDirectedRay
      (erasedSelectedSwitchedEdges U S K)) :
    Compatible U S K where
  biUnique := hunique
  noDirectedCycle := hcycle
  noReverseDirectedRay := hray
  isolated_nonincident :=
    erasedSelectedSurvivingIsolated_nonincident U S K

end GroundingErasedSwitchRelation
end Erdos599
