/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointRoofCut
import ErdosProblems.Erdos599.ColouredSafeEndpointWeakSourceCoverage

/-!
# Incidence and full-reference accounting for endpoint-pruned roof cuts

All erased incidences at strictly roofed occurrence points survive the cut
once retained touched prefixes are essential. For source accounting, only
the new carrier has to be roofed. An untouched full-reference owner is
retained in the endpoint-pruned reference, and any new contact exposes its
unchanged initial in the actual touched essential local reference.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointRoofCut

open Set Cardinal DirectedPath Alternating Ladder LinkageBlueprint
open DWeb.KappaLadder.Deferred ColouredSafeReverseReachability ColouredSafeAmbientOccurrence
open ColouredSafeHammock ColouredSafeEndpointReference ColouredSafeEndpointStageReference
open ColouredSafeReferenceRoofCut

universe u

variable {V : Type u} {Gamma : DWeb V} {rho : Cardinal.{u}}
variable {L : Gamma.KappaLadder rho} {a : Stage rho} {s : V} {e : Option V}

theorem stageEdge_mem_touchedReference_of_endpoint
    (hL : HalfwayGeometry L) (A : Occurrence (reference L.limitWarp s e) s)
    (hEss : ∀ p ∈ stageReference hL a s e, (p.support ∩ A.vertexSet).Nonempty →
      p ∈ ladderReference L a)
    {edge : V × V} (he : edge ∈ familyEdges (stageReference hL a s e))
    (hend : edge.1 ∈ A.vertexSet ∨ edge.2 ∈ A.vertexSet) :
    edge ∈ familyEdges (stageTouchedReference hL a A) := by
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, hep⟩ := he
  have hsupport := p.edgeSet_subset_support_prod hep
  have hmeet : (p.support ∩ A.vertexSet).Nonempty := by
    rcases hend with ht | hh
    · exact ⟨edge.1, hsupport.1, ht⟩
    · exact ⟨edge.2, hsupport.2, hh⟩
  exact ⟨p, ⟨hp, hEss p hp hmeet, hmeet⟩, hep⟩

theorem incoming_backwardEdges_iff
    (hL : HalfwayGeometry L) (A : Occurrence (reference L.limitWarp s e) s)
    (hEss : ∀ p ∈ stageReference hL a s e, (p.support ∩ A.vertexSet).Nonempty →
      p ∈ ladderReference L a)
    {x y : V} (hxA : x ∈ A.vertexSet) (hxRoof : x ∈ Gamma.roof (L.frontier a)) :
    (y, x) ∈ backwardEdges A (stageTouchedReference hL a A) ↔
      (y, x) ∈ A.backwardEdges := by
  constructor
  · exact fun h ↦ h.1
  · intro hyx
    have hglobal : (y, x) ∈ familyEdges (reference L.limitWarp s e) := by
      cases A with
      | infinite Q => exact Q.backwardEdges_subset_familyEdges hyx
      | finite t Q => exact Q.backwardEdges_subset_familyEdges hyx
    exact ⟨hyx, stageEdge_mem_touchedReference_of_endpoint hL A hEss
      (incoming_edge_reflect hL hglobal hxRoof) (Or.inr hxA)⟩

theorem outgoing_backwardEdges_iff
    (hL : HalfwayGeometry L) (A : Occurrence (reference L.limitWarp s e) s)
    (hEss : ∀ p ∈ stageReference hL a s e, (p.support ∩ A.vertexSet).Nonempty →
      p ∈ ladderReference L a)
    {x y : V} (hxA : x ∈ A.vertexSet) (hxStrict : x ∈ Gamma.strictRoof (L.frontier a)) :
    (x, y) ∈ backwardEdges A (stageTouchedReference hL a A) ↔
      (x, y) ∈ A.backwardEdges := by
  constructor
  · exact fun h ↦ h.1
  · intro hxy
    have hglobal : (x, y) ∈ familyEdges (reference L.limitWarp s e) := by
      cases A with
      | infinite Q => exact Q.backwardEdges_subset_familyEdges hxy
      | finite t Q => exact Q.backwardEdges_subset_familyEdges hxy
    obtain ⟨p, hp, hxp⟩ := vertexSet_reflect hL
      (familyEdges_subset_vertexSet_prod (reference L.limitWarp s e) hglobal).1 hxStrict.1
    have hpTouched : p ∈ stageTouchedReference hL a A :=
      ⟨hp, hEss p hp ⟨x, hxp, hxA⟩, x, hxp, hxA⟩
    have hxNotTerminal : x ∉ Gamma.terminalFrontier (stageTouchedReference hL a A) := by
      intro hx
      apply hxStrict.2
      rw [L.frontiersAreEssential_of_roofsSourceAtStages hL.roofsSourceAtStages a]
      exact stageTouchedReference_terminals_subset hL A hx
    have hlocalOut : ∃ z, (x, z) ∈ familyEdges (stageTouchedReference hL a A) := by
      by_contra hno
      apply hxNotTerminal
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
        (stageTouchedReference_isWarp hL A)]
      exact ⟨⟨p, hpTouched, hxp⟩, hno⟩
    obtain ⟨z, hxz⟩ := hlocalOut
    have hzy : z = y := (IsWarp.familyEdges_biUnique
      (ColouredSafeEndpointReference.isWarp (hL.warpStages (finalStage rho)))).2
        (stageTouchedReference_edges_subset hL A hxz) hglobal
    exact ⟨hxy, hzy ▸ hxz⟩

theorem limitOwner_initial_mem_stageTouchedReference_of_meets
    (hL : HalfwayGeometry L) (A : Occurrence (reference L.limitWarp s e) s)
    {K : Set V} (hKRoof : K ⊆ Gamma.roof (L.frontier a))
    (hKCarrier : K ⊆ Gamma.vertexSet (stageTouchedReference hL a A) ∪ A.vertexSet)
    {p : Gamma.DPath} (hp : p ∈ reference L.limitWarp s e)
    (hfrontier : (p.support ∩ L.frontier a).Nonempty) (hmeet : (p.support ∩ K).Nonempty) :
    p.initial ∈ Gamma.initialSet (stageTouchedReference hL a A) := by
  obtain ⟨v, hvp, hvFrontier⟩ := hfrontier
  obtain ⟨q, hq, _hqTerminal, hqp⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit hL hp.1 hvFrontier hvp
  have hqRetained : q ∈ stageReference hL a s e :=
    mem_stageReference_of_common_vertex hq.1 hp q.initial_mem_support
      (Gamma.support_mono_of_extends hqp q.initial_mem_support)
  obtain ⟨x, hxp, hxK⟩ := hmeet
  have hxq : x ∈ q.support := limitComponent_support_inter_roof_subset_prefix
    hL a hp.1 hq.1 hqp ⟨hxp, hKRoof hxK⟩
  have hqTouched : q ∈ stageTouchedReference hL a A := by
    rcases hKCarrier hxK with hxLocal | hxA
    · obtain ⟨r, hr, hxr⟩ := hxLocal
      have hqr : q = r := DWeb.IsWarp.eq_of_mem_support
        (hL.warpStages (Stage.toExtended a)) hq.1 (stageReference_subset hr.1) hxq hxr
      exact hqr ▸ hr
    · exact ⟨hqRetained, hq, x, hxq, hxA⟩
  exact ⟨q, hqTouched, Gamma.extends_initial hqp⟩

theorem sourceCondition_of_roofCut
    (hL : HalfwayGeometry L) (A : Occurrence (reference L.limitWarp s e) s)
    {K : Set V} (hKRoof : K ⊆ Gamma.roof (L.frontier a))
    (hKCarrier : K ⊆ Gamma.vertexSet (stageTouchedReference hL a A) ∪ A.vertexSet)
    {D : DWeb V} {W U : Set D.DPath}
    (hends : endpoints s e ⊆ D.vertexSet W)
    (hcover : Gamma.source ⊆ D.initialSet W ∪ Gamma.initialSet
      (referencePathsMeeting L.limitWarp (L.frontier a) \
        referencePathsMeeting L.limitWarp (D.vertexSet W)))
    (hinitial : D.initialSet W ⊆ D.initialSet U)
    (hreference : Gamma.initialSet (stageTouchedReference hL a A) ⊆ D.initialSet U)
    (hcarrier : D.vertexSet U ⊆ D.vertexSet W ∪ K) :
    Gamma.source ⊆ D.initialSet U ∪ Gamma.initialSet
      (referencePathsMeeting L.limitWarp (L.frontier a) \
        referencePathsMeeting L.limitWarp (D.vertexSet U)) := by
  intro x hx
  rcases hcover hx with hxOld | ⟨p, hp, hpx⟩
  · exact Or.inl (hinitial hxOld)
  · have hnotOld : ¬(p.support ∩ D.vertexSet W).Nonempty :=
      fun hmeet ↦ hp.2 ⟨hp.1.1, hmeet⟩
    by_cases hmeet : (p.support ∩ D.vertexSet U).Nonempty
    · obtain ⟨v, hvp, hvU⟩ := hmeet
      have hvK : v ∈ K := by
        rcases hcarrier hvU with hvOld | hvK
        · exact False.elim (hnotOld ⟨v, hvp, hvOld⟩)
        · exact hvK
      have hpRetained := mem_reference_of_not_meets hends hp.1.1 hnotOld
      have hroot := limitOwner_initial_mem_stageTouchedReference_of_meets
        hL A hKRoof hKCarrier hpRetained hp.1.2 ⟨v, hvp, hvK⟩
      exact Or.inl (hpx ▸ hreference hroot)
    · exact Or.inr ⟨p, ⟨hp.1, fun h ↦ hmeet h.2⟩, hpx⟩

#print axioms incoming_backwardEdges_iff
#print axioms outgoing_backwardEdges_iff
#print axioms limitOwner_initial_mem_stageTouchedReference_of_meets
#print axioms sourceCondition_of_roofCut

end Erdos599.Blueprint.ColouredSafeEndpointRoofCut
