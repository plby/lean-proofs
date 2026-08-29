/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointStageWeakSwitch

/-!
# Full-reference source accounting for an endpoint-pruned weak switch

An owner excluded through a displayed endpoint already meets any input
carrier containing those endpoints. Thus every newly touched limiting owner
is retained by the pruned reference. Its actual stage prefix contributes
its unchanged initial to a genuine switch companion. The resulting source
condition refers to the original full limiting reference, not only its
pruned subfamily. The ambient augmented graph remains arbitrary.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointReference

open Set Cardinal DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {s : V} {e : Option V} {X : Set V}

/-- Untouched owners cannot be among those excluded through the endpoints
of an already present edge (or an already present infinite-route source). -/
theorem mem_reference_of_not_meets
    (hends : ColouredSafeHammock.endpoints s e ⊆ X)
    {p : Gamma.DPath} (hp : p ∈ Y) (hnot : ¬(p.support ∩ X).Nonempty) :
    p ∈ reference Y s e := by
  refine ⟨hp, Set.disjoint_left.mpr ?_⟩
  intro x hxp hxEnd
  exact hnot ⟨x, hxp, hends hxEnd⟩

end Erdos599.Blueprint.ColouredSafeEndpointReference

namespace Erdos599.ColouredSafeAmbientOccurrence.TouchedWeakSwitch

open Set Cardinal DirectedPath Alternating Ladder Blueprint
open DWeb.KappaLadder.Deferred ColouredSafeReverseReachability
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference

universe u

variable {V : Type u} {Gamma : DWeb V} {rho : Cardinal.{u}}
variable {L : Gamma.KappaLadder rho} {a : Stage rho} {s t : V} {e : Option V}

/-- The actual retained stage prefix has the original limiting owner's
initial, and its newly touched source appears in a companion component. -/
theorem endpoint_limitOwner_initial_mem_companions_of_meets
    (hL : HalfwayGeometry L) {A : Occurrence (reference L.limitWarp s e) s}
    (hARoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (T : TouchedWeakSwitch (A.retypeEndpointStageReference hL hARoof) t)
    (hTRoof : Gamma.vertexSet T.paths ⊆ Gamma.roof (L.frontier a))
    {p : Gamma.DPath} (hp : p ∈ reference L.limitWarp s e)
    (hfrontier : (p.support ∩ L.frontier a).Nonempty)
    (hmeet : (p.support ∩ Gamma.vertexSet T.paths).Nonempty) :
    p.initial ∈ Gamma.initialSet T.companions := by
  obtain ⟨v, hvp, hvFrontier⟩ := hfrontier
  obtain ⟨q, hq, _hqTerminal, hqp⟩ :=
    LinkageBlueprint.ladderReference.exists_prefix_of_limitWarp_frontier_hit
      hL hp.1 hvFrontier hvp
  have hqRetained : q ∈ stageReference hL a s e :=
    mem_stageReference_of_common_vertex hq.1 hp q.initial_mem_support
      (Gamma.support_mono_of_extends hqp q.initial_mem_support)
  obtain ⟨x, hxp, hxT⟩ := hmeet
  have hxq : x ∈ q.support :=
    limitComponent_support_inter_roof_subset_prefix hL a hp.1 hq.1 hqp ⟨hxp, hTRoof hxT⟩
  have hsOff : s ∉ Gamma.vertexSet (stageReference hL a s e) := by
    intro hs
    exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
      hs (Or.inl rfl)
  have hqInitial := T.referenceOwner_initial_mem_companions_of_meets
    stageReference_isWarp hsOff hqRetained ⟨x, hxq, hxT⟩
  exact Gamma.extends_initial hqp ▸ hqInitial

#print axioms endpoint_limitOwner_initial_mem_companions_of_meets

end Erdos599.ColouredSafeAmbientOccurrence.TouchedWeakSwitch

namespace Erdos599.Blueprint.ColouredSafeEndpointSourceCoverage

open Set Cardinal DirectedPath Alternating Ladder LinkageBlueprint
open DWeb.KappaLadder.Deferred ColouredSafeReverseReachability ColouredSafeAmbientOccurrence
open ColouredSafeEndpointReference

universe u

variable {V : Type u} {Gamma : DWeb V} {rho : Cardinal.{u}}
variable {L : Gamma.KappaLadder rho} {a : Stage rho} {s t : V} {e : Option V}

/-- Preserve the exact full-reference source condition. Actual path
subdivision supplies the three displayed initial/carrier inclusions;
endpoint exclusion is accounted for using the input's literal carrier. -/
theorem sourceCondition_of_endpointWeakSwitch
    (hL : HalfwayGeometry L) {A : Occurrence (reference L.limitWarp s e) s}
    (hARoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (T : TouchedWeakSwitch (A.retypeEndpointStageReference hL hARoof) t)
    (hTRoof : Gamma.vertexSet T.paths ⊆ Gamma.roof (L.frontier a))
    {D : DWeb V} {W U : Set D.DPath}
    (hends : ColouredSafeHammock.endpoints s e ⊆ D.vertexSet W)
    (hcover : Gamma.source ⊆ D.initialSet W ∪ Gamma.initialSet
      (referencePathsMeeting L.limitWarp (L.frontier a) \
        referencePathsMeeting L.limitWarp (D.vertexSet W)))
    (hinitial : D.initialSet W ⊆ D.initialSet U)
    (hcompanion : Gamma.initialSet T.companions ⊆ D.initialSet U)
    (hcarrier : D.vertexSet U ⊆ D.vertexSet W ∪ Gamma.vertexSet T.paths) :
    Gamma.source ⊆ D.initialSet U ∪ Gamma.initialSet
      (referencePathsMeeting L.limitWarp (L.frontier a) \
        referencePathsMeeting L.limitWarp (D.vertexSet U)) := by
  intro x hx
  rcases hcover hx with hxOld | hxReference
  · exact Or.inl (hinitial hxOld)
  · obtain ⟨p, hp, hpx⟩ := hxReference
    have hnotOld : ¬(p.support ∩ D.vertexSet W).Nonempty :=
      fun h ↦ hp.2 ⟨hp.1.1, h⟩
    by_cases hmeet : (p.support ∩ D.vertexSet U).Nonempty
    · obtain ⟨v, hvp, hvU⟩ := hmeet
      have hvT : v ∈ Gamma.vertexSet T.paths := by
        rcases hcarrier hvU with hvW | hvT
        · exact False.elim (hnotOld ⟨v, hvp, hvW⟩)
        · exact hvT
      have hpRetained := mem_reference_of_not_meets hends hp.1.1 hnotOld
      have hpInitial := T.endpoint_limitOwner_initial_mem_companions_of_meets
        hL hARoof hTRoof hpRetained hp.1.2 ⟨v, hvp, hvT⟩
      exact Or.inl (hpx ▸ hcompanion hpInitial)
    · exact Or.inr ⟨p, ⟨hp.1, fun h ↦ hmeet h.2⟩, hpx⟩

#print axioms sourceCondition_of_endpointWeakSwitch

end Erdos599.Blueprint.ColouredSafeEndpointSourceCoverage
