/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointWeakSourceCoverage

/-!
# Type-independent full-reference source accounting for pruned switches

The proof uses the actual added carrier's roof and localized-reference
closure bounds, not a weak/strong/infinite type tag. Every newly touched
full limiting owner has its unchanged initial in the touched local reference.
Keeping these initials preserves the exact original source condition.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointSourceCoverage

open Set Cardinal DirectedPath Alternating Ladder LinkageBlueprint
open DWeb.KappaLadder.Deferred ColouredSafeReverseReachability ColouredSafeAmbientOccurrence
open ColouredSafeHammock ColouredSafeEndpointReference ColouredSafeEndpointStageReference

universe u

variable {V : Type u} {Gamma : DWeb V} {rho : Cardinal.{u}}
variable {L : Gamma.KappaLadder rho} {a : Stage rho} {s : V} {e : Option V}

theorem limitOwner_initial_mem_touchedReference_of_meets
    (hL : HalfwayGeometry L) (A : Occurrence (reference L.limitWarp s e) s)
    (hARoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    {K : Set Gamma.DPath} (hKRoof : Gamma.vertexSet K ⊆ Gamma.roof (L.frontier a))
    (hKClosure : Gamma.vertexSet K ⊆
      (A.retypeEndpointStageReference hL hARoof).referenceClosure)
    {p : Gamma.DPath} (hp : p ∈ reference L.limitWarp s e)
    (hfrontier : (p.support ∩ L.frontier a).Nonempty)
    (hmeet : (p.support ∩ Gamma.vertexSet K).Nonempty) :
    p.initial ∈ Gamma.initialSet (A.retypeEndpointStageReference hL hARoof).touchedReference := by
  obtain ⟨v, hvp, hvFrontier⟩ := hfrontier
  obtain ⟨q, hq, _hqTerminal, hqp⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit hL hp.1 hvFrontier hvp
  have hqRetained : q ∈ stageReference hL a s e :=
    mem_stageReference_of_common_vertex hq.1 hp q.initial_mem_support
      (Gamma.support_mono_of_extends hqp q.initial_mem_support)
  obtain ⟨x, hxp, hxK⟩ := hmeet
  have hxq := limitComponent_support_inter_roof_subset_prefix hL a hp.1 hq.1 hqp
    ⟨hxp, hKRoof hxK⟩
  let B := A.retypeEndpointStageReference hL hARoof
  have hqTouched := B.mem_touchedReference_of_meets_referenceClosure
    stageReference_isWarp hqRetained ⟨x, hxq, hKClosure hxK⟩
  exact ⟨q, hqTouched, Gamma.extends_initial hqp⟩

/-- A real carrier supplied by any of the actual switch constructions can
be used; all new full-reference source obligations are proved pointwise. -/
theorem sourceCondition_of_endpointSwitch
    (hL : HalfwayGeometry L) (A : Occurrence (reference L.limitWarp s e) s)
    (hARoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    {K : Set Gamma.DPath} (hKRoof : Gamma.vertexSet K ⊆ Gamma.roof (L.frontier a))
    (hKClosure : Gamma.vertexSet K ⊆
      (A.retypeEndpointStageReference hL hARoof).referenceClosure)
    {D : DWeb V} {W U : Set D.DPath}
    (hends : endpoints s e ⊆ D.vertexSet W)
    (hcover : Gamma.source ⊆ D.initialSet W ∪ Gamma.initialSet
      (referencePathsMeeting L.limitWarp (L.frontier a) \
        referencePathsMeeting L.limitWarp (D.vertexSet W)))
    (hinitial : D.initialSet W ⊆ D.initialSet U)
    (hreference : Gamma.initialSet (A.retypeEndpointStageReference hL hARoof).touchedReference ⊆
      D.initialSet U)
    (hcarrier : D.vertexSet U ⊆ D.vertexSet W ∪ Gamma.vertexSet K) :
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
      have hvK : v ∈ Gamma.vertexSet K := by
        rcases hcarrier hvU with hvW | hvK
        · exact False.elim (hnotOld ⟨v, hvp, hvW⟩)
        · exact hvK
      have hpRetained := mem_reference_of_not_meets hends hp.1.1 hnotOld
      have hpInitial := limitOwner_initial_mem_touchedReference_of_meets
        hL A hARoof hKRoof hKClosure hpRetained hp.1.2 ⟨v, hvp, hvK⟩
      exact Or.inl (hpx ▸ hreference hpInitial)
    · exact Or.inr ⟨p, ⟨hp.1, fun h ↦ hmeet h.2⟩, hpx⟩

/-- Both port splices have this exact initial identity. Exposedness in the
pruned local reference proves that deleting the displayed source loses no
touched-reference initial, including full owners newly met by the output. -/
theorem sourceCondition_of_endpointSwitch_initials_eq
    (hL : HalfwayGeometry L) (A : Occurrence (reference L.limitWarp s e) s)
    (hARoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    {K : Set Gamma.DPath} (hKRoof : Gamma.vertexSet K ⊆ Gamma.roof (L.frontier a))
    (hKClosure : Gamma.vertexSet K ⊆
      (A.retypeEndpointStageReference hL hARoof).referenceClosure)
    (hKI : Gamma.initialSet K =
      Gamma.initialSet (A.retypeEndpointStageReference hL hARoof).touchedReference ∪ {s})
    {D : DWeb V} {W U : Set D.DPath}
    (hends : endpoints s e ⊆ D.vertexSet W)
    (hcover : Gamma.source ⊆ D.initialSet W ∪ Gamma.initialSet
      (referencePathsMeeting L.limitWarp (L.frontier a) \
        referencePathsMeeting L.limitWarp (D.vertexSet W)))
    (hUI : D.initialSet U = D.initialSet W ∪ (Gamma.initialSet K \ {s}))
    (hUV : D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet K) :
    Gamma.source ⊆ D.initialSet U ∪ Gamma.initialSet
      (referencePathsMeeting L.limitWarp (L.frontier a) \
        referencePathsMeeting L.limitWarp (D.vertexSet U)) := by
  apply sourceCondition_of_endpointSwitch hL A hARoof hKRoof hKClosure hends hcover
  · rw [hUI]
    exact Set.subset_union_left
  · intro x hx
    rw [hUI]
    right
    refine ⟨hKI.symm ▸ Or.inl hx, ?_⟩
    intro hxs
    obtain ⟨p, hp, hpx⟩ := hx
    exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
      ⟨p, hp.1, hpx ▸ p.initial_mem_support⟩ (Or.inl hxs)
  · rw [hUV]

#print axioms limitOwner_initial_mem_touchedReference_of_meets
#print axioms sourceCondition_of_endpointSwitch
#print axioms sourceCondition_of_endpointSwitch_initials_eq

end Erdos599.Blueprint.ColouredSafeEndpointSourceCoverage
