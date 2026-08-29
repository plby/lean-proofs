/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointLocalizationSemantics
import ErdosProblems.Erdos599.ColouredSafeStageWeakSwitch

/-!
# One protected endpoint-pruned selector for finite and infinite routes

Reserve the protected and inessential carriers before choosing the actual
route. A retained touched prefix cannot contain a displayed endpoint, so
every touched prefix is essential even when an excluded endpoint owner is
inessential. The route filter and explicit fixed-stage roof are retained.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem endpoint_hasCard_exists_essentialOccurrence_avoiding
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s : V} {e : Option V}
    {extra : Occurrence (reference C.ladder.limitWarp s e) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s e) s e extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s e) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s e) s e extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        (A.retypeEndpointStageReference C.legal hARoof).touchedReference ⊆
          ladderReference C.ladder a ∧
        (A.retypeEndpointStageReference C.legal hARoof).referenceClosure ∩ X ⊆ endpoints s e ∧
        (A.retypeEndpointStageReference C.legal hARoof).referenceClosure ⊆
          Gamma.roof (C.ladder.frontier a) := by
  let bad := C.inessentialCarrierAt a
  have hbad : #bad ≤ kappa := by
    apply DWeb.KappaLadder.Deferred.mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi
      C.legal C.capacity_infinite a
    intro haPhi
    exact Set.disjoint_left.mp C.club_avoids_phi ha haPhi
  have hreserve : #(X ∪ bad : Set V) ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite hX hbad)
  obtain ⟨A, hA, havoid⟩ := h.exists_goodRoute_avoiding_referenceClosure
    (ColouredSafeEndpointReference.isWarp (C.legal.warpStages (finalStage (succ kappa))))
    C.capacity_infinite hreserve
  let hARoof := hroof A hA.2.2.2.2
  let B := A.retypeEndpointStageReference C.legal hARoof
  have hBessential : B.touchedReference ⊆ ladderReference C.ladder a := by
    intro p hp
    by_contra hpEss
    obtain ⟨x, hxp, hxB⟩ := hp.2
    have hxA : x ∈ A.vertexSet := by
      simpa only [B, CurrentSafeOccurrence.retypeEndpointStageReference_vertexSet] using hxB
    have hxBad : x ∈ bad := ⟨p, ⟨stageReference_subset hp.1, hpEss⟩, hxp⟩
    have hxEnds := havoid ⟨Or.inl hxA, Or.inr hxBad⟩
    exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
      ⟨p, hp.1, hxp⟩ hxEnds
  have hBClosure : B.referenceClosure ⊆ A.referenceClosure :=
    A.retypeEndpointStageReference_referenceClosure_subset C.legal hARoof
  have hBX : B.referenceClosure ∩ X ⊆ endpoints s e := by
    intro x hx
    exact havoid ⟨hBClosure hx.1, Or.inl hx.2⟩
  have hstageRoof : Gamma.vertexSet (C.ladder.warpAt a) ⊆
      Gamma.roof (C.ladder.frontier a) := by
    rw [C.ladder.frontier_eq_essential_terminalFrontier C.legal.roofsSourceAtStages,
      Gamma.roof_essential]
    exact DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier C.legal a
  refine ⟨A, hA, hARoof, hBessential, hBX, ?_⟩
  apply Set.union_subset
  · simpa only [B, CurrentSafeOccurrence.retypeEndpointStageReference_vertexSet] using hARoof
  · exact meetingVertices_subset_roof Gamma (stageReference C.legal a s e) B.vertexSet _
      (fun p hp x hxp ↦ hstageRoof ⟨p, stageReference_subset hp, hxp⟩)

#print axioms endpoint_hasCard_exists_essentialOccurrence_avoiding

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
