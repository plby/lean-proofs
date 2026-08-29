/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReferenceRoofCut
import ErdosProblems.Erdos599.ColouredSafeEndpointStageSelection

/-!
# Actual endpoint-pruned roof cuts without uniform capture

The retained local family is selected by full limiting owners. Its exact
roof-cut relation has a countable finite-character realization inside the
pruned global reference closure. Protected selection excludes inessential
contacts only on retained owners; the displayed endpoints may themselves
lie on excluded inessential owners. No roof bound on an eligible word is
assumed. Rooted boundary and port accounting are separate obligations.
-/

noncomputable section

namespace Erdos599

open Set Cardinal Order DirectedPath Alternating Ladder Blueprint
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference
open DWeb.KappaLadder.Deferred

universe u

variable {V : Type u} {Gamma : DWeb V} {rho : Cardinal.{u}}

namespace Blueprint.ColouredSafeEndpointRoofCut

variable {L : Gamma.KappaLadder rho} {a : Stage rho} {s : V} {e : Option V}

def stageTouchedReference (hL : HalfwayGeometry L) (a : Stage rho)
    (A : Occurrence (reference L.limitWarp s e) s) : Set Gamma.DPath :=
  {p | p ∈ stageReference hL a s e ∧ p ∈ LinkageBlueprint.ladderReference L a ∧
    (p.support ∩ A.vertexSet).Nonempty}

theorem stageTouchedReference_isWarp (hL : HalfwayGeometry L)
    (A : Occurrence (reference L.limitWarp s e) s) :
    Gamma.IsWarp (stageTouchedReference hL a A) :=
  (LinkageBlueprint.ladderReference.isWarp hL).subset (fun _ hp ↦ hp.2.1)

theorem stageTouchedReference_finiteCharacter (hL : HalfwayGeometry L)
    (A : Occurrence (reference L.limitWarp s e) s) :
    Gamma.HasFiniteCharacter (stageTouchedReference hL a A) :=
  fun hp ↦ LinkageBlueprint.ladderReference.finiteCharacter hp.2.1

theorem stageTouchedReference_edges_subset (hL : HalfwayGeometry L)
    (A : Occurrence (reference L.limitWarp s e) s) :
    familyEdges (stageTouchedReference hL a A) ⊆
      familyEdges (reference L.limitWarp s e) := by
  intro edge he
  apply (embedding hL a s e).familyEdges_subset
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, hep⟩ := he
  exact ⟨p, hp.1, hep⟩

theorem stageTouchedReference_initials_subset (hL : HalfwayGeometry L)
    (A : Occurrence (reference L.limitWarp s e) s) :
    Gamma.initialSet (stageTouchedReference hL a A) ⊆
      Gamma.initialSet (reference L.limitWarp s e) := by
  rintro x ⟨p, hp, hpx⟩
  exact ColouredSafeEndpointStageReference.initialSet_subset ⟨p, hp.1, hpx⟩

theorem stageTouchedReference_terminals_subset (hL : HalfwayGeometry L)
    (A : Occurrence (reference L.limitWarp s e) s) :
    Gamma.terminalFrontier (stageTouchedReference hL a A) ⊆ L.frontier a := by
  rintro x ⟨p, hp, hpx⟩
  rw [← LinkageBlueprint.ladderReference.terminalFrontier_eq hL]
  exact ⟨p, hp.2.1, hpx⟩

theorem stageTouchedReference_vertexSet_subset_roof (hL : HalfwayGeometry L)
    (A : Occurrence (reference L.limitWarp s e) s) :
    Gamma.vertexSet (stageTouchedReference hL a A) ⊆ Gamma.roof (L.frontier a) := by
  intro x hx
  apply LinkageBlueprint.ladderReference.vertexSet_subset_roof hL
    (vertexSet_warpAt_subset_roof_terminalFrontier hL a)
  obtain ⟨p, hp, hxp⟩ := hx
  exact ⟨p, hp.2.1, hxp⟩

theorem stageTouchedReference_vertexSet_subset_referenceClosure (hL : HalfwayGeometry L)
    (A : Occurrence (reference L.limitWarp s e) s) :
    Gamma.vertexSet (stageTouchedReference hL a A) ⊆ A.referenceClosure := by
  rintro x ⟨p, hp, hxp⟩
  let E := embedding hL a s e
  let q := E.owner ⟨p, hp.1⟩
  obtain ⟨y, hyp, hyA⟩ := hp.2.2
  exact Or.inr (support_subset_meetingVertices Gamma (reference L.limitWarp s e)
    A.vertexSet q.2 ⟨y, E.support_subset ⟨p, hp.1⟩ hyp, hyA⟩
    (E.support_subset ⟨p, hp.1⟩ hxp))

theorem exists_stageTouched_finiteWarp (hL : HalfwayGeometry L)
    (A : Occurrence (reference L.limitWarp s e) s) (hA : Valid A) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = ColouredSafeReferenceRoofCut.edges A
        (stageTouchedReference hL a A) (L.frontier a) ∧
      isolatedVertices U = isolatedVertices (stageTouchedReference hL a A) ∧
      Gamma.vertexSet U ⊆ Gamma.roof (L.frontier a) ∧
      Gamma.vertexSet U ⊆
        Gamma.vertexSet (stageTouchedReference hL a A) ∪ A.vertexSet ∧
      Gamma.vertexSet U ⊆ A.referenceClosure ∧ (Gamma.vertexSet U).Countable ∧
      familyEdges U ⊆ A.switchedEdges := by
  have hG : Gamma.IsWarp (reference L.limitWarp s e) :=
    ColouredSafeEndpointReference.isWarp (hL.warpStages (finalStage rho))
  obtain ⟨U, hU, hUfinite, hUE, hUI, hURoof, hUCarrier⟩ :=
    ColouredSafeReferenceRoofCut.exists_finiteWarp_roofed hG A hA
      (stageTouchedReference hL a A) (stageTouchedReference_isWarp hL A)
      (stageTouchedReference_finiteCharacter hL A) (stageTouchedReference_edges_subset hL A)
      (stageTouchedReference_initials_subset hL A) (L.frontier a)
      (L.frontiersAreEssential_of_roofsSourceAtStages hL.roofsSourceAtStages a)
      (stageTouchedReference_terminals_subset hL A)
      (stageTouchedReference_vertexSet_subset_roof hL A)
  have hclosure : Gamma.vertexSet U ⊆ A.referenceClosure :=
    hUCarrier.trans (Set.union_subset
      (stageTouchedReference_vertexSet_subset_referenceClosure hL A) Set.subset_union_left)
  refine ⟨U, hU, hUfinite, hUE, hUI, hURoof, hUCarrier, hclosure,
    (A.referenceClosure_countable hG).mono hclosure, ?_⟩
  rw [hUE]
  exact ColouredSafeReferenceRoofCut.edges_subset_switchedEdges A
    (stageTouchedReference_edges_subset hL A) (L.frontier a)

#print axioms exists_stageTouched_finiteWarp

end Blueprint.ColouredSafeEndpointRoofCut

namespace Blueprint.LinkageBlueprint.ClubStageGeometry

variable {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- The protected selector needs no roof filter if its conclusion only
asks for essentiality of the retained touched stage prefixes. -/
theorem endpoint_hasCard_exists_essentialOccurrence_unroofed
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s : V} {e : Option V}
    {extra : Occurrence (reference C.ladder.limitWarp s e) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s e) s e extra (succ kappa))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s e) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s e) s e extra ∧
      A.referenceClosure ∩ X ⊆ endpoints s e ∧
      ∀ p ∈ stageReference C.legal a s e, (p.support ∩ A.vertexSet).Nonempty →
        p ∈ ladderReference C.ladder a := by
  let bad := C.inessentialCarrierAt a
  have hbad : #bad ≤ kappa := by
    apply mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi C.legal C.capacity_infinite a
    intro haPhi
    exact Set.disjoint_left.mp C.club_avoids_phi ha haPhi
  have hreserve : #(X ∪ bad : Set V) ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite hX hbad)
  obtain ⟨A, hA, havoid⟩ := h.exists_goodRoute_avoiding_referenceClosure
    (ColouredSafeEndpointReference.isWarp (C.legal.warpStages (finalStage (succ kappa))))
    C.capacity_infinite hreserve
  refine ⟨A, hA, fun _ hx ↦ havoid ⟨hx.1, Or.inl hx.2⟩, ?_⟩
  intro p hp hmeet
  by_contra hpEss
  obtain ⟨x, hxp, hxA⟩ := hmeet
  have hxBad : x ∈ bad := ⟨p, ⟨stageReference_subset hp, hpEss⟩, hxp⟩
  exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
    ⟨p, hp, hxp⟩ (havoid ⟨Or.inl hxA, Or.inr hxBad⟩)

/-- An actual protected endpoint-pruned roof-cut family at the displayed
stage, even when the chosen occurrence leaves that roof. -/
theorem endpoint_hasCard_exists_protected_roofCut
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s : V} {e : Option V}
    {extra : Occurrence (reference C.ladder.limitWarp s e) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s e) s e extra (succ kappa))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s e) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s e) s e extra ∧
      A.referenceClosure ∩ X ⊆ endpoints s e ∧
      (∀ p ∈ stageReference C.legal a s e, (p.support ∩ A.vertexSet).Nonempty →
        p ∈ ladderReference C.ladder a) ∧
      ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
        familyEdges U = ColouredSafeReferenceRoofCut.edges A
          (ColouredSafeEndpointRoofCut.stageTouchedReference C.legal a A) (C.ladder.frontier a) ∧
        isolatedVertices U = isolatedVertices
          (ColouredSafeEndpointRoofCut.stageTouchedReference C.legal a A) ∧
        Gamma.vertexSet U ⊆ Gamma.roof (C.ladder.frontier a) ∧
        Gamma.vertexSet U ⊆ A.referenceClosure ∧
        Gamma.vertexSet U ∩ X ⊆ endpoints s e ∧
        (Gamma.vertexSet U).Countable ∧ familyEdges U ⊆ A.switchedEdges := by
  obtain ⟨A, hA, hAX, hEss⟩ := C.endpoint_hasCard_exists_essentialOccurrence_unroofed ha h hX
  obtain ⟨U, hU, hUfinite, hUE, hUI, hURoof, _hUCarrier, hclosure, hcountable, hUEsub⟩ :=
    ColouredSafeEndpointRoofCut.exists_stageTouched_finiteWarp (a := a) C.legal A hA.1
  exact ⟨A, hA, hAX, hEss, U, hU, hUfinite, hUE, hUI, hURoof, hclosure,
    fun _ hx ↦ hAX ⟨hclosure hx.1, hx.2⟩, hcountable, hUEsub⟩

#print axioms endpoint_hasCard_exists_essentialOccurrence_unroofed
#print axioms endpoint_hasCard_exists_protected_roofCut

end Blueprint.LinkageBlueprint.ClubStageGeometry

end Erdos599
