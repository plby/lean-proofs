/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointLocalizationSemantics
import ErdosProblems.Erdos599.ColouredSafeStageWeakSwitch

/-!
# Actual protected weak switching with endpoint-pruned references

The fixed-stage route filter is explicit. Select a degenerate route avoiding
the protected set and the actual inessential carrier, up to its endpoints.
A retained touched prefix cannot meet that carrier at an endpoint, so it
is essential and the touched switch really has finite character. Excluded
endpoint owners need not be disjoint from the original inessential carrier.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- A genuine weak switch and all its reference-source companions, for a
large pruned hammock with an explicitly uniform fixed-stage roof filter. -/
theorem endpoint_weak_hasCard_exists_essentialTouchedSwitch_avoiding
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s t : V} (hne : s ≠ t)
    {extra : Occurrence (reference C.ladder.limitWarp s (some t)) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s (some t)) s (some t) extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    (hnot : ¬HasCard (reference C.ladder.limitWarp s (some t)) s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s (some t)) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s (some t)) s (some t) extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        ∃ T : TouchedWeakSwitch (A.retypeEndpointStageReference C.legal hARoof) t,
          Disjoint (Gamma.vertexSet T.companions) X ∧
          T.connector.support ∩ X ⊆ {s, t} ∧
          Gamma.vertexSet T.paths ⊆ Gamma.roof (C.ladder.frontier a) ∧
          (A.retypeEndpointStageReference C.legal hARoof).touchedReference ⊆
            ladderReference C.ladder a := by
  let bad := C.inessentialCarrierAt a
  have hbad : #bad ≤ kappa := by
    apply DWeb.KappaLadder.Deferred.mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi
      C.legal C.capacity_infinite a
    intro haPhi
    exact Set.disjoint_left.mp C.club_avoids_phi ha haPhi
  let reserve : Set V := X ∪ bad
  have hreserve : #reserve ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite hX hbad)
  have hGlobalWarp : Gamma.IsWarp (reference C.ladder.limitWarp s (some t)) :=
    ColouredSafeEndpointReference.isWarp (C.legal.warpStages (finalStage (succ kappa)))
  have hdeg := h.hasCard_degenerate_of_not_nondegenerate C.capacity_infinite hnot
  obtain ⟨A, hA, havoid⟩ := hdeg.exists_goodRoute_avoiding_referenceClosure
    hGlobalWarp C.capacity_infinite hreserve
  have hgood : A ∈ goodRoutes (reference C.ladder.limitWarp s (some t)) s (some t) extra :=
    ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1⟩
  let hARoof := hroof A hgood.2.2.2.2
  let B := A.retypeEndpointStageReference C.legal hARoof
  have hBvalid : Valid B := hA.1.retypeEndpointStageReference C.legal hARoof
  have hBessential : B.touchedReference ⊆ ladderReference C.ladder a := by
    intro p hp
    by_cases hpEss : p ∈ ladderReference C.ladder a
    · exact hpEss
    · obtain ⟨x, hxp, hxB⟩ := hp.2
      have hxA : x ∈ A.vertexSet := by
        simpa only [B, CurrentSafeOccurrence.retypeEndpointStageReference_vertexSet] using hxB
      have hxBad : x ∈ bad := ⟨p, ⟨stageReference_subset hp.1, hpEss⟩, hxp⟩
      have hxEnds := havoid ⟨Or.inl hxA, Or.inr hxBad⟩
      exact False.elim (Set.disjoint_left.mp
        ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints ⟨p, hp.1, hxp⟩ hxEnds)
  have hBfinite : Gamma.HasFiniteCharacter B.touchedReference :=
    fun hp ↦ ladderReference.finiteCharacter (hBessential hp)
  have htRoof : t ∈ Gamma.roof (C.ladder.frontier a) :=
    hARoof (A.terminal_mem_vertexSet hA.2.1)
  have hBdeg : B.HasFiniteSwitchedPathTo t :=
    (A.hasFiniteSwitchedPathTo_retypeEndpointStageReference_iff
      C.legal hARoof htRoof).mpr hA.2.2.2.2.2
  have hsOff : s ∉ Gamma.vertexSet (stageReference C.legal a s (some t)) := by
    intro hs
    exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
      hs (Or.inl rfl)
  have htOff : t ∉ Gamma.vertexSet (stageReference C.legal a s (some t)) := by
    intro ht
    exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
      ht (Or.inr rfl)
  obtain ⟨T⟩ := hBvalid.exists_touchedWeakSwitch stageReference_isWarp hBfinite
    (by simpa only [B, CurrentSafeOccurrence.retypeEndpointStageReference_terminal?] using hA.2.1)
    hne hsOff htOff hBdeg
  have hBClosure : B.referenceClosure ⊆ A.referenceClosure :=
    A.retypeEndpointStageReference_referenceClosure_subset C.legal hARoof
  have hBX : B.referenceClosure ∩ X ⊆ {s, t} := by
    intro x hx
    simpa only [endpoints_some] using havoid ⟨hBClosure hx.1, Or.inl hx.2⟩
  have hstageRoof : Gamma.vertexSet (C.ladder.warpAt a) ⊆
      Gamma.roof (C.ladder.frontier a) := by
    rw [C.ladder.frontier_eq_essential_terminalFrontier C.legal.roofsSourceAtStages,
      Gamma.roof_essential]
    exact DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier C.legal a
  have hBClosureRoof : B.referenceClosure ⊆ Gamma.roof (C.ladder.frontier a) := by
    apply Set.union_subset
    · simpa only [B, CurrentSafeOccurrence.retypeEndpointStageReference_vertexSet] using hARoof
    · exact meetingVertices_subset_roof Gamma (stageReference C.legal a s (some t)) B.vertexSet _
        (fun p hp x hxp ↦ hstageRoof ⟨p, stageReference_subset hp, hxp⟩)
  refine ⟨A, hgood, hARoof, T, T.companions_disjoint_protected hBX, ?_,
    T.carrier_subset.trans hBClosureRoof, hBessential⟩
  intro x hx
  exact hBX ⟨T.carrier_subset ⟨.inl T.connector, T.connector_mem, hx.1⟩, hx.2⟩

#print axioms endpoint_weak_hasCard_exists_essentialTouchedSwitch_avoiding

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
