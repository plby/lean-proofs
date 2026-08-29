/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageRoofCutRelation
import ErdosProblems.Erdos599.ColouredSafeStageStrongSwitch

/-!
# Protected selection for the actual fixed-stage roof cut

Reserve the protected set and the inessential carrier before choosing a
global native occurrence. No uniform roof-containment filter is needed.
The realized roof-cut family is countable, avoids the protected carrier
apart from the exposed ends, and stays in the global reference closure of
the chosen occurrence. Boundary accounting is deliberately not asserted.
-/

noncomputable section

namespace Erdos599

open Set Cardinal Order DirectedPath Alternating Ladder Blueprint
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace ColouredSafeStageRoofCutRelation

variable {L : Gamma.KappaLadder kappa} {a : Stage kappa} {s : V}

/-- Each touched essential stage owner is a literal prefix of a limiting
owner touched by the same occurrence. This uses no roofedness of the word. -/
theorem vertexSet_stageTouchedReference_subset_referenceClosure
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : Occurrence L.limitWarp s) :
    Gamma.vertexSet (stageTouchedReference (a := a) A) ⊆ A.referenceClosure := by
  rintro x ⟨p, hp, hxp⟩
  let E := hL.stageReferenceEmbedding a
  let q := E.owner ⟨p, hp.1.1⟩
  obtain ⟨y, hyp, hyA⟩ := hp.2
  exact Or.inr (support_subset_meetingVertices Gamma L.limitWarp A.vertexSet q.2
    ⟨y, E.support_subset ⟨p, hp.1.1⟩ hyp, hyA⟩
    (E.support_subset ⟨p, hp.1.1⟩ hxp))

/-- The canonical exact realization can be chosen within the original
global reference closure, as well as within the fixed stage roof. -/
theorem exists_stageTouched_finiteWarp_in_referenceClosure
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : Occurrence L.limitWarp s) (hA : Valid A) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = edges A (stageTouchedReference (a := a) A) (L.frontier a) ∧
      isolatedVertices U = isolatedVertices (stageTouchedReference (a := a) A) ∧
      Gamma.vertexSet U ⊆ Gamma.roof (L.frontier a) ∧
      Gamma.vertexSet U ⊆ A.referenceClosure ∧
      (Gamma.vertexSet U).Countable := by
  obtain ⟨U, hU, hUfinite, hUE, hUI, hroof, hcarrier⟩ :=
    exists_finiteWarp_roofed hL A hA (stageTouchedReference (a := a) A)
      (stageTouchedReference_isWarp hL A)
      (stageTouchedReference_finiteCharacter A)
      (fun _ hp ↦ hp.1.1) (L.frontier a)
      (L.frontiersAreEssential_of_roofsSourceAtStages hL.roofsSourceAtStages a)
      (stageTouchedReference_terminal_subset hL A)
      (stageTouchedReference_vertexSet_subset_roof hL A)
  refine ⟨U, hU, hUfinite, hUE, hUI, hroof, ?_, ?_⟩
  · exact hcarrier.trans (Set.union_subset
      (vertexSet_stageTouchedReference_subset_referenceClosure hL A)
      Set.subset_union_left)
  · exact ((vertexSet_stageTouchedReference_countable hL A).union
      A.vertexSet_countable).mono hcarrier

end ColouredSafeStageRoofCutRelation

namespace Blueprint.LinkageBlueprint.ClubStageGeometry

variable {Y : Set Gamma.DPath}

/-- Protected global selection does not require stage capture. The whole
reference closure avoids the inessential carrier, not just the word. -/
theorem native_global_hasCard_exists_occurrence_avoiding_stageInessential
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s : V} {e : Option V}
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s e extra (succ kappa))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence C.ladder.limitWarp s,
      A ∈ goodRoutes C.ladder.limitWarp s e extra ∧
      A.referenceClosure ∩ X ⊆ endpoints s e ∧
      Disjoint A.referenceClosure (C.inessentialCarrierAt a) ∧
      ∀ p ∈ C.ladder.warpAt a, (p.support ∩ A.vertexSet).Nonempty →
        p ∈ ladderReference C.ladder a := by
  let bad := C.inessentialCarrierAt a
  have hbad : #bad ≤ kappa := by
    apply DWeb.KappaLadder.Deferred.mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi
      C.legal C.capacity_infinite a
    intro haPhi
    exact Set.disjoint_left.mp C.club_avoids_phi ha haPhi
  have hreserve : #(X ∪ bad : Set V) ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite hX hbad)
  obtain ⟨A, hA, havoid⟩ := h.exists_goodRoute_avoiding_referenceClosure
    (C.legal.warpStages (finalStage (succ kappa))) C.capacity_infinite hreserve
  have hbadGlobal : bad ⊆ Gamma.vertexSet C.ladder.limitWarp := by
    rintro x ⟨p, hp, hxp⟩
    exact ⟨p, C.legal.mem_limitWarp_of_mem_inessential hp, hxp⟩
  have hAbad : Disjoint A.referenceClosure bad := by
    apply Set.disjoint_left.mpr
    intro x hxA hxBad
    rcases havoid ⟨hxA, Or.inr hxBad⟩ with hxs | hxt
    · exact hA.2.2.1 (Set.mem_singleton_iff.mp hxs ▸ hbadGlobal hxBad)
    · exact hA.2.2.2.1 x hxt (hbadGlobal hxBad)
  refine ⟨A, hA, fun _ hx ↦ havoid ⟨hx.1, Or.inl hx.2⟩, hAbad, ?_⟩
  intro p hp hmeet
  by_contra hpEss
  obtain ⟨x, hxp, hxA⟩ := hmeet
  have hxBad : x ∈ bad := ⟨p, ⟨hp, hpEss⟩, hxp⟩
  exact Set.disjoint_left.mp hAbad (Or.inl hxA) hxBad

/-- An actual protected countable roof-cut warp selected from a large
global hammock. The source and terminal sets are not inferred from mere
relation realization; those require the separate boundary argument. -/
theorem native_global_hasCard_exists_protected_roofCut
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s : V} {e : Option V}
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s e extra (succ kappa))
    {X : Set V} (hX : #X ≤ kappa) :
    ∃ A : Occurrence C.ladder.limitWarp s,
      A ∈ goodRoutes C.ladder.limitWarp s e extra ∧
      A.referenceClosure ∩ X ⊆ endpoints s e ∧
      Disjoint A.referenceClosure (C.inessentialCarrierAt a) ∧
      ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
        familyEdges U = ColouredSafeStageRoofCutRelation.edges A
          (ColouredSafeStageRoofCutRelation.stageTouchedReference (a := a) A)
          (C.ladder.frontier a) ∧
        Gamma.vertexSet U ⊆ Gamma.roof (C.ladder.frontier a) ∧
        Gamma.vertexSet U ⊆ A.referenceClosure ∧
        Gamma.vertexSet U ∩ X ⊆ endpoints s e ∧
        (Gamma.vertexSet U).Countable := by
  obtain ⟨A, hA, hAX, hAbad, _hTouched⟩ :=
    C.native_global_hasCard_exists_occurrence_avoiding_stageInessential ha h hX
  obtain ⟨U, hU, hUfinite, hUE, _hUI, hroof, hcarrier, hcountable⟩ :=
    ColouredSafeStageRoofCutRelation.exists_stageTouched_finiteWarp_in_referenceClosure
      (a := a) C.legal A hA.1
  exact ⟨A, hA, hAX, hAbad, U, hU, hUfinite, hUE, hroof, hcarrier,
    fun _ hx ↦ hAX ⟨hcarrier hx.1, hx.2⟩, hcountable⟩

#print axioms native_global_hasCard_exists_occurrence_avoiding_stageInessential
#print axioms native_global_hasCard_exists_protected_roofCut

end Blueprint.LinkageBlueprint.ClubStageGeometry

end Erdos599
