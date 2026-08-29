/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReferenceRoofCutBoundary
import ErdosProblems.Erdos599.ColouredSafeEndpointRoofCutAccounting

/-!
# Actual protected rooted endpoint-pruned roof cuts

The selected retained prefixes supply all erased incidences required for
the balance inequality. Their frontier points are their actual terminals.
The resulting rooted finite warp retains exactly the touched-reference
initials and the source, with no uniform roof filter on the occurrence.
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

theorem frontier_mem_terminal_of_mem_stageTouchedReference
    (hL : HalfwayGeometry L) (A : Occurrence (reference L.limitWarp s e) s)
    {x : V} (hx : x ∈ Gamma.vertexSet (stageTouchedReference hL a A))
    (hxT : x ∈ L.frontier a) : x ∈ Gamma.terminalFrontier (stageTouchedReference hL a A) := by
  obtain ⟨p, hp, hxp⟩ := hx
  rw [← LinkageBlueprint.ladderReference.terminalFrontier_eq hL] at hxT
  obtain ⟨q, hq, hqx⟩ := hxT
  have hpq : p = q := DWeb.IsWarp.eq_of_mem_support
    (LinkageBlueprint.ladderReference.isWarp hL) hp.2.1 hq hxp (Gamma.terminal_mem_support hqx)
  exact ⟨p, hp, hpq ▸ hqx⟩

theorem exists_rooted_roofCut (hL : HalfwayGeometry L)
    (A : Occurrence (reference L.limitWarp s e) s) (hA : Valid A) (hAT : A.terminal? = e)
    (hEss : ∀ p ∈ stageReference hL a s e, (p.support ∩ A.vertexSet).Nonempty →
      p ∈ LinkageBlueprint.ladderReference L a)
    (hsStrict : s ∈ Gamma.strictRoof (L.frontier a))
    (hsTerminal : ∀ t, e = some t → s ≠ t) :
    ∃ P : Set Gamma.DPath, Gamma.IsWarp P ∧ Gamma.HasFiniteCharacter P ∧
      Gamma.initialSet P = Gamma.initialSet (stageTouchedReference hL a A) ∪ {s} ∧
      Gamma.terminalFrontier P ⊆ L.frontier a ∪ {x | e = some x} ∧
      Gamma.vertexSet P ⊆ Gamma.roof (L.frontier a) ∧
      Gamma.vertexSet P ⊆ Gamma.vertexSet (stageTouchedReference hL a A) ∪ A.vertexSet ∧
      Gamma.vertexSet P ⊆ A.referenceClosure ∧ (Gamma.vertexSet P).Countable ∧
      familyEdges P ⊆ A.switchedEdges := by
  have hG : Gamma.IsWarp (reference L.limitWarp s e) :=
    ColouredSafeEndpointReference.isWarp (hL.warpStages (finalStage rho))
  have hOff : Disjoint (Gamma.vertexSet (stageTouchedReference hL a A)) (endpoints s e) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨p, hp, hxp⟩ hx
    exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
      ⟨p, hp.1, hxp⟩ hx
  have hLower := fun x (hxA : x ∈ A.vertexSet)
      (hxStrict : x ∈ Gamma.strictRoof (L.frontier a)) ↦
    ColouredSafeReferenceRoofCut.balance_lower hG A hA
      (stageTouchedReference_isWarp hL A) (stageTouchedReference_edges_subset hL A)
      hxStrict
      (fun y hy ↦ ((incoming_backwardEdges_iff hL A hEss hxA hxStrict.1).2 hy).2)
      (fun y hy ↦ ((outgoing_backwardEdges_iff hL A hEss hxA hxStrict).2 hy).2)
  obtain ⟨P, hP, hPfinite, hPI, hPT, hPRoof, hPCarrier, hPE⟩ :=
    ColouredSafeReferenceRoofCut.exists_rooted_finiteWarp hG A hA
      (stageTouchedReference hL a A) (stageTouchedReference_isWarp hL A)
      (stageTouchedReference_finiteCharacter hL A) (stageTouchedReference_edges_subset hL A)
      (stageTouchedReference_initials_subset hL A) (L.frontier a)
      (L.frontiersAreEssential_of_roofsSourceAtStages hL.roofsSourceAtStages a)
      (stageTouchedReference_terminals_subset hL A)
      (stageTouchedReference_vertexSet_subset_roof hL A)
      (fun _ hx hxT ↦ frontier_mem_terminal_of_mem_stageTouchedReference hL A hx hxT)
      hLower (fun t ht hx ↦ Set.disjoint_left.mp hOff hx (Or.inr (hAT.symm.trans ht)))
      hsStrict (fun hx ↦ Set.disjoint_left.mp hOff hx (Or.inl rfl))
      (fun t ht ↦ hsTerminal t (hAT.symm.trans ht))
  have hclosure : Gamma.vertexSet P ⊆ A.referenceClosure :=
    hPCarrier.trans (Set.union_subset
      (stageTouchedReference_vertexSet_subset_referenceClosure hL A) Set.subset_union_left)
  refine ⟨P, hP, hPfinite, hPI, ?_, hPRoof, hPCarrier, hclosure,
    (A.referenceClosure_countable hG).mono hclosure, ?_⟩
  · simpa only [hAT] using hPT
  · exact hPE.trans (ColouredSafeReferenceRoofCut.edges_subset_switchedEdges A
      (stageTouchedReference_edges_subset hL A) (L.frontier a))

#print axioms exists_rooted_roofCut

end Blueprint.ColouredSafeEndpointRoofCut

namespace Blueprint.LinkageBlueprint.ClubStageGeometry

variable {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem endpoint_hasCard_exists_protected_rooted_roofCut
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s : V} {e : Option V}
    {extra : Occurrence (reference C.ladder.limitWarp s e) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s e) s e extra (succ kappa))
    {X : Set V} (hX : #X ≤ kappa)
    (hsStrict : s ∈ Gamma.strictRoof (C.ladder.frontier a))
    (hsTerminal : ∀ t, e = some t → s ≠ t) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s e) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s e) s e extra ∧
      ∃ P : Set Gamma.DPath, Gamma.IsWarp P ∧ Gamma.HasFiniteCharacter P ∧
        Gamma.initialSet P = Gamma.initialSet
          (ColouredSafeEndpointRoofCut.stageTouchedReference C.legal a A) ∪ {s} ∧
        Gamma.terminalFrontier P ⊆ C.ladder.frontier a ∪ {x | e = some x} ∧
        Gamma.vertexSet P ⊆ Gamma.roof (C.ladder.frontier a) ∧
        Gamma.vertexSet P ⊆ Gamma.vertexSet
          (ColouredSafeEndpointRoofCut.stageTouchedReference C.legal a A) ∪ A.vertexSet ∧
        Gamma.vertexSet P ⊆ A.referenceClosure ∧
        Gamma.vertexSet P ∩ X ⊆ endpoints s e ∧
        (Gamma.vertexSet P).Countable ∧ familyEdges P ⊆ A.switchedEdges := by
  obtain ⟨A, hA, hAX, hEss⟩ := C.endpoint_hasCard_exists_essentialOccurrence_unroofed ha h hX
  obtain ⟨P, hP, hPfinite, hPI, hPT, hPRoof, hPCarrier, hclosure, hcountable, hPE⟩ :=
    ColouredSafeEndpointRoofCut.exists_rooted_roofCut C.legal A hA.1 hA.2.1
      hEss hsStrict hsTerminal
  exact ⟨A, hA, P, hP, hPfinite, hPI, hPT, hPRoof, hPCarrier, hclosure,
    fun _ hx ↦ hAX ⟨hclosure hx.1, hx.2⟩, hcountable, hPE⟩

#print axioms endpoint_hasCard_exists_protected_rooted_roofCut

end Blueprint.LinkageBlueprint.ClubStageGeometry

end Erdos599
