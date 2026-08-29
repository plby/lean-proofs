/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageRoofCutSwitch

/-!
# The exposed roof-cut source is strictly roofed

Nonemptiness of a native hammock already says that its exposed source is
outside the limiting reference.  Since every deferred-ladder frontier is
carried by that reference, ordinary roof membership upgrades to strict-roof
membership.  This removes the only artificial geometric premise from the
selected roof-cut switch interface.
-/

noncomputable section

namespace Erdos599

open Set Cardinal Order DirectedPath Alternating Ladder Blueprint
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {rho kappa : Cardinal.{u}}

namespace Blueprint.ColouredSafeHammock

/-- A successor-sized native hammock has a good member, so its exposed
source is outside the reference. -/
theorem HasCard.source_not_mem_reference
    {s : V} {e : Option V} {extra : Occurrence Y s → Prop}
    (h : HasCard Y s e extra (succ rho)) :
    s ∉ Gamma.vertexSet Y := by
  obtain ⟨H, hH, hcard⟩ := h
  obtain ⟨A, _hAH, hgood, _hdisjoint⟩ :=
    exists_mem_avoiding (X := (∅ : Set V)) hH hcard (by simp)
  exact hgood.2.2.1

#print axioms HasCard.source_not_mem_reference

end Blueprint.ColouredSafeHammock

namespace DWeb.KappaLadder.Deferred

/-- Every selected deferred-ladder frontier point lies on a limiting
reference component.  This uses the actual stage-to-limit embedding and
does not pass through legacy split legality. -/
theorem frontier_subset_vertexSet_limitWarp
    {L : Gamma.KappaLadder kappa} (hL : HalfwayGeometry L)
    (a : Stage kappa) :
    L.frontier a ⊆ Gamma.vertexSet L.limitWarp := by
  intro x hx
  have hxTerminal : x ∈ Gamma.terminalFrontier
      (LinkageBlueprint.ladderReference L a) := by
    rw [LinkageBlueprint.ladderReference.terminalFrontier_eq hL]
    exact hx
  obtain ⟨p, hp, hpx⟩ := hxTerminal
  let E := hL.stageReferenceEmbedding a
  exact ⟨(E.owner ⟨p, hp.1⟩).1, (E.owner ⟨p, hp.1⟩).2,
    E.support_subset ⟨p, hp.1⟩ (Gamma.terminal_mem_support hpx)⟩

/-- A point below the stage frontier but outside the limiting reference is
strictly below that frontier. -/
theorem mem_strictRoof_of_mem_roof_of_not_mem_limitWarp
    {L : Gamma.KappaLadder kappa} (hL : HalfwayGeometry L)
    {a : Stage kappa} {s : V} (hsRoof : s ∈ Gamma.roof (L.frontier a))
    (hsOff : s ∉ Gamma.vertexSet L.limitWarp) :
    s ∈ Gamma.strictRoof (L.frontier a) := by
  refine ⟨hsRoof, ?_⟩
  intro hsEssential
  exact hsOff (frontier_subset_vertexSet_limitWarp hL a
    (Gamma.essential_subset (L.frontier a) hsEssential))

#print axioms frontier_subset_vertexSet_limitWarp
#print axioms mem_strictRoof_of_mem_roof_of_not_mem_limitWarp

end DWeb.KappaLadder.Deferred

namespace Blueprint.ColouredSafeHammock

/-- Native hammock nonemptiness supplies the missing strictness once the
ambient construction gives ordinary source roof membership. -/
theorem HasCard.source_mem_strictRoof
    {L : Gamma.KappaLadder kappa}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a : Stage kappa} {s : V} {e : Option V}
    {extra : Occurrence L.limitWarp s → Prop}
    (h : HasCard L.limitWarp s e extra (succ rho))
    (hsRoof : s ∈ Gamma.roof (L.frontier a)) :
    s ∈ Gamma.strictRoof (L.frontier a) :=
  DWeb.KappaLadder.Deferred.mem_strictRoof_of_mem_roof_of_not_mem_limitWarp
    hL hsRoof h.source_not_mem_reference

#print axioms HasCard.source_mem_strictRoof

end Blueprint.ColouredSafeHammock

namespace Blueprint.LinkageBlueprint.ClubStageGeometry

open Blueprint.ColouredSafeHammock

/-- Source-roof form of the selected pruned roof-cut theorem. -/
theorem native_global_hasCard_exists_prunedRoofCut_of_sourceRoof
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club) {s : V} {e : Option V}
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s e extra (succ kappa))
    {X : Set V} (hX : #X ≤ kappa)
    (hsRoof : s ∈ Gamma.roof (C.ladder.frontier a))
    (hsTerminal : ∀ t, e = some t → s ≠ t) :
    ∃ A : Occurrence C.ladder.limitWarp s,
      A ∈ goodRoutes C.ladder.limitWarp s e extra ∧
      A.referenceClosure ∩ X ⊆ endpoints s e ∧
      Disjoint A.referenceClosure (C.inessentialCarrierAt a) ∧
      ∃ P : Set Gamma.DPath,
        Gamma.IsWarp P ∧ Gamma.HasFiniteCharacter P ∧
        Gamma.initialSet P = Gamma.initialSet
          (ColouredSafeStageRoofCutRelation.stageTouchedReference (a := a) A) ∪ {s} ∧
        Gamma.terminalFrontier P ⊆
          C.ladder.frontier a ∪ {x | e = some x} ∧
        Gamma.vertexSet P ⊆ Gamma.roof (C.ladder.frontier a) ∧
        Gamma.vertexSet P ⊆ Gamma.vertexSet
          (ColouredSafeStageRoofCutRelation.stageTouchedReference (a := a) A) ∪
            A.vertexSet ∧
        Gamma.vertexSet P ⊆ A.referenceClosure ∧
        Gamma.vertexSet P ∩ X ⊆ endpoints s e ∧
        (Gamma.vertexSet P).Countable ∧
        familyEdges P ⊆ A.switchedEdges := by
  exact C.native_global_hasCard_exists_prunedRoofCut ha h hX
    (h.source_mem_strictRoof C.legal hsRoof) hsTerminal

#print axioms native_global_hasCard_exists_prunedRoofCut_of_sourceRoof

end Blueprint.LinkageBlueprint.ClubStageGeometry

end Erdos599
