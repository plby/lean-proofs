/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeWeakReferenceCompletion

/-!
# Exact retained-reference source coverage after a native weak switch

A newly touched limiting owner cannot simply be discarded from the source
accounting. Its actual stage prefix contributes its initial to a companion
of the local weak switch. Together with the exact carrier identity, this
proves the literal source-coverage condition for the new augmented warp.
No strong-branch construction or fair limiting schedule is assumed here.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa rho : Cardinal.{u}}

/-- The literal meeting-owner difference in blueprint condition (2). -/
def retainedReferenceInitials
    (W : Set (imaginaryWeb Y kappa).DPath) (T : Set V) : Set V :=
  Gamma.initialSet
    (LinkageBlueprint.referencePathsMeeting Y T \
      LinkageBlueprint.referencePathsMeeting Y ((imaginaryWeb Y kappa).vertexSet W))

def CoversSource (W : Set (imaginaryWeb Y kappa).DPath) (T : Set V) : Prop :=
  Gamma.source ⊆ (imaginaryWeb Y kappa).initialSet W ∪ retainedReferenceInitials W T

/-- Source accounting for a genuine change of carrier: a previously retained
owner is either still untouched or has its initial represented in the new warp. -/
theorem coversSource_of_newlyTouched
    {W U : Set (imaginaryWeb Y kappa).DPath} {T : Set V}
    (hcover : CoversSource W T)
    (hinitial : (imaginaryWeb Y kappa).initialSet W ⊆
      (imaginaryWeb Y kappa).initialSet U)
    (hnew : ∀ p ∈ Y, (p.support ∩ T).Nonempty →
      ¬(p.support ∩ (imaginaryWeb Y kappa).vertexSet W).Nonempty →
      (p.support ∩ (imaginaryWeb Y kappa).vertexSet U).Nonempty →
      p.initial ∈ (imaginaryWeb Y kappa).initialSet U) :
    CoversSource U T := by
  intro x hx
  rcases hcover hx with hxOld | hxReference
  · exact Or.inl (hinitial hxOld)
  · obtain ⟨p, hp, hpx⟩ := hxReference
    by_cases hmeet : (p.support ∩ (imaginaryWeb Y kappa).vertexSet U).Nonempty
    · exact Or.inl (hpx ▸ hnew p hp.1.1 hp.1.2 (fun h ↦ hp.2 ⟨hp.1.1, h⟩) hmeet)
    · exact Or.inr ⟨p, ⟨hp.1, fun h ↦ hmeet h.2⟩, hpx⟩

/-- The local switch's actual companions account for every newly touched
limiting reference source, including contacts on the connector itself. -/
theorem coversSource_of_stageWeakSwitch
    {L : Gamma.KappaLadder rho} (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a : Stage rho} {s t : V} {A : Occurrence L.limitWarp s}
    (hARoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (T : TouchedWeakSwitch (A.retypeStageReference hL hARoof) t)
    (hs : s ∉ Gamma.vertexSet (L.warpAt a))
    (hTRoof : Gamma.vertexSet T.paths ⊆ Gamma.roof (L.frontier a))
    {W U : Set (imaginaryWeb L.limitWarp kappa).DPath}
    (hcover : CoversSource W (L.frontier a))
    (hinitial : (imaginaryWeb L.limitWarp kappa).initialSet W ⊆
      (imaginaryWeb L.limitWarp kappa).initialSet U)
    (hcompanion : Gamma.initialSet T.companions ⊆
      (imaginaryWeb L.limitWarp kappa).initialSet U)
    (hcarrier : (imaginaryWeb L.limitWarp kappa).vertexSet U ⊆
      (imaginaryWeb L.limitWarp kappa).vertexSet W ∪ Gamma.vertexSet T.paths) :
    CoversSource U (L.frontier a) := by
  apply coversSource_of_newlyTouched hcover hinitial
  intro p hp hpFrontier hpOld hpNew
  obtain ⟨x, hxp, hxU⟩ := hpNew
  have hxT : x ∈ Gamma.vertexSet T.paths := by
    rcases hcarrier hxU with hxW | hxT
    · exact False.elim (hpOld ⟨x, hxp, hxW⟩)
    · exact hxT
  exact hcompanion (T.limitOwner_initial_mem_companions_of_meets
    hL hARoof hs hTRoof hp hpFrontier ⟨x, hxp, hxT⟩)

/-- An actual protected weak subdivision with companions preserves the
source condition, not merely the union of source carriers. -/
theorem exists_sourceCovered_weakSubdivision
    {L : Gamma.KappaLadder rho} (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a : Stage rho} {s t : V} {A : Occurrence L.limitWarp s}
    (hARoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (T : TouchedWeakSwitch (A.retypeStageReference hL hARoof) t)
    (hs : s ∉ Gamma.vertexSet (L.warpAt a))
    (ht : t ∉ Gamma.vertexSet (L.warpAt a))
    (hTRoof : Gamma.vertexSet T.paths ⊆ Gamma.roof (L.frontier a))
    {W : Set (imaginaryWeb L.limitWarp kappa).DPath}
    (hW : (imaginaryWeb L.limitWarp kappa).IsWarp W)
    (hcover : CoversSource W (L.frontier a))
    (hedge : (s, t) ∈ familyEdges W)
    (hconnector : T.connector.support ∩
      (imaginaryWeb L.limitWarp kappa).vertexSet W ⊆ {s, t})
    (hcompanions : Disjoint (Gamma.vertexSet T.companions)
      ((imaginaryWeb L.limitWarp kappa).vertexSet W)) :
    ∃ U : Set (imaginaryWeb L.limitWarp kappa).DPath,
      (imaginaryWeb L.limitWarp kappa).IsWarp U ∧
      CoversSource U (L.frontier a) ∧
      (imaginaryWeb L.limitWarp kappa).initialSet U =
        (imaginaryWeb L.limitWarp kappa).initialSet W ∪
          Gamma.initialSet (A.retypeStageReference hL hARoof).touchedReference ∧
      (imaginaryWeb L.limitWarp kappa).terminalFrontier U =
        (imaginaryWeb L.limitWarp kappa).terminalFrontier W ∪
          Gamma.terminalFrontier (A.retypeStageReference hL hARoof).touchedReference ∧
      (imaginaryWeb L.limitWarp kappa).vertexSet U =
        ((imaginaryWeb L.limitWarp kappa).vertexSet W ∪ T.connector.support) ∪
          Gamma.vertexSet T.companions := by
  obtain ⟨U, hU, hUI, hUT, hUV⟩ :=
    exists_weakSubdivision_with_companions T hs ht hW hedge hconnector hcompanions
  refine ⟨U, hU, ?_, hUI, hUT, hUV⟩
  apply coversSource_of_stageWeakSwitch hL hARoof T hs hTRoof hcover
  · rw [hUI]
    exact Set.subset_union_left
  · rw [hUI, T.companions_initialSet hs]
    exact Set.subset_union_right
  · rw [hUV]
    rintro x ((hxW | hxConnector) | hxCompanion)
    · exact Or.inl hxW
    · exact Or.inr ⟨.inl T.connector, T.connector_mem, hxConnector⟩
    · obtain ⟨p, hp, hxp⟩ := hxCompanion
      exact Or.inr ⟨p, hp.1, hxp⟩

#print axioms coversSource_of_newlyTouched
#print axioms coversSource_of_stageWeakSwitch
#print axioms exists_sourceCovered_weakSubdivision

end Erdos599.Blueprint.ColouredSafeShortcutGraph
