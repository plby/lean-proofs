/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageRoofCutSelection
import ErdosProblems.Erdos599.ColouredSafeWeakSourceCoverage

/-!
# Source accounting for a roof-cut carrier

Only the replacement carrier, not the whole global occurrence, has to lie
in the displayed roof. A newly touched limiting owner then contributes its
unchanged initial through an actually touched essential stage prefix.
Preservation of those local initials is a separate explicit hypothesis.
-/

noncomputable section

namespace Erdos599

open Set Cardinal Order DirectedPath Alternating Ladder Blueprint
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {rho kappa : Cardinal.{u}}

namespace ColouredSafeStageRoofCutRelation

variable {L : Gamma.KappaLadder rho} {a : Stage rho} {s : V}

/-- The literal cropped relation is contained in the full global switched
relation even when the occurrence leaves and reenters the stage roof. -/
theorem edges_subset_switchedEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : Occurrence L.limitWarp s) {Y : Set Gamma.DPath}
    (hY : Y ⊆ L.warpAt a) (T : Set V) :
    edges A Y T ⊆ A.switchedEdges := by
  rintro e (he | he)
  · refine Or.inl ⟨?_, fun hback ↦ he.2 ⟨hback, he.1⟩⟩
    apply (hL.stageReferenceEmbedding a).familyEdges_subset
    have hlocal := he.1
    simp only [familyEdges, Set.mem_iUnion] at hlocal ⊢
    obtain ⟨p, hp, hep⟩ := hlocal
    exact ⟨p, hY hp, hep⟩
  · exact Or.inr he.1

/-- A limiting owner meeting the frontier and a roof-cut carrier has its
initial in the actual touched stage reference. The whole occurrence need
not be roofed. The carrier-union bound is essential. -/
theorem limitOwner_initial_mem_stageTouchedReference_of_meets
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : Occurrence L.limitWarp s) {K : Set V}
    (hKroof : K ⊆ Gamma.roof (L.frontier a))
    (hKcarrier : K ⊆
      Gamma.vertexSet (stageTouchedReference (a := a) A) ∪ A.vertexSet)
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    (hfrontier : (p.support ∩ L.frontier a).Nonempty)
    (hmeet : (p.support ∩ K).Nonempty) :
    p.initial ∈ Gamma.initialSet (stageTouchedReference (a := a) A) := by
  obtain ⟨v, hvp, hvFrontier⟩ := hfrontier
  obtain ⟨q, hq, _hqTerminal, hqp⟩ :=
    LinkageBlueprint.ladderReference.exists_prefix_of_limitWarp_frontier_hit
      hL hp hvFrontier hvp
  obtain ⟨x, hxp, hxK⟩ := hmeet
  have hxq : x ∈ q.support :=
    DWeb.KappaLadder.Deferred.limitComponent_support_inter_roof_subset_prefix
      hL a hp hq.1 hqp ⟨hxp, hKroof hxK⟩
  have hqTouched : q ∈ stageTouchedReference (a := a) A := by
    rcases hKcarrier hxK with hxY | hxA
    · obtain ⟨r, hr, hxr⟩ := hxY
      have hqr : q = r := by
        by_contra hne
        exact Set.disjoint_left.mp
          (hL.warpStages (Stage.toExtended a) hq.1 hr.1.1 hne) hxq hxr
      exact hqr ▸ hr
    · exact ⟨hq, x, hxq, hxA⟩
  exact ⟨q, hqTouched, Gamma.extends_initial hqp⟩

#print axioms edges_subset_switchedEdges
#print axioms limitOwner_initial_mem_stageTouchedReference_of_meets

end ColouredSafeStageRoofCutRelation

namespace Blueprint.ColouredSafeShortcutGraph

/-- A roof-cut insertion preserves blueprint source coverage provided it
retains the old initials and the actual touched stage-reference initials.
These boundary hypotheses must come from the real local construction. -/
theorem coversSource_of_roofCut
    {L : Gamma.KappaLadder rho} (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a : Stage rho} {s : V} (A : Occurrence L.limitWarp s) {K : Set V}
    (hKroof : K ⊆ Gamma.roof (L.frontier a))
    (hKcarrier : K ⊆ Gamma.vertexSet
      (ColouredSafeStageRoofCutRelation.stageTouchedReference (a := a) A) ∪ A.vertexSet)
    {W U : Set (imaginaryWeb L.limitWarp kappa).DPath}
    (hcover : CoversSource W (L.frontier a))
    (hinitial : (imaginaryWeb L.limitWarp kappa).initialSet W ⊆
      (imaginaryWeb L.limitWarp kappa).initialSet U)
    (hreference : Gamma.initialSet
      (ColouredSafeStageRoofCutRelation.stageTouchedReference (a := a) A) ⊆
        (imaginaryWeb L.limitWarp kappa).initialSet U)
    (hcarrier : (imaginaryWeb L.limitWarp kappa).vertexSet U ⊆
      (imaginaryWeb L.limitWarp kappa).vertexSet W ∪ K) :
    CoversSource U (L.frontier a) := by
  apply coversSource_of_newlyTouched hcover hinitial
  intro p hp hpFrontier hpOld hpNew
  obtain ⟨x, hxp, hxU⟩ := hpNew
  have hxK : x ∈ K := by
    rcases hcarrier hxU with hxW | hxK
    · exact False.elim (hpOld ⟨x, hxp, hxW⟩)
    · exact hxK
  exact hreference
    (ColouredSafeStageRoofCutRelation.limitOwner_initial_mem_stageTouchedReference_of_meets
      hL A hKroof hKcarrier hp hpFrontier ⟨x, hxp, hxK⟩)

#print axioms coversSource_of_roofCut

end Blueprint.ColouredSafeShortcutGraph

end Erdos599
