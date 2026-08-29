/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageStrongSwitch
import ErdosProblems.Erdos599.ColouredSafeWeakBlueprintTransaction

/-!
# Source accounting for the native strong two-port replacement

Every newly touched limiting owner contributes its initial to the complete
local switch's reference-initial set. A two-port insertion retains that set
in its new initials, including the path prepended to the old suffix. This
is the exact source condition, not mere containment in the new carrier.
-/

noncomputable section

namespace Erdos599.ColouredSafeAmbientOccurrence.TouchedStrongSwitch

open Set Cardinal Order DirectedPath Ladder Blueprint
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {s t : V}
variable {A : Occurrence Y s}

theorem initials_sdiff_source (T : TouchedStrongSwitch A t)
    (hs : s ∉ Gamma.vertexSet Y) :
    Gamma.initialSet T.paths \ {s} = Gamma.initialSet A.touchedReference := by
  rw [T.initials]
  have hsLocal : s ∉ Gamma.initialSet A.touchedReference := by
    rintro ⟨p, hp, hps⟩
    exact hs ⟨p, hp.1, hps ▸ p.initial_mem_support⟩
  ext x
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx | hx, hne⟩
    · exact hx
    · exact False.elim (hne hx)
  · intro hx
    exact ⟨Or.inl hx, fun hxs ↦ hsLocal (hxs ▸ hx)⟩

theorem terminals_sdiff_end (T : TouchedStrongSwitch A t)
    (ht : t ∉ Gamma.vertexSet Y) :
    Gamma.terminalFrontier T.paths \ {t} =
      Gamma.terminalFrontier A.touchedReference := by
  rw [T.terminals]
  have htLocal : t ∉ Gamma.terminalFrontier A.touchedReference := by
    rintro ⟨p, hp, hpt⟩
    exact ht ⟨p, hp.1, Gamma.terminal_mem_support hpt⟩
  ext x
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx | hx, hne⟩
    · exact hx
    · exact False.elim (hne hx)
  · intro hx
    exact ⟨Or.inl hx, fun hxt ↦ htLocal (hxt ▸ hx)⟩

theorem limitOwner_initial_mem_touchedReference_of_meets
    {rho : Cardinal.{u}} {L : Gamma.KappaLadder rho} {a : Stage rho}
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {A : Occurrence L.limitWarp s}
    (hARoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (T : TouchedStrongSwitch (A.retypeStageReference hL hARoof) t)
    (hTRoof : Gamma.vertexSet T.paths ⊆ Gamma.roof (L.frontier a))
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    (hfrontier : (p.support ∩ L.frontier a).Nonempty)
    (hmeet : (p.support ∩ Gamma.vertexSet T.paths).Nonempty) :
    p.initial ∈ Gamma.initialSet (A.retypeStageReference hL hARoof).touchedReference := by
  obtain ⟨v, hvp, hvFrontier⟩ := hfrontier
  obtain ⟨q, hq, _hqTerminal, hqp⟩ :=
    LinkageBlueprint.ladderReference.exists_prefix_of_limitWarp_frontier_hit
      hL hp hvFrontier hvp
  obtain ⟨x, hxp, hxT⟩ := hmeet
  have hxq : x ∈ q.support :=
    DWeb.KappaLadder.Deferred.limitComponent_support_inter_roof_subset_prefix
      hL a hp hq.1 hqp ⟨hxp, hTRoof hxT⟩
  have hqTouched :=
    (A.retypeStageReference hL hARoof).mem_touchedReference_of_meets_referenceClosure
      (hL.warpStages (Stage.toExtended a)) hq.1 ⟨x, hxq, T.carrier_subset hxT⟩
  exact ⟨q, hqTouched, Gamma.extends_initial hqp⟩

#print axioms initials_sdiff_source
#print axioms terminals_sdiff_end
#print axioms limitOwner_initial_mem_touchedReference_of_meets

end Erdos599.ColouredSafeAmbientOccurrence.TouchedStrongSwitch

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Ladder
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa rho : Cardinal.{u}}
variable {Y : Set Gamma.DPath}

theorem coversSource_of_stageStrongSwitch
    {L : Gamma.KappaLadder rho} (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {a : Stage rho} {s t : V} {A : Occurrence L.limitWarp s}
    (hARoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (T : TouchedStrongSwitch (A.retypeStageReference hL hARoof) t)
    (hTRoof : Gamma.vertexSet T.paths ⊆ Gamma.roof (L.frontier a))
    {W U : Set (imaginaryWeb L.limitWarp kappa).DPath}
    (hcover : CoversSource W (L.frontier a))
    (hinitial : (imaginaryWeb L.limitWarp kappa).initialSet W ⊆
      (imaginaryWeb L.limitWarp kappa).initialSet U)
    (hreference : Gamma.initialSet (A.retypeStageReference hL hARoof).touchedReference ⊆
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
  exact hreference (T.limitOwner_initial_mem_touchedReference_of_meets
    hL hARoof hTRoof hp hpFrontier ⟨x, hxp, hxT⟩)

#print axioms coversSource_of_stageStrongSwitch

/-- Exact two-port geometry preserves all six native conditions. The
actual path-family construction supplies these identities separately. -/
theorem isLinkageBlueprint_of_stageStrongSwitch
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} {Z persistent : Set V}
    (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    {s t : V} {A : Occurrence C.ladder.limitWarp s}
    (hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    (T : TouchedStrongSwitch (A.retypeStageReference C.legal hARoof) t)
    (hs : s ∉ Gamma.vertexSet (C.ladder.warpAt a))
    (ht : t ∉ Gamma.vertexSet (C.ladder.warpAt a))
    (hTRoof : Gamma.vertexSet T.paths ⊆ Gamma.roof (C.ladder.frontier a))
    (hAClosed : A.vertexSet ⊆ Z)
    (hEss : (A.retypeStageReference C.legal hARoof).touchedReference ⊆
      LinkageBlueprint.ladderReference C.ladder a)
    {U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hU : (imaginaryWeb C.ladder.limitWarp kappa).IsWarp U)
    (hUI : (imaginaryWeb C.ladder.limitWarp kappa).initialSet U =
      (imaginaryWeb C.ladder.limitWarp kappa).initialSet W ∪
        (Gamma.initialSet T.paths \ {s}))
    (hUT : (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U =
      (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W ∪
        (Gamma.terminalFrontier T.paths \ {t}))
    (hUV : (imaginaryWeb C.ladder.limitWarp kappa).vertexSet U =
      (imaginaryWeb C.ladder.limitWarp kappa).vertexSet W ∪ Gamma.vertexSet T.paths)
    (htrace : ∀ r : Ray (imaginaryWeb C.ladder.limitWarp kappa).graph, Sum.inr r ∈ U →
      ∃ r0 : Ray (imaginaryWeb C.ladder.limitWarp kappa).graph, Sum.inr r0 ∈ W ∧
        ∃ lost : Set (V × V), lost.Finite ∧ r0.edgeSet \ lost ⊆ r.edgeSet) :
    IsLinkageBlueprint U (C.ladder.frontier a) Z persistent := by
  let D := imaginaryWeb C.ladder.limitWarp kappa
  rw [T.initials_sdiff_source hs] at hUI
  rw [T.terminals_sdiff_end ht] at hUT
  have hcover : CoversSource U (C.ladder.frontier a) := by
    apply coversSource_of_stageStrongSwitch C.legal hARoof T hTRoof hW.covers_source
    · rw [hUI]
      exact Set.subset_union_left
    · rw [hUI]
      exact Set.subset_union_right
    · exact le_of_eq hUV
  have hTClosed : Gamma.vertexSet T.paths ⊆ Z :=
    T.carrier_subset.trans
      ((A.retypeStageReference_referenceClosure_subset C.legal hARoof).trans
        (A.referenceClosure_subset_of_closedUnderPaths hZ hAClosed))
  have hWcard : #(D.vertexSet W) ≤ kappa :=
    CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
      C.capacity_infinite W hW.card_paths
  have hUcard : #(D.vertexSet U) ≤ kappa := by
    rw [hUV]
    exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le
      C.capacity_infinite hWcard (T.carrier_countable.le_aleph0.trans C.capacity_infinite))
  have hnewTerminals : Gamma.terminalFrontier
      (A.retypeStageReference C.legal hARoof).touchedReference ⊆ C.ladder.frontier a := by
    rintro x ⟨p, hp, hpx⟩
    rw [← LinkageBlueprint.ladderReference.terminalFrontier_eq C.legal]
    exact ⟨p, hEss hp, hpx⟩
  exact {
    isWarp := hU
    vertices_roofed := by
      rw [hUV]
      exact Set.union_subset hW.vertices_roofed hTRoof
    covers_source := hcover
    vertices_closed := by
      rw [hUV]
      exact Set.union_subset hW.vertices_closed hTClosed
    card_paths := (mk_paths_le_vertexSet hU).trans hUcard
    infinitely_many_strong := DWeb.infinitelyManyMarkedEdges_of_finite_rayTrace
      hW.infinitely_many_strong htrace
    terminals_popular := by
      rw [hUT]
      exact Set.union_subset hW.terminals_popular
        (hnewTerminals.trans Set.subset_union_right) }

#print axioms isLinkageBlueprint_of_stageStrongSwitch

end Erdos599.Blueprint.ColouredSafeShortcutGraph
