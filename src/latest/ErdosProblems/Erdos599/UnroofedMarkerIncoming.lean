/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerEssential
import ErdosProblems.Erdos599.GroundingSuccessorRoofTransport

/-!
# Incoming-edge reflection for the actual unroofed ladder

The head of a new rung edge is outside the complete old roof. At a genuine
limit every edge comes from an earlier stage. Thus a later family edge
whose head is roofed at a fixed stage was already present at that stage.
The argument also allows the fixed stage to be the final extended stage.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder

open Set Cardinal Order Ladder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- The raw terminal roofs increase at all extended stages. -/
theorem roof_mono_of_geometry {L : G.KappaLadder kappa}
    (hgeometry : CanonicalLadderGeometry L) {a b : ExtendedStage kappa}
    (hab : a ≤ b) :
    G.roof (G.terminalFrontier (L.accumulated a)) ⊆
      G.roof (G.terminalFrontier (L.accumulated b)) := by
  apply G.roof_cut
  rintro x ⟨p, hp, hpx⟩
  obtain ⟨q, hq, hpq⟩ := hgeometry.grows hab p hp
  exact hgeometry.selfRoofing b
    ⟨q, hq, G.support_mono_of_extends hpq (G.terminal_mem_support hpx)⟩

/-- Exact successor arrows contribute no new edge with head in the old
roof. Optional singleton markers have no edges. -/
theorem incoming_edge_reflect_successor
    (L : G.KappaLadder kappa) (harrows : L.HasExactSuccessorArrows)
    (a : Stage kappa) {x y : V}
    (he : (x, y) ∈ G.pathFamilyEdgeSet (L.successorWarp a))
    (hy : y ∈ G.roof (G.terminalFrontier (L.warpAt a))) :
    (x, y) ∈ G.pathFamilyEdgeSet (L.warpAt a) := by
  obtain ⟨q, hq, heq⟩ := he
  rw [(harrows a).2] at hq
  rcases hq with hqArrow | hqMarker
  · obtain ⟨p, hp, hpq⟩ := (harrows a).1.2 q hqArrow
    rcases hpq with ⟨_, rfl⟩ | ⟨z, _, hcontinue | hfixed⟩
    · exact ⟨q, hp, heq⟩
    · obtain ⟨r, _, _, _, _, _, hedge, _⟩ := hcontinue
      change (x, y) ∈ pathEdgeSet q at heq
      rw [hedge] at heq
      rcases heq with heOld | heNew
      · exact ⟨p, hp, heOld⟩
      · exact (L.liftStagePath_edge_head_not_mem_roof a r heNew hy).elim
    · rcases hfixed with ⟨_, rfl⟩
      exact ⟨q, hp, heq⟩
  · cases hm : L.marker a with
    | none => simp [markerPathSet, hm] at hqMarker
    | some y =>
        have hqEq : q = G.trivialPath y := by
          simpa only [markerPathSet, hm, Set.mem_singleton_iff] using hqMarker
        subst q
        exact heq.elim

/-- Reflection through all later successors and actual threadwise limits,
without any marker-exhaustion or bookkeeping premise. -/
theorem incoming_edge_reflect_of_geometry
    {L : G.KappaLadder kappa} (hgeometry : CanonicalLadderGeometry L)
    (harrows : L.HasExactSuccessorArrows)
    {a b : ExtendedStage kappa} (hab : a ≤ b) {x y : V}
    (he : (x, y) ∈ G.pathFamilyEdgeSet (L.accumulated b))
    (hy : y ∈ G.roof (G.terminalFrontier (L.accumulated a))) :
    (x, y) ∈ G.pathFamilyEdgeSet (L.accumulated a) := by
  have hmain : ∀ (o : Ordinal.{u}) (ho : o ≤ kappa.ord), a.1 ≤ o →
      (x, y) ∈ G.pathFamilyEdgeSet (L.accumulated ⟨o, ho⟩) →
        (x, y) ∈ G.pathFamilyEdgeSet (L.accumulated a) := by
    intro o
    induction o using Ordinal.limitRecOn with
    | zero =>
        intro ho ha he
        have heq : (⟨0, ho⟩ : ExtendedStage kappa) = a :=
          Subtype.ext (le_antisymm ha bot_le).symm
        rwa [heq] at he
    | add_one o ih =>
        intro ho ha he
        rcases ha.lt_or_eq with ha | ha
        · have hao : a.1 ≤ o := (Order.lt_add_one_iff).mp ha
          let s : Stage kappa := ⟨o, (Order.add_one_le_iff).mp ho⟩
          apply ih s.2.le hao
          exact L.incoming_edge_reflect_successor harrows s he
            (roof_mono_of_geometry hgeometry (a := a) (b := Stage.toExtended s) hao hy)
        · have heq : (⟨o + 1, ho⟩ : ExtendedStage kappa) = a := Subtype.ext ha.symm
          rwa [heq] at he
    | limit o hoLimit ih =>
        intro ho ha he
        rcases ha.lt_or_eq with ha | ha
        · obtain ⟨C, hstage, hlimit⟩ := hgeometry.limitStages ⟨o, ho⟩ hoLimit
          have heLimit : (x, y) ∈ G.pathFamilyEdgeSet (C.limitPaths G) := by
            rwa [← hlimit]
          rw [C.pathFamilyEdgeSet_limitPaths G] at heLimit
          obtain ⟨c, hec⟩ := Set.mem_iUnion.mp heLimit
          let ai : Set.Iio o := ⟨a.1, ha⟩
          obtain ⟨d, hcd, had⟩ := exists_ge_ge c ai
          have hed : (x, y) ∈ G.pathFamilyEdgeSet (C.stage d) :=
            C.pathFamilyEdgeSet_mono G hcd hec
          rw [hstage d] at hed
          exact ih d.1 d.2 (d.2.le.trans ho) had hed
        · have heq : (⟨o, ho⟩ : ExtendedStage kappa) = a := Subtype.ext ha.symm
          rwa [heq] at he
  exact hmain b.1 b.2 hab he

end Erdos599.DWeb.KappaLadder

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder

universe u

variable {V : Type u}

/-- Every pre-marker terminal is carried by the final reference warp. -/
theorem ladder_arrowEssential_subset_limitVertices
    (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (a : Stage kappa) :
    G.essential (G.terminalFrontier ((ladder G kappa preferred).arrowPart a)) ⊆
      G.vertexSet (ladder G kappa preferred).limitWarp := by
  let L := ladder G kappa preferred
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx.1
  have hpNext : p ∈ L.successorWarp a := hp.1
  obtain ⟨q, hq, hpq⟩ := (ladder_geometry G kappa preferred hNoEnter).grows
    (a := Stage.succExtended a) (b := finalStage kappa) (Stage.succExtended a).2 p hpNext
  exact ⟨q, hq, G.support_mono_of_extends hpq (G.terminal_mem_support hpx)⟩

/-- An edge of the final reference entering the pre-marker roof already
belongs to that pre-marker arrow, and its tail lies in the strict roof. -/
theorem ladder_limitEdge_tail_strictRoof_arrowPart
    (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (a : Stage kappa) {x y : V}
    (he : (x, y) ∈ G.pathFamilyEdgeSet (ladder G kappa preferred).limitWarp)
    (hy : y ∈ G.roof
      (G.terminalFrontier ((ladder G kappa preferred).arrowPart a))) :
    x ∈ G.strictRoof
      (G.terminalFrontier ((ladder G kappa preferred).arrowPart a)) := by
  let L := ladder G kappa preferred
  have hgeometry := ladder_geometry G kappa preferred hNoEnter
  have harrows := ladder_hasExactSuccessorArrows G kappa preferred hNoEnter
  have hyNext : y ∈ G.roof (G.terminalFrontier (L.successorWarp a)) := by
    apply G.roof_mono ?_ hy
    rintro z ⟨p, hp, hpz⟩
    exact ⟨p, hp.1, hpz⟩
  have heNext := incoming_edge_reflect_of_geometry hgeometry harrows
    (a := Stage.succExtended a) (b := finalStage kappa) (Stage.succExtended a).2 he hyNext
  obtain ⟨q, hq, heq⟩ := heNext
  have heArrow : (x, y) ∈ G.pathFamilyEdgeSet (L.arrowPart a) := by
    change q ∈ L.successorWarp a at hq
    rw [(harrows a).2] at hq
    rcases hq with hq | hq
    · exact ⟨q, hq, heq⟩
    · change q ∈ L.markerPathSet a at hq
      cases hm : L.marker a with
      | none => simp [markerPathSet, hm] at hq
      | some z =>
          have hqEq : q = G.trivialPath z := by
            simpa only [markerPathSet, hm, Set.mem_singleton_iff] using hq
          subst q
          exact heq.elim
  have hinv := state_invariant G (extendLadderPreference kappa preferred) hNoEnter a.1
  apply edge_tail_mem_strictRoof_of_selfRoofing (G := G) ?_ ?_ heArrow
  · rw [ladder_arrowPart_eq_arrow G kappa preferred hNoEnter a]
    exact G.isWarp_arrow hinv.warp
      (G.isWarp_liftedLadderRungOfState' (state G (extendLadderPreference kappa preferred) a.1))
  · rw [ladder_arrowPart_eq_arrow G kappa preferred hNoEnter a]
    exact G.canonicalArrow_self_roofing hNoEnter
      (state G (extendLadderPreference kappa preferred) a.1) hinv.warp hinv.selfRoof hinv.sourceRoof

#print axioms incoming_edge_reflect_of_geometry
#print axioms ladder_arrowEssential_subset_limitVertices
#print axioms ladder_limitEdge_tail_strictRoof_arrowPart

end Erdos599.DWeb.UnroofedMarker
