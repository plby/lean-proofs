/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerArrows
import ErdosProblems.Erdos599.DeferredPreMarkerRecordRoof

/-!
# An unroofed marker creates no inessential old component

An essential pre-marker terminal is essential in the rung's quotient web.
Roof maximality preserves it after adjoining the marker there; lifting a
private escape back to the ambient graph preserves it in the actual
successor. Consequently all successor-inessential members already belong
to the pre-marker inessential family, and their entire supports are in its
strict roof. This is a pre-marker statement, not an old-stage index shift.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder

universe u

variable {V : Type u}

/-- The exact essential-frontier calculation for the actual pre-marker
arrow. Both cross-roof hypotheses follow from the recursive invariants. -/
theorem ladder_essential_arrowPart_eq_union (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (a : Stage kappa) :
    G.essential (G.terminalFrontier ((ladder G kappa preferred).arrowPart a)) =
      G.essential (G.terminalFrontier ((ladder G kappa preferred).warpAt a) ∪
        ((ladder G kappa preferred).stageWeb a).terminalFrontier
          ((ladder G kappa preferred).rung a)) := by
  let L := ladder G kappa preferred
  let s := state G (extendLadderPreference kappa preferred) a.1
  have hinv := state_invariant G (extendLadderPreference kappa preferred) hNoEnter a.1
  have hLiftInitial : G.initialSet (L.liftedRung a) ⊆
      G.essential (G.terminalFrontier (L.warpAt a)) :=
    G.initialSet_liftedLadderRungOfState_subset_essential s hinv.sourceRoof
  have hEssRoof : G.essential (G.terminalFrontier (L.warpAt a)) ⊆
      G.roof (G.terminalFrontier (L.liftedRung a)) :=
    G.essential_subset_roof_terminalFrontier_liftedLadderRungOfState hNoEnter s
  have hOldRoof : G.roof (G.terminalFrontier (L.warpAt a)) ⊆
      G.roof (G.terminalFrontier (L.liftedRung a)) := by
    rw [← G.roof_essential (G.terminalFrontier (L.warpAt a))]
    exact G.roof_cut hEssRoof
  have hOldCross : G.initialSet (L.warpAt a ∪ L.liftedRung a) ⊆
      G.roof (G.terminalFrontier (L.warpAt a)) := by
    rw [G.initialSet_union]
    rintro z (hzOld | hzLift)
    · exact hinv.selfRoof (G.initialSet_subset_vertexSet' _ hzOld)
    · exact G.essential_subset_roof _ (hLiftInitial hzLift)
  have hLiftCross : G.initialSet (L.warpAt a ∪ L.liftedRung a) ⊆
      G.roof (G.terminalFrontier (L.liftedRung a)) :=
    hOldCross.trans hOldRoof
  rw [ladder_arrowPart_eq_arrow G kappa preferred hNoEnter a]
  have heq := G.essential_terminalFrontier_arrow_eq_union_of_crossRoof
    (U := L.warpAt a) (W := L.liftedRung a)
    hinv.warp (G.isWarp_liftedLadderRungOfState' s) hOldCross hLiftCross
  simpa only [terminalFrontier_liftedRung] using heq

/-- Every essential pre-marker terminal stays essential after the
unroofed singleton is inserted. -/
theorem ladder_oldEssential_mem_successorEssential
    (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} {x y : V}
    (hmarker : (ladder G kappa preferred).marker a = some y)
    (hx : x ∈ G.essential
      (G.terminalFrontier ((ladder G kappa preferred).arrowPart a))) :
    x ∈ G.essential
      (G.terminalFrontier ((ladder G kappa preferred).successorWarp a)) := by
  let L := ladder G kappa preferred
  let A := G.terminalFrontier (L.warpAt a)
  let T := (L.stageWeb a).terminalFrontier (L.rung a)
  change L.marker a = some y at hmarker
  have hess : G.essential (G.terminalFrontier (L.arrowPart a)) =
      G.essential (A ∪ T) := ladder_essential_arrowPart_eq_union G kappa preferred hNoEnter a
  have hroof : G.roof (G.terminalFrontier (L.arrowPart a)) = G.roof (A ∪ T) := by
    rw [← G.roof_essential (G.terminalFrontier (L.arrowPart a)), hess,
      G.roof_essential]
  have hyNotRoof : y ∉ G.roof (G.terminalFrontier (L.arrowPart a)) :=
    ladder_marker_not_mem_roof_arrowPart G kappa preferred hNoEnter hmarker
  have hyOld : y ∉ G.roof A := by
    intro hy
    apply hyNotRoof
    rw [hroof]
    exact G.roof_mono Set.subset_union_left hy
  have hyReach : y ∈ (L.stageWeb a).reachableToTarget :=
    (L.mem_stageVertexSet_of_not_mem_accumulatedRoof a hyOld).1
  have hyOutside : y ∉ (L.stageWeb a).vertexSet (L.rung a) := by
    intro hy
    have hyLift : y ∈ G.vertexSet (L.liftedRung a) := by
      rwa [L.vertexSet_liftedRung a]
    have hyRoofLift := G.liftedLadderRungOfState_self_roofing hNoEnter
      (state G (extendLadderPreference kappa preferred) a.1) hyLift
    change y ∈ G.roof (G.terminalFrontier (L.liftedRung a)) at hyRoofLift
    rw [terminalFrontier_liftedRung] at hyRoofLift
    apply hyNotRoof
    rw [hroof]
    exact G.roof_mono Set.subset_union_right hyRoofLift
  have hxUnion : x ∈ G.essential (A ∪ T) := hess ▸ hx
  have hxStage : x ∈ (L.stageWeb a).essential T :=
    L.stageEssential_of_ambientEssential_old_union_rung_of_wave hNoEnter a
      (ladder_hasWaveRungs G kappa preferred a) hxUnion
  obtain ⟨r, hr, hrx⟩ := hxStage.1
  have hxStageMarker : x ∈ (L.stageWeb a).essential (T ∪ {y}) :=
    essential_terminal_insert_of_roofMaximal_wave (L.stageWeb a)
      (ladder_hasWaveRungs G kappa preferred a)
      (ladder_hasRoofMaximalRungs G kappa preferred a) hr hrx
      ⟨hr, x, hrx, hxStage⟩ hyReach hyOutside
  have hxAmbient : x ∈ G.essential (A ∪ (T ∪ {y})) :=
    ambientEssential_union_of_stageEssential G A (T ∪ {y}) hxStageMarker
  have hsucc : L.successorWarp a = L.arrowPart a ∪ L.markerPathSet a :=
    (ladder_hasExactSuccessorArrows G kappa preferred hNoEnter a).2
  have hxSuccessor : x ∈ G.terminalFrontier (L.successorWarp a) := by
    obtain ⟨p, hp, hpx⟩ := hx.1
    exact ⟨p, hsucc ▸ Or.inl hp, hpx⟩
  apply essential_of_mem_of_subset G (S := G.terminalFrontier (L.successorWarp a))
    (R := A ∪ (T ∪ {y})) ?_ hxSuccessor hxAmbient
  rintro z ⟨p, hp, hpz⟩
  rw [hsucc] at hp
  rcases hp with hpArrow | hpMarker
  · have hpArrow' : p ∈ G.arrow (L.warpAt a) (L.liftedRung a) := by
      rwa [← ladder_arrowPart_eq_arrow G kappa preferred hNoEnter a]
    rcases G.terminalFrontier_arrow_subset_union (L.warpAt a) (L.liftedRung a)
        ⟨p, hpArrow', hpz⟩ with hzA | hzT
    · exact Or.inl hzA
    · exact Or.inr (Or.inl (by rwa [terminalFrontier_liftedRung] at hzT))
  · have hpTrivial : p = G.trivialPath y := by
      change p ∈ L.markerPathSet a at hpMarker
      simpa only [markerPathSet, hmarker, Set.mem_singleton_iff] using hpMarker
    subst p
    have hyz : y = z := Option.some.inj ((G.terminal?_trivialPath y).symm.trans hpz)
    exact Or.inr (Or.inr hyz.symm)

/-- Inessentiality of a successor component is never created by its new
marker. This applies to every component, not just the selected record. -/
theorem ladder_inessential_successor_subset_arrowPart
    (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    (a : Stage kappa) :
    G.inessentialPaths ((ladder G kappa preferred).successorWarp a) ⊆
      G.inessentialPaths ((ladder G kappa preferred).arrowPart a) := by
  let L := ladder G kappa preferred
  intro p hp
  have hsucc : L.successorWarp a = L.arrowPart a ∪ L.markerPathSet a :=
    (ladder_hasExactSuccessorArrows G kappa preferred hNoEnter a).2
  have hpArrow : p ∈ L.arrowPart a := by
    have hpMem := hp.1
    rw [hsucc] at hpMem
    rcases hpMem with hpArrow | hpMarker
    · exact hpArrow
    · cases hm : L.marker a with
      | none => simp [markerPathSet, hm] at hpMarker
      | some y =>
          have hpEq : p = G.trivialPath y := by
            simpa only [markerPathSet, hm, Set.mem_singleton_iff] using hpMarker
          exact (hp.2 ⟨hp.1, y, hpEq ▸ G.terminal?_trivialPath y,
            ladder_marker_essential_successor G kappa preferred hm⟩).elim
  refine ⟨hpArrow, ?_⟩
  intro hpEss
  cases hm : L.marker a with
  | none =>
      have heq : L.successorWarp a = L.arrowPart a := by
        simpa only [markerPathSet, hm, Set.union_empty] using hsucc
      exact hp.2 (heq ▸ hpEss)
  | some y =>
      obtain ⟨_, z, hpz, hz⟩ := hpEss
      exact hp.2 ⟨hp.1, z, hpz,
        ladder_oldEssential_mem_successorEssential G kappa preferred hNoEnter hm hz⟩

theorem ladder_chosen_support_subset_strictRoof_arrowPart
    (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} {p : G.DPath}
    (hchosen : (ladder G kappa preferred).chosen a = some p) :
    p.support ⊆ G.strictRoof
      (G.terminalFrontier ((ladder G kappa preferred).arrowPart a)) := by
  let L := ladder G kappa preferred
  have hp := (L.bookkeeping.chosen_mem_available
    (ladder_validBookkeeping G kappa preferred) hchosen).1
  have hpArrow := ladder_inessential_successor_subset_arrowPart G kappa preferred hNoEnter a hp
  have hinv := state_invariant G (extendLadderPreference kappa preferred) hNoEnter a.1
  apply inessentialPath_support_subset_strictRoof_of_selfRoofing (G := G) ?_ ?_ hpArrow
  · rw [ladder_arrowPart_eq_arrow G kappa preferred hNoEnter a]
    exact G.isWarp_arrow hinv.warp
      (G.isWarp_liftedLadderRungOfState' (state G (extendLadderPreference kappa preferred) a.1))
  · rw [ladder_arrowPart_eq_arrow G kappa preferred hNoEnter a]
    exact G.canonicalArrow_self_roofing hNoEnter
      (state G (extendLadderPreference kappa preferred) a.1) hinv.warp hinv.selfRoof hinv.sourceRoof

#print axioms ladder_oldEssential_mem_successorEssential
#print axioms ladder_inessential_successor_subset_arrowPart
#print axioms ladder_chosen_support_subset_strictRoof_arrowPart

end Erdos599.DWeb.UnroofedMarker
