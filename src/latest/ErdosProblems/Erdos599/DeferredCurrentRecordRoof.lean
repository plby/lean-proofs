/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredLadderRoofTransport
import ErdosProblems.Erdos599.GroundingDescentBridge

/-!
# Current-stage roof confinement for deferred inessential records

Self-roofing of a deferred accumulated warp upgrades pathwise
inessentiality at the current stage to confinement of the *whole* path in
the current strict roof.  This applies to the prior-record branch of the
grounding split.  A record freshly selected at `a` is only known to be
inessential in the successor warp, so the corresponding unconditional
conclusion remains successor-indexed; no reverse index shift is asserted.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Every point of a path which is already inessential in the accumulated
warp at `a` lies in the strict roof of the frontier at `a`.

The roof half is the deferred accumulated-warp self-roof theorem.  If a
point were on the essential frontier, a terminal path witnessing that
frontier point would be an essential member of the same warp and would meet
the alleged inessential member, contradicting warp disjointness. -/
theorem inessentialPath_support_subset_strictRoof_frontier
    (L : Gamma.KappaLadder kappa) (hlegal : HalfwayGeometry L)
    {a : Stage kappa} {p : Gamma.DPath}
    (hp : p ∈ Gamma.inessentialPaths (L.warpAt a)) :
    p.support ⊆ Gamma.strictRoof (L.frontier a) := by
  intro x hxp
  let T := Gamma.terminalFrontier (L.warpAt a)
  have hxRoofT : x ∈ Gamma.roof T :=
    vertexSet_warpAt_subset_roof_terminalFrontier hlegal a
      ⟨p, hp.1, hxp⟩
  have hxRoof : x ∈ Gamma.roof (L.frontier a) := by
    rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages, Gamma.roof_essential]
    exact hxRoofT
  refine ⟨hxRoof, ?_⟩
  intro hxEssentialFrontier
  have hxFrontier : x ∈ L.frontier a := by
    rw [← hlegal.frontiersEssential a]
    exact hxEssentialFrontier
  have hxEssentialT : x ∈ Gamma.essential T := by
    rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages] at hxFrontier
    exact hxFrontier
  have hxT : x ∈ T := Gamma.essential_subset T hxEssentialT
  obtain ⟨q, hqWarp, hqTerminal⟩ := hxT
  have hqEssential : q ∈ Gamma.essentialWarpPart (L.warpAt a) :=
    ⟨hqWarp, x, hqTerminal, hxEssentialT⟩
  exact (Gamma.not_mem_inessentialPaths_of_intersects_essential
    (hlegal.warpStages (Stage.toExtended a)) hqEssential
      ⟨x, hxp, Gamma.terminal_mem_support hqTerminal⟩) hp

/-- Chosen-record form with the precise extra fact needed for a current
stage conclusion exposed explicitly. -/
theorem chosen_support_subset_strictRoof_frontier_of_currentInessential
    (L : Gamma.KappaLadder kappa) (hlegal : HalfwayGeometry L)
    {a : Stage kappa} {p : Gamma.DPath}
    (_hchosen : L.chosen a = some p)
    (hpCurrent : p ∈ Gamma.inessentialPaths (L.warpAt a)) :
    p.support ⊆ Gamma.strictRoof (L.frontier a) :=
  inessentialPath_support_subset_strictRoof_frontier L hlegal hpCurrent

/-- Every chosen record in the genuine prior-inessential branch has its
entire support in the current-stage strict roof. -/
theorem priorInessentialRecord_support_subset_strictRoof_frontier
    (L : Gamma.KappaLadder kappa) (hlegal : HalfwayGeometry L)
    {a : Stage kappa} (ha : a ∈ L.priorInessentialRecordStages)
    {p : Gamma.DPath} (hchosen : L.chosen a = some p) :
    p.support ⊆ Gamma.strictRoof (L.frontier a) := by
  obtain ⟨q, hqChosen, hqCurrent⟩ := ha
  have hqp : q = p := Option.some.inj (hqChosen.symm.trans hchosen)
  subst q
  exact inessentialPath_support_subset_strictRoof_frontier
    L hlegal hqCurrent

/-- Deferred selection alone gives the corresponding all-support statement
at the successor frontier, and no statement at the old frontier. -/
theorem chosen_support_subset_strictRoof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : HalfwayGeometry L)
    {a : Stage kappa} {p : Gamma.DPath}
    (hchosen : L.chosen a = some p) :
    p.support ⊆ Gamma.strictRoof
      (L.frontier (successorStage L hlegal a)) := by
  have hpSuccessor : p ∈ Gamma.inessentialPaths
      (L.warpAt (successorStage L hlegal a)) := by
    change p ∈ Gamma.inessentialPaths (L.successorWarp a)
    exact (chosen_spec hlegal.validBookkeeping hchosen).1
  exact inessentialPath_support_subset_strictRoof_frontier
    L hlegal hpSuccessor

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.inessentialPath_support_subset_strictRoof_frontier
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.priorInessentialRecord_support_subset_strictRoof_frontier
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.chosen_support_subset_strictRoof_successorFrontier
