/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredRegularGeometry
import ErdosProblems.Erdos599.GroundingSuccessorRoofTransport

/-!
# Roof transport for deferred-legal ladders

The roof arguments below use only the geometric construction laws shared by
the canonical ladder and its deferred-bookkeeping repair.  They are stated
explicitly for `HalfwayGeometry`; no implication between deferred legality
and either legacy or split legality is asserted.
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

/-- A marker inserted at an earlier stage is roofed by every later frontier
of a deferred-legal ladder. -/
theorem marker_mem_roof_frontier_of_lt
    {L : Gamma.KappaLadder kappa} (hlegal : HalfwayGeometry L)
    {a b : Stage kappa} {y : V} (hba : b < a)
    (hy : L.marker b = some y) :
    y ∈ Gamma.roof (L.frontier a) := by
  let c : Stage kappa :=
    ⟨b.1 + 1, by
      exact lt_of_le_of_lt
        ((Order.add_one_le_iff).2 (show b.1 < a.1 from hba)) a.2⟩
  have hc_le : c ≤ a := by
    change b.1 + 1 ≤ a.1
    exact (Order.add_one_le_iff).2 hba
  have hySucc : Gamma.trivialPath y ∈ L.successorWarp b :=
    hlegal.markerInserted b y hy
  have hyWarp : Gamma.trivialPath y ∈ L.warpAt c := by
    change Gamma.trivialPath y ∈
      L.accumulated (Ladder.Stage.toExtended c)
    change Gamma.trivialPath y ∈
      L.accumulated (Ladder.Stage.succExtended b) at hySucc
    simpa [c, Ladder.Stage.toExtended, Ladder.Stage.succExtended] using hySucc
  have hyTerminal : y ∈ Gamma.terminalFrontier (L.warpAt c) :=
    ⟨Gamma.trivialPath y, hyWarp, Gamma.terminal?_trivialPath y⟩
  have hyRoofC : y ∈ Gamma.roof (L.frontier c) := by
    rw [L.frontier_eq_essential_terminalFrontier
        hlegal.roofsSourceAtStages,
      Gamma.roof_essential]
    exact Gamma.subset_roof _ hyTerminal
  rcases hc_le.lt_or_eq with hca | hca
  · exact Gamma.roof_cut (hlegal.frontierChronology hca) hyRoofC
  · rw [← hca]
    exact hyRoofC

/-- Every accumulated family of a deferred-legal ladder is self-roofing. -/
theorem vertexSet_warpAt_subset_roof_terminalFrontier
    {L : Gamma.KappaLadder kappa} (hlegal : HalfwayGeometry L)
    (a : Stage kappa) :
    Gamma.vertexSet (L.warpAt a) ⊆
      Gamma.roof (Gamma.terminalFrontier (L.warpAt a)) := by
  rintro x ⟨p, hp, hxp⟩
  let T := Gamma.terminalFrontier (L.warpAt a)
  have hpInitialRoofFrontier : p.initial ∈ Gamma.roof (L.frontier a) := by
    rcases hlegal.accumulatedInitialProvenance
        (Stage.toExtended a) p hp with hpSource | ⟨b, hba, hbMarker⟩
    · rw [L.frontier_eq_essential_terminalFrontier
          hlegal.roofsSourceAtStages,
        Gamma.roof_essential]
      exact hlegal.roofsSourceAtStages (Stage.toExtended a) hpSource
    · have hba' : b < a := by
        change b.1 + 1 ≤ a.1 at hba
        change b.1 < a.1
        exact (Order.add_one_le_iff).1 hba
      exact marker_mem_roof_frontier_of_lt hlegal hba' hbMarker
  have hpInitialRoof : p.initial ∈ Gamma.roof T := by
    rw [L.frontier_eq_essential_terminalFrontier
        hlegal.roofsSourceAtStages,
      Gamma.roof_essential] at hpInitialRoofFrontier
    exact hpInitialRoofFrontier
  have hpInterTerminal : p.support ∩ T ⊆
      (match Gamma.terminal? p with
      | some t => ({t} : Set V)
      | none => ∅) := by
    exact Gamma.waveRoofSystem.support_inter_terminalSet_subset
      (show Gamma.IsWarp (L.warpAt a) from
        hlegal.warpStages (Stage.toExtended a)) hp
  have hpSupportRoof : p.support ⊆ Gamma.roof T := by
    apply Gamma.pathSupportRoof p T hpInitialRoof
    · intro t ht
      exact ⟨p, hp, ht⟩
    · exact hpInterTerminal
  exact hpSupportRoof hxp

end Deferred
end KappaLadder
end DWeb
end Erdos599
