/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawSwitchRealization
import ErdosProblems.Erdos599.SplitGroundingEqualTargetComponent

/-!
# Raw boundary and finite-source realization for split legality

Both canonical grounding branches use the same lossless incidence argument.
This file supplies its hypotheses directly from split legality, without
converting split bookkeeping to the legacy ordinary legality package.
-/

noncomputable section

namespace Erdos599
namespace DWeb.KappaLadder

open Set _root_.Erdos599.DirectedPath Alternating Alternating.TerminalContactSwitch

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- All finite split records remain terminals in the limiting warp. -/
theorem splitFiniteTerminalSet_subset_limitWarp_terminalFrontier
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal) :
    L.finiteTerminalSet ⊆ Gamma.terminalFrontier L.limitWarp := by
  rintro x ⟨a, _ha, p, hp, hpx⟩
  refine ⟨p, ?_, hpx⟩
  exact (L.recorded_mem_inessential hL.recordedPathsPersist hp
    (b := Ladder.finalStage kappa) (by
      change a.1 + 1 ≤ kappa.ord
      exact (Order.add_one_le_iff).2 a.2)).1

/-- Every target marker is an actual reference initial under split legality. -/
theorem splitTargetMarkers_subset_limitWarp_initialSet
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal) :
    (L.splitPopularAuxiliaryInput hL).targetMarkers ⊆ Gamma.initialSet L.limitWarp := by
  intro y hy
  obtain ⟨p, hp, hyp⟩ := hy.2
  exact ⟨p, hp.1,
    hL.initial_eq_of_splitTargetMarker_mem_limitWarp_support hy hp.1 hyp⟩

/-- The actual split auxiliary supplies every raw boundary incidence. -/
theorem splitPopularAuxiliary_hasBoundaryIncidence
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal) :
    (L.splitPopularAuxiliaryInput hL).HasBoundaryIncidence := by
  constructor
  · intro x hx
    have hterminal : x ∈ Gamma.terminalFrontier L.limitWarp :=
      L.splitFiniteTerminalSet_subset_limitWarp_terminalFrontier hL hx
    have hno := not_hasOutgoing_familyEdges_of_mem_terminalFrontier_anyWarp
      (hL.warpStages (Ladder.finalStage kappa)) hterminal
    simpa only [HasOutgoing, Alternating.familyEdges,
      PopularAuxiliary.Input.familyEdges, splitPopularAuxiliaryInput,
      Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, limitWarp] using hno
  · intro y hy
    have hinitial : y ∈ Gamma.initialSet L.limitWarp :=
      L.splitTargetMarkers_subset_limitWarp_initialSet hL hy
    have hno := not_hasIncoming_familyEdges_of_mem_initialSet_anyWarp
      (hL.warpStages (Ladder.finalStage kappa)) hinitial
    simpa only [HasIncoming, Alternating.familyEdges,
      PopularAuxiliary.Input.familyEdges, splitPopularAuxiliaryInput,
      Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, limitWarp] using hno

/-- The same concrete balanced path/ray realization is available on the
actual split auxiliary; no compatibility or switching provider is assumed. -/
theorem splitPopularAuxiliary_exists_rawFiniteSwitchWarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (p : FinitePath (L.splitPopularAuxiliaryInput hL).lambda.graph)
    (hs : p.start ∈ (L.splitPopularAuxiliaryInput hL).lambda.source) {s t : V}
    (hstart : p.start = .old s)
    (hexit : (L.splitPopularAuxiliaryInput hL).gadgetExit p.finish = some t) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
      familyEdges W = (L.splitPopularAuxiliaryInput hL).rawSwitchedEdges p \
        cyclicEdges ((L.splitPopularAuxiliaryInput hL).rawSwitchedEdges p) ∧
      isolatedVertices W = ∅ ∧
      ∀ x, edgeBalance (familyEdges W) x =
        edgeBalance (L.splitPopularAuxiliaryInput hL).familyEdges x +
          propInt (x = s) - propInt (x = t) :=
  (L.splitPopularAuxiliary_hasBoundaryIncidence hL)
    |>.exists_rawSwitchWarp_of_start_old p hs hstart hexit

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.splitPopularAuxiliary_hasBoundaryIncidence
#print axioms Erdos599.DWeb.KappaLadder.splitPopularAuxiliary_exists_rawFiniteSwitchWarp
