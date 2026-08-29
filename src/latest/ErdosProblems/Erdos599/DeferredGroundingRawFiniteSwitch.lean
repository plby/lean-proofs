/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawBoundary
import ErdosProblems.Erdos599.LambdaRawSwitchRealization

/-!
# A balanced, companion-preserving raw finite-source transaction

The actual deferred ladder supplies all boundary incidences. The output is
the explicit raw switched relation with proved degrees and exact endpoint
balance. It is not yet a simultaneous grounding or a separator witness.
-/

noncomputable section

namespace Erdos599
namespace DWeb.KappaLadder.Deferred

open Set _root_.Erdos599.DirectedPath Alternating Alternating.TerminalContactSwitch

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Finite-source switching on the genuine deferred auxiliary: every
unmodified reference edge remains, local degrees are at most one, and the
only balance changes occur at the two original decoded endpoints. -/
theorem popularAuxiliary_rawFiniteSwitch
    (L : Gamma.KappaLadder kappa) (hL : IsDeferredLegal L)
    (p : FinitePath (popularAuxiliaryInput L hL).lambda.graph)
    (hs : p.start ∈ (popularAuxiliaryInput L hL).lambda.source) {s t : V}
    (hstart : p.start = .old s)
    (hexit : (popularAuxiliaryInput L hL).gadgetExit p.finish = some t) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ (popularAuxiliaryInput L hL).rawSwitchedEdges p) ∧
    ∀ x, edgeBalance ((popularAuxiliaryInput L hL).rawSwitchedEdges p) x =
      edgeBalance (popularAuxiliaryInput L hL).familyEdges x +
        propInt (x = s) - propInt (x = t) := by
  have hboundary := popularAuxiliary_hasBoundaryIncidence L hL
  exact ⟨hboundary.rawSwitchedEdges_biUnique_of_start_old p hs hstart,
    hboundary.rawSwitchedEdges_balance_of_start_old p hs hstart hexit⟩

/-- The finite-source transaction has a genuine path/ray realization,
with cycles removed and the exact same signed boundary. -/
theorem popularAuxiliary_exists_rawFiniteSwitchWarp
    (L : Gamma.KappaLadder kappa) (hL : IsDeferredLegal L)
    (p : FinitePath (popularAuxiliaryInput L hL).lambda.graph)
    (hs : p.start ∈ (popularAuxiliaryInput L hL).lambda.source) {s t : V}
    (hstart : p.start = .old s)
    (hexit : (popularAuxiliaryInput L hL).gadgetExit p.finish = some t) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
      familyEdges W = (popularAuxiliaryInput L hL).rawSwitchedEdges p \
        cyclicEdges ((popularAuxiliaryInput L hL).rawSwitchedEdges p) ∧
      isolatedVertices W = ∅ ∧
      ∀ x, edgeBalance (familyEdges W) x =
        edgeBalance (popularAuxiliaryInput L hL).familyEdges x +
          propInt (x = s) - propInt (x = t) :=
  (popularAuxiliary_hasBoundaryIncidence L hL)
    |>.exists_rawSwitchWarp_of_start_old p hs hstart hexit

end DWeb.KappaLadder.Deferred
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.Deferred.popularAuxiliary_rawFiniteSwitch
#print axioms Erdos599.DWeb.KappaLadder.Deferred.popularAuxiliary_exists_rawFiniteSwitchWarp
