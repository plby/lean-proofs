/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedAssignmentMacroActiveSource
import ErdosProblems.Erdos599.FracturedProjectionFiniteDirectionOccurrence

/-!
# Finite selected occurrence lift for the macro compiler
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

open Set DirectedPath _root_.Erdos599.Alternating
open Alternating.FracturedDuplication PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

theorem MacroCompressorProducedBracketFracturedAssignment.activeProjection_path_eq_finite
    {Z : FracturedWarp Gamma}
    (A : MacroCompressorProducedBracketFracturedAssignment Z Y)
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : A.occurrenceAssignment.assigned
      (toLiftedSource Z A.reference_finite z) = .finite Q) :
    (A.activeProjection z).traversal.produced.base.path =
      (finiteTraceCompression Z Q).path := by
  unfold MacroCompressorProducedBracketFracturedAssignment.activeProjection
  rw [compressorProducedProjections_eq_selectedFinite Z A.boundary
    A.reference_isWarp A.paths_finite A.edges_finite A.reference_finite
    A.occurrenceAssignment.toBracketSimultaneousAssignment z Q hQ]
  rfl

/-- In the finite selected branch, every forward edge of the active
projection lifts back to a literal edge of the exact macro-owned occurrence
route. -/
theorem MacroCompressorProducedBracketFracturedAssignment.activeProjection_forwardEdge_occurrenceLift_of_finite
    {Z : FracturedWarp Gamma}
    (A : MacroCompressorProducedBracketFracturedAssignment Z Y)
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : A.occurrenceAssignment.assigned
      (toLiftedSource Z A.reference_finite z) = .finite Q)
    {x y : V}
    (hxy : (x, y) ∈
      (A.activeProjection z).traversal.produced.base.path.directionEdges
        .forward) :
    ∃ (l : Link (web Gamma Z).graph),
      l ∈ (A.occurrenceAssignment.assigned
        (toLiftedSource Z A.reference_finite z)).links ∧
      l.direction = .forward ∧
      ∃ e ∈ l.path.edgeSet, project e.1 = x ∧ project e.2 = y := by
  let E := (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute
  have hpath :
      (A.activeProjection z).traversal.produced.base.path =
        (finiteTraceCompression Z Q).path := by
    exact A.activeProjection_path_eq_finite z Q hQ
  by_cases hnil : E.steps = []
  · have htrivial :
        (A.activeProjection z).traversal.produced.base.path =
          .trivial (project Q.initial) := by
      rw [hpath]
      simp [finiteTraceCompression, ErasedSignedRoute.compressionOfValid,
        E, hnil]
    rw [htrivial] at hxy
    simp [AltPath.directionEdges] at hxy
  · have hxy' : (x, y) ∈
        (finiteTraceCompression Z Q).path.directionEdges .forward := by
      rw [← hpath]
      exact hxy
    obtain ⟨l, hl, hldir, e, he, htail, hhead⟩ :=
      finiteTraceCompression_forwardEdge_occurrenceLift Z Q hnil hxy'
    refine ⟨l, ?_, hldir, e, he, htail, hhead⟩
    rw [hQ]
    exact hl

end Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

#print axioms Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel.MacroCompressorProducedBracketFracturedAssignment.activeProjection_forwardEdge_occurrenceLift_of_finite
