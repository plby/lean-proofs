/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedAssignmentMacroActiveSource
import ErdosProblems.Erdos599.FracturedProjectionInfiniteOccurrenceLift

/-!
# Infinite selected occurrence lift for the macro compiler

The selected infinite computation law exposes the literal loop-erased
compressor input of the active projection.  Each forward edge of that
projection can therefore be traced to a concrete forward edge in the exact
occurrence-level assignment.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

open Set DirectedPath _root_.Erdos599.Alternating
open Alternating.FracturedDuplication

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

theorem MacroCompressorProducedBracketFracturedAssignment.activeProjection_path_eq_infinite
    {Z : FracturedWarp Gamma}
    (A : MacroCompressorProducedBracketFracturedAssignment Z Y)
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (R : InfiniteTrace (web Gamma Z).graph)
    (hR : A.occurrenceAssignment.assigned
      (toLiftedSource Z A.reference_finite z) = .infinite R) :
    let hbracket : IsBracketSafe (activeLiftedPaths Z)
        (liftedReference Z (activeReference Z Y)) (.infinite R) := by
      have h := A.occurrenceAssignment.bracket_safe
        (toLiftedSource Z A.reference_finite z)
      rw [hR] at h
      exact h
    let P := InfiniteTraversalFrontend.edgeProvenance Z R hbracket A.paths_finite
    let hfinite := InfiniteTraversalFrontend.omegaBlocks_vertex_finite
      Z R hbracket
    let S := P.loopErasedInput hfinite
    let hchange := P.loopErasedInput_changes Z.edgeWarp_isWarp
      (activeReference_isWarp Z A.reference_isWarp) hfinite
      (InfiniteTraversalFrontend.edgeProvenance_carrier_finite Z R hbracket
        A.paths_finite A.edges_finite A.reference_finite)
    (A.activeProjection z).traversal.produced.base.path =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace := by
  dsimp only
  unfold MacroCompressorProducedBracketFracturedAssignment.activeProjection
  rw [compressorProducedProjections_eq_selectedInfinite Z A.boundary
    A.reference_isWarp A.paths_finite A.edges_finite A.reference_finite
    A.occurrenceAssignment.toBracketSimultaneousAssignment z R hR]
  let hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R) := by
    have h := A.occurrenceAssignment.bracket_safe
      (toLiftedSource Z A.reference_finite z)
    rw [hR] at h
    exact h
  let hinitial : project (AltPath.infinite R).initial ∉
      Gamma.vertexSet Y := by
    have h := selected_project_initial_outside Z A.boundary A.reference_finite
      A.occurrenceAssignment.toBracketSimultaneousAssignment z
    rw [hR] at h
    exact h
  let T := InfiniteTraversalFrontend.infiniteTraversalBlocks Z R hbracket
    A.paths_finite A.edges_finite A.reference_finite hinitial
  calc
    _ = (T.compile A.reference_isWarp A.edges_finite).path := by
      simp only [selectedInfiniteProjection_compressorProduced,
        InfiniteTraversalBlocks.assignedPathProjection]
      rfl
    _ = _ := T.compile_path_eq_loopErasedInput
      A.reference_isWarp A.edges_finite

/-- In the infinite selected branch, every forward edge of the active
projection lifts back to a literal edge of the exact occurrence-level
assignment route. -/
theorem MacroCompressorProducedBracketFracturedAssignment.activeProjection_forwardEdge_occurrenceLift_of_infinite
    {Z : FracturedWarp Gamma}
    (A : MacroCompressorProducedBracketFracturedAssignment Z Y)
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (R : InfiniteTrace (web Gamma Z).graph)
    (hR : A.occurrenceAssignment.assigned
      (toLiftedSource Z A.reference_finite z) = .infinite R)
    {x y : V}
    (hxy : (x, y) ∈
      (A.activeProjection z).traversal.produced.base.path.directionEdges
        .forward) :
    ∃ (l : Link (web Gamma Z).graph),
      l ∈ (A.occurrenceAssignment.assigned
        (toLiftedSource Z A.reference_finite z)).links ∧
      l.direction = .forward ∧
      ∃ e ∈ l.path.edgeSet, project e.1 = x ∧ project e.2 = y := by
  let hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R) := by
    have h := A.occurrenceAssignment.bracket_safe
      (toLiftedSource Z A.reference_finite z)
    rw [hR] at h
    exact h
  have hpath := A.activeProjection_path_eq_infinite z R hR
  rw [hpath] at hxy
  obtain ⟨l, hl, hldir, e, he, he1, he2⟩ :=
    InfiniteTraversalFrontend.infiniteRunWalk_forwardEdge_occurrenceLift
      Z R hbracket A.reference_isWarp A.paths_finite A.edges_finite
        A.reference_finite hxy
  refine ⟨l, ?_, hldir, e, he, he1, he2⟩
  rw [hR]
  exact hl

#print axioms MacroCompressorProducedBracketFracturedAssignment.activeProjection_path_eq_infinite
#print axioms MacroCompressorProducedBracketFracturedAssignment.activeProjection_forwardEdge_occurrenceLift_of_infinite

end Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel
