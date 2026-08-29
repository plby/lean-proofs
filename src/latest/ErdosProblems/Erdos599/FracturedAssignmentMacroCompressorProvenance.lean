/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedAssignmentProducedCompressor
import ErdosProblems.Erdos599.HalfwayMacroContactOwnership

/-!
# Retaining the occurrence-level macro assignment through compression

The projected fractured-assignment compiler previously retained its final
compressor input but forgot the selected assignment in the duplicated web.
That loss is harmless for endpoint injection, but not for a contact split:
two distinct occurrence vertices can project to one cut vertex, and the
upstream occurrence is exactly what determines whether the contact is the
incoming or outgoing side of the cut.

This additive producer keeps the concrete macro-owned assignment used by
the source theorem and defines the projected compressor output from that
same object.  It adds no compatibility premise and does not claim that the
projection itself is vertex-disjoint.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

open Set DirectedPath _root_.Erdos599.Alternating
open Alternating.FracturedDuplication

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

/-- The active duplicated problem has the strengthened macro-owned source
assignment under the same finite-character hypotheses as the ordinary
bracket assignment. -/
theorem exists_activeLiftedMacroOwnedBracketAssignment
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    Nonempty (MacroOwnedBracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y))) := by
  apply boundaryMacroOwnedBracketSimultaneousAssignment
    (web Gamma Z)
  · exact boundaryAligned_activeLifted Z hboundary hY hYfinite
  · exact activeLiftedPaths_isWarp Z
  · exact liftedReference_isWarp Z (activeReference_isWarp Z hY)
  · exact activeLiftedPaths_hasFiniteCharacter Z hZfinite
  · exact liftedReference_hasFiniteCharacter Z (activeReference Z Y)
  · rw [initialSet_liftedReference Z
        (activeReference_hasFiniteCharacter Z hYfinite),
      initialSet_activeLiftedPaths]
    exact Set.image_mono
      (activeReference_initials_subset_activePaths Z hboundary hY
        hZfinite hinitial)

/-- Concrete occurrence-level provenance together with its compressor
projection.  The projection is a definition of the stored macro assignment,
not an independently supplied final assignment. -/
structure MacroCompressorProducedBracketFracturedAssignment
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) where
  boundary : BoundaryAligned Z.paths Y
  reference_isWarp : Gamma.IsWarp Y
  paths_finite : Gamma.HasFiniteCharacter Z.paths
  edges_finite : Gamma.HasFiniteCharacter Z.edgeWarp
  reference_finite : Gamma.HasFiniteCharacter Y
  reference_initials : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths
  occurrenceAssignment : MacroOwnedBracketSimultaneousAssignment
    (activeLiftedPaths Z)
    (liftedReference Z (activeReference Z Y))

namespace MacroCompressorProducedBracketFracturedAssignment

/-- The literal per-active-source projection before the family assembly
forgets the selected occurrence path. -/
noncomputable def activeProjection
    {Z : FracturedWarp Gamma}
    (A : MacroCompressorProducedBracketFracturedAssignment Z Y)
    (s : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y}) :
    CompressorProducedAssignedPathProjection (Y := Y) Z
      (A.occurrenceAssignment.assigned
        (toLiftedSource Z A.reference_finite s)) s.1 :=
  compressorProducedProjectionsOfFiniteAndInfiniteBranches Z A.boundary
    A.reference_isWarp A.paths_finite A.edges_finite A.reference_finite
    A.occurrenceAssignment.toBracketSimultaneousAssignment s

/-- The final compressor-produced fractured assignment, compiled from the
same stored occurrence-level assignment. -/
noncomputable def compiled
    {Z : FracturedWarp Gamma}
    (A : MacroCompressorProducedBracketFracturedAssignment Z Y) :
    CompressorProducedBracketFracturedAssignment Z Y :=
  compressorProducedBracketFracturedAssignmentOfCompiler Z A.boundary
    A.reference_isWarp A.paths_finite A.edges_finite A.reference_finite
    A.occurrenceAssignment.toBracketSimultaneousAssignment

/-- On an active source, the family output is definitionally the projected
path attached to that exact source. -/
theorem compiled_assigned_eq_activeProjection
    {Z : FracturedWarp Gamma}
    (A : MacroCompressorProducedBracketFracturedAssignment Z Y)
    (s : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y}) :
    A.compiled.traversal.produced.bracket.assignment.assigned
        (ofActiveSource Z s) =
      (A.activeProjection s).traversal.produced.base.path := by
  have hnot : s.1 ∉ singletonVertices Z := by
    obtain ⟨p, hp, hpinitial⟩ := s.property.1
    exact Set.disjoint_left.1 (activePath_avoids_singletonVertices Z hp)
      (hpinitial ▸ p.initial_mem_support)
  have hnot' : (ofActiveSource Z s).1 ∉ singletonVertices Z := hnot
  have hsource : toActiveSource Z A.paths_finite (ofActiveSource Z s) hnot' =
      s := by
    apply Subtype.ext
    rfl
  simp [compiled, activeProjection,
    compressorProducedBracketFracturedAssignmentOfCompiler,
    bracketAssignmentOfActiveLiftedProjections,
    assignmentOfActiveLiftedProjections,
    combineActiveAssignment, hnot', hsource]
  rfl

end MacroCompressorProducedBracketFracturedAssignment

/-- Unconditional construction from the actual source theorem, preserving
the selected occurrence assignment rather than rebuilding it afterward. -/
theorem exists_macroCompressorProducedBracketFracturedAssignment
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    Nonempty (MacroCompressorProducedBracketFracturedAssignment Z Y) := by
  obtain ⟨M⟩ := exists_activeLiftedMacroOwnedBracketAssignment Z hboundary
    hY hZfinite hYfinite hinitial
  exact ⟨{
    boundary := hboundary
    reference_isWarp := hY
    paths_finite := hZfinite
    edges_finite := hZedgeFinite
    reference_finite := hYfinite
    reference_initials := hinitial
    occurrenceAssignment := M }⟩

end Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

#print axioms Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel.exists_activeLiftedMacroOwnedBracketAssignment
#print axioms Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel.exists_macroCompressorProducedBracketFracturedAssignment
