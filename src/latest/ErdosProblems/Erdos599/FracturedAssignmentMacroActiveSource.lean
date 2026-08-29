/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedAssignmentMacroCompressorProvenance
import ErdosProblems.Erdos599.HalfwayClosedClassifiedContactSegmentation

/-!
# Recovering the active occurrence source from a compressed shortcut

The full fractured assignment reinserts uncovered singleton holes by the
trivial assigned path.  Such a path cannot support a classified contact
shortcut.  Hence every shortcut canonically determines the active source
and, through it, the selected occurrence-level route.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

open Set DirectedPath _root_.Erdos599.Alternating
open Alternating.FracturedDuplication

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

theorem MacroCompressorProducedBracketFracturedAssignment.compiled_assigned_eq_trivial_of_singleton
    {Z : FracturedWarp Gamma}
    (A : MacroCompressorProducedBracketFracturedAssignment Z Y)
    (s : {x // x ∈ Gamma.initialSet Z.paths \ Gamma.initialSet Y})
    (hs : s.1 ∈ singletonVertices Z) :
    A.compiled.traversal.produced.bracket.assignment.assigned s =
      .trivial s.1 := by
  simp [MacroCompressorProducedBracketFracturedAssignment.compiled,
    compressorProducedBracketFracturedAssignmentOfCompiler,
    bracketAssignmentOfActiveLiftedProjections,
    assignmentOfActiveLiftedProjections,
    combineActiveAssignment, hs]

/-- A shortcut in any exact segmentation of the compiled route excludes the
reinserted singleton branch. -/
theorem MacroCompressorProducedBracketFracturedAssignment.not_singleton_of_mem_segmentation_shortcut
    {Z : FracturedWarp Gamma}
    {Yclass : Set Gamma.DPath} {X persistent : Set V}
    (A : MacroCompressorProducedBracketFracturedAssignment Z Y)
    (s : {x // x ∈ Gamma.initialSet Z.paths \ Gamma.initialSet Y})
    (S : ClosedClassifiedContactSegmentation
      (Y := Yclass) (kappa := kappa)
      (A.compiled.traversal.produced.bracket.assignment.assigned s)
      X persistent)
    {x y : V} (hxy : (x, y) ∈ S.shortcutEdges) :
    s.1 ∉ singletonVertices Z := by
  intro hs
  have hxVertex := S.contactSet_subset_vertexSet
    (S.endpoints_mem_contactSet hxy).1
  have hyVertex := S.contactSet_subset_vertexSet
    (S.endpoints_mem_contactSet hxy).2
  rw [A.compiled_assigned_eq_trivial_of_singleton s hs] at hxVertex hyVertex
  have hxs : x = s.1 := by
    simpa [AltPath.vertexSet] using hxVertex
  have hys : y = s.1 := by
    simpa [AltPath.vertexSet] using hyVertex
  have hlt := S.contactRank_lt_of_mem_shortcutEdges hxy
  rw [hxs, hys] at hlt
  exact Nat.lt_irrefl _ hlt

/-- Canonical active source associated with a non-singleton full source. -/
noncomputable def MacroCompressorProducedBracketFracturedAssignment.activeSource
    {Z : FracturedWarp Gamma}
    (A : MacroCompressorProducedBracketFracturedAssignment Z Y)
    (s : {x // x ∈ Gamma.initialSet Z.paths \ Gamma.initialSet Y})
    (hs : s.1 ∉ singletonVertices Z) :
    {x // x ∈ Gamma.initialSet (activePaths Z) \ Gamma.initialSet Y} :=
  toActiveSource Z A.paths_finite s hs

@[simp] theorem MacroCompressorProducedBracketFracturedAssignment.ofActiveSource_activeSource
    {Z : FracturedWarp Gamma}
    (A : MacroCompressorProducedBracketFracturedAssignment Z Y)
    (s : {x // x ∈ Gamma.initialSet Z.paths \ Gamma.initialSet Y})
    (hs : s.1 ∉ singletonVertices Z) :
    ofActiveSource Z (A.activeSource s hs) = s := by
  apply Subtype.ext
  rfl

/-- The compiled path at an active full source is the literal active
projection of the selected occurrence route. -/
theorem MacroCompressorProducedBracketFracturedAssignment.compiled_assigned_eq_activeSourceProjection
    {Z : FracturedWarp Gamma}
    (A : MacroCompressorProducedBracketFracturedAssignment Z Y)
    (s : {x // x ∈ Gamma.initialSet Z.paths \ Gamma.initialSet Y})
    (hs : s.1 ∉ singletonVertices Z) :
    A.compiled.traversal.produced.bracket.assignment.assigned s =
      (A.activeProjection (A.activeSource s hs)).traversal.produced.base.path := by
  let z := A.activeSource s hs
  have hzs : ofActiveSource Z z = s := A.ofActiveSource_activeSource s hs
  calc
    A.compiled.traversal.produced.bracket.assignment.assigned s =
        A.compiled.traversal.produced.bracket.assignment.assigned
          (ofActiveSource Z z) := congrArg
            (fun q => A.compiled.traversal.produced.bracket.assignment.assigned q)
            hzs.symm
    _ = (A.activeProjection z).traversal.produced.base.path :=
      A.compiled_assigned_eq_activeProjection z

end Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

#print axioms Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel.MacroCompressorProducedBracketFracturedAssignment.not_singleton_of_mem_segmentation_shortcut
