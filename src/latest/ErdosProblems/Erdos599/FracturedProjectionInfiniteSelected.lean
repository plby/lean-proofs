/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedInfiniteTraversalBlocks
import ErdosProblems.Erdos599.FracturedProjectionSelectedEndpoints

/-!
# Selected infinite branch of fractured projection

This file converts the generic infinite traversal compiler into the exact
per-source output consumed by `FracturedAssignmentPeel`.  Construction of the
concrete traversal blocks is kept in its own frontend module.
-/

noncomputable section

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace FracturedAssignmentPeel

open Set DirectedPath Alternating
open Alternating.FracturedDuplication

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

namespace InfiniteTraversalBlocks

variable {Z : FracturedWarp Gamma}
variable {R : InfiniteTrace (web Gamma Z).graph} {M : Type v}

/-- An infinite compiled projection has all clauses required of one selected
downstairs assigned path. -/
noncomputable def assignedPathProjection
    (T : InfiniteTraversalBlocks (Y := Y) Z (.infinite R) M)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    {source : V}
    (hinitial : project R.initial = source)
    (hinitialOutside : project R.initial ∉ Gamma.vertexSet Y) :
    AssignedPathProjection (Y := Y) Z (.infinite R) source := by
  let C := T.compile hY hZfinite
  have hfullBracket : IsBracketSafe Z.edgeWarp Y C.path :=
    IsBracketSafe.of_reference_subwarp C.bracket_safe hY
      (activeReference_subset Z Y)
      (fun _ ↦ by
        rw [C.initial_eq]
        exact hinitialOutside)
      (fun t ht _ ↦ by
        have hnone := C.path.isInfinite_iff_terminal?_eq_none.mp C.infinite
        rw [hnone] at ht
        simp at ht)
  refine {
    path := C.path
    starts_at := C.initial_eq.trans hinitial
    bracket_safe := hfullBracket
    safe := hfullBracket.isSafe
    leaving := Or.inl C.infinite
    maximal := Or.inl C.infinite
    terminal_lift := ?_ }
  intro v hv
  have hnone := C.path.isInfinite_iff_terminal?_eq_none.mp C.infinite
  rw [hnone] at hv
  simp at hv

end InfiniteTraversalBlocks

/-- Application of the infinite branch compiler to a path selected by the
peeled bracket assignment.  The traversal frontend supplies `T`; all endpoint,
maximality, and full-reference promotion facts are automatic. -/
noncomputable def selectedInfiniteProjectionOfBlocks
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (R : InfiniteTrace (web Gamma Z).graph)
    (hR : B.assigned (toLiftedSource Z hYfinite z) = .infinite R)
    {M : Type v}
    (T : InfiniteTraversalBlocks (Y := Y) Z (.infinite R) M) :
    AssignedPathProjection (Y := Y) Z
      (B.assigned (toLiftedSource Z hYfinite z)) z.1 := by
  rw [hR]
  apply T.assignedPathProjection hY hZfinite
  · have h := selected_project_initial Z hYfinite B z
    rw [hR] at h
    exact h
  · have h := selected_project_initial_outside Z hboundary hYfinite B z
    rw [hR] at h
    exact h

/-- The unconditional selected infinite branch, using the canonical
connector-deleted omega traversal and its owner provenance. -/
noncomputable def selectedInfiniteProjection
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (R : InfiniteTrace (web Gamma Z).graph)
    (hR : B.assigned (toLiftedSource Z hYfinite z) = .infinite R) :
    AssignedPathProjection (Y := Y) Z
      (B.assigned (toLiftedSource Z hYfinite z)) z.1 := by
  have hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R) := by
    have h := B.bracket_safe (toLiftedSource Z hYfinite z)
    rw [hR] at h
    exact h
  have hinitial : project (AltPath.infinite R).initial ∉
      Gamma.vertexSet Y := by
    have h := selected_project_initial_outside Z hboundary hYfinite B z
    rw [hR] at h
    exact h
  let T := InfiniteTraversalFrontend.infiniteTraversalBlocks Z R hbracket
    hZfinite hZedgeFinite hYfinite hinitial
  exact selectedInfiniteProjectionOfBlocks Z hboundary hY hZedgeFinite
    hYfinite B z R hR T

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599
