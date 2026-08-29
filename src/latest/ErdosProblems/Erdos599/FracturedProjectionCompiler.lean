/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedProjectionFiniteProvenance
import ErdosProblems.Erdos599.FracturedProjectionInfiniteSelected

/-!
# Assembly of the fractured-warp projection compiler

The finite and infinite connector-deletion frontends are intentionally kept
separate.  This file contains their common, purely dependent-type assembly:
once each nontrivial selected lifted path can be projected, the trivial case
is impossible and the peeled singleton holes are reinserted by
`bracketAssignmentOfActiveLiftedProjections`.
-/

noncomputable section

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace FracturedAssignmentPeel

open Set DirectedPath Alternating
open Alternating.FracturedDuplication

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

/-- Assemble the two nontrivial constructors for selected lifted paths.  The
zero-link constructor is ruled out by maximality of the lifted assignment. -/
noncomputable def projectionsOfFiniteAndInfiniteBranches
    (Z : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (finiteProjection : ∀
      (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
        Gamma.initialSet Y})
      (Q : FiniteTrace (web Gamma Z).graph),
      B.assigned (toLiftedSource Z hYfinite z) = .finite Q →
        AssignedPathProjection (Y := Y) Z
          (B.assigned (toLiftedSource Z hYfinite z)) z.1)
    (infiniteProjection : ∀
      (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
        Gamma.initialSet Y})
      (R : InfiniteTrace (web Gamma Z).graph),
      B.assigned (toLiftedSource Z hYfinite z) = .infinite R →
        AssignedPathProjection (Y := Y) Z
          (B.assigned (toLiftedSource Z hYfinite z)) z.1) :
    ∀ z : {x // x ∈ Gamma.initialSet (activePaths Z) \
        Gamma.initialSet Y},
      AssignedPathProjection (Y := Y) Z
        (B.assigned (toLiftedSource Z hYfinite z)) z.1 := by
  intro z
  generalize hselected : B.assigned (toLiftedSource Z hYfinite z) = Q
  cases Q with
  | trivial w =>
      exact False.elim
        (assigned_ne_trivial Z hYfinite B z w hselected)
  | finite Q =>
      rw [← hselected]
      exact finiteProjection z Q hselected
  | infinite R =>
      rw [← hselected]
      exact infiniteProjection z R hselected

/-- Common final assembly after the concrete finite and infinite projection
frontends have supplied their per-source constructors. -/
noncomputable def bracketFracturedAssignmentOfBranchCompilers
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (finiteProjection : ∀
      (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
        Gamma.initialSet Y})
      (Q : FiniteTrace (web Gamma Z).graph),
      B.assigned (toLiftedSource Z hYfinite z) = .finite Q →
        AssignedPathProjection (Y := Y) Z
          (B.assigned (toLiftedSource Z hYfinite z)) z.1)
    (infiniteProjection : ∀
      (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
        Gamma.initialSet Y})
      (R : InfiniteTrace (web Gamma Z).graph),
      B.assigned (toLiftedSource Z hYfinite z) = .infinite R →
        AssignedPathProjection (Y := Y) Z
          (B.assigned (toLiftedSource Z hYfinite z)) z.1) :
    BracketFracturedAssignment Z Y :=
  bracketAssignmentOfActiveLiftedProjections Z hboundary hY hZfinite
    hYfinite B
    (projectionsOfFiniteAndInfiniteBranches Z hYfinite B
      finiteProjection infiniteProjection)

/-- The whole family compiler reduced to its finite selected branch.  The
infinite branch is discharged unconditionally by the canonical omega
traversal frontend. -/
theorem exists_bracketFracturedAssignment_of_finiteCompiler
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (finiteProjection : ∀
      (B : BracketSimultaneousAssignment
        (activeLiftedPaths Z)
        (liftedReference Z (activeReference Z Y)))
      (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
        Gamma.initialSet Y})
      (Q : FiniteTrace (web Gamma Z).graph),
      B.assigned (toLiftedSource Z hYfinite z) = .finite Q →
        AssignedPathProjection (Y := Y) Z
          (B.assigned (toLiftedSource Z hYfinite z)) z.1) :
    Nonempty (BracketFracturedAssignment Z Y) := by
  obtain ⟨B⟩ := exists_activeLiftedBracketAssignment Z hboundary hY
    hZfinite hYfinite hinitial
  exact ⟨bracketFracturedAssignmentOfBranchCompilers Z hboundary hY
    hZfinite hYfinite B (finiteProjection B)
    (selectedInfiniteProjection Z hboundary hY hZfinite hZedgeFinite
      hYfinite B)⟩

/-- The source-specific fractured-warp projection compiler.  It deletes the
plain-copy connector steps in the expanded duplicated reference, erases the
resulting projected loops, and compresses maximal equal-direction runs.  The
finite and infinite branches both retain the bracket provenance needed by the
downstream cut construction. -/
theorem exists_bracketFracturedAssignment
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    Nonempty (BracketFracturedAssignment Z Y) :=
  exists_bracketFracturedAssignment_of_finiteCompiler Z hboundary hY
    hZfinite hZedgeFinite hYfinite hinitial
    (selectedFiniteProjection Z hboundary hY hZedgeFinite hYfinite)

/-- Ordinary simultaneous-assignment consequence of the bracket-preserving
fractured-warp compiler. -/
theorem exists_simultaneousAssignment
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    Nonempty (SimultaneousAssignment Z.paths Y) := by
  obtain ⟨B⟩ := exists_bracketFracturedAssignment Z hboundary hY
    hZfinite hZedgeFinite hYfinite hinitial
  exact ⟨B.assignment⟩

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599
