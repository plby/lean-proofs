/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedProjectionCompiler
import ErdosProblems.Erdos599.HalfwayCutConstruction

/-!
# Assignment compiler for a literal outside fractured warp

This is the cut-facing wrapper around the source-specific duplicated-vertex
projection compiler.  It deliberately returns the assignment for the literal
hole family `F.holes.paths`; the certified recombination `F.holes.edgeWarp` is
used only to rule out an eventually-forward projected tail.
-/

noncomputable section

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace OutsideFracturedWarp

open Set DirectedPath Alternating
open FracturedAssignmentPeel

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {W Y : Set Gamma.DPath} {X : Set V}

/-- A literal outside fractured warp satisfying the boundary conditions has a
bracket-preserving simultaneous assignment. -/
theorem exists_bracketFracturedAssignment
    (F : OutsideFracturedWarp W X)
    (hboundary : BoundaryAligned F.holes.paths Y)
    (hY : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet F.holes.paths) :
    Nonempty (BracketFracturedAssignment F.holes Y) :=
  FracturedAssignmentPeel.exists_bracketFracturedAssignment F.holes
    hboundary hY F.finiteCharacter F.edgeWarpFiniteCharacter hYfinite hinitial

/-- Ordinary simultaneous-assignment consequence for the literal outside
hole family. -/
theorem exists_simultaneousAssignment
    (F : OutsideFracturedWarp W X)
    (hboundary : BoundaryAligned F.holes.paths Y)
    (hY : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet F.holes.paths) :
    Nonempty (SimultaneousAssignment F.holes.paths Y) := by
  obtain ⟨B⟩ := F.exists_bracketFracturedAssignment hboundary hY hYfinite
    hinitial
  exact ⟨B.assignment⟩

end OutsideFracturedWarp
end LinkageBlueprint
end Blueprint
end Erdos599
