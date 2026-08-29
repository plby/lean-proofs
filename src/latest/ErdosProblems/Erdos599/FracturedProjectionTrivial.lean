/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedAssignmentPeel

/-!
# Excluding the trivial lifted-assignment branch

An active fractured member is nontrivial.  Its finite lifted terminal is an
incoming copy, whereas every lifted assignment source is an outgoing copy.
Consequently a maximal assignment chosen for an active source cannot be the
zero-link alternating path.  This removes the degenerate branch before the
finite and infinite connector-deletion compilers are invoked.
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

/-- A selected path for an active lifted source is never trivial.  The proof
uses maximality of the selected assignment, not an extra nondegeneracy
assumption on the compiler. -/
theorem assigned_ne_trivial
    (Z : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y}) (w : Vertex V) :
    B.assigned (toLiftedSource Z hYfinite z) ≠ .trivial w := by
  intro htrivial
  have hstart := B.starts_at (toLiftedSource Z hYfinite z)
  rw [htrivial] at hstart
  change w = (toLiftedSource Z hYfinite z).1 at hstart
  have hterminal :
      (B.assigned (toLiftedSource Z hYfinite z)).terminal? = some w := by
    simp [htrivial, AltPath.terminal?]
  have hwFrontier := B.toSimultaneousAssignment.finite_terminal_mem
    (toLiftedSource Z hYfinite z) hterminal
  have hwIncoming :=
    terminal_eq_incoming_project_of_mem_activeLiftedFrontier Z hwFrontier.1
  have hproject : project w = z.1 := by
    rw [hstart]
    exact project_toLiftedSource Z hYfinite z
  apply outgoing_ne_incoming z.1
  calc
    outgoing z.1 = sourceCopy Z z.1 := rfl
    _ = w := hstart.symm
    _ = incoming (project w) := hwIncoming
    _ = incoming z.1 := congrArg incoming hproject

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599
