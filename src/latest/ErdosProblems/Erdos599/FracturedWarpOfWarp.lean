/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BoundarySimultaneousAssignment

/-! # Honest warps as fractured warps

This tiny module isolates the definitionally unchanged embedding of a warp
into the fractured-warp interface.  It has no club-stage dependencies.
-/

noncomputable section

namespace Erdos599
namespace Alternating.FracturedWarp

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Every honest warp is canonically a fractured warp with the same members
and the same edge witness. -/
def ofWarp (Z : Set Gamma.DPath) (hZ : Gamma.IsWarp Z) :
    FracturedWarp Gamma where
  paths := Z
  edgeWarp := Z
  edgeWarp_isWarp := hZ
  same_edges := rfl
  allowed_intersection := by
    intro p hp q hq hpq hmeet
    exact (hmeet (hZ hp hq hpq)).elim

@[simp] theorem paths_ofWarp (Z : Set Gamma.DPath) (hZ : Gamma.IsWarp Z) :
    (ofWarp Z hZ).paths = Z :=
  rfl

@[simp] theorem edgeWarp_ofWarp (Z : Set Gamma.DPath)
    (hZ : Gamma.IsWarp Z) :
    (ofWarp Z hZ).edgeWarp = Z :=
  rfl

end Alternating.FracturedWarp
end Erdos599

