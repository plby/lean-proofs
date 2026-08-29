/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating

/-!
# The outside subfamily of a reference warp

This small module contains only the cut-dependent path filter used by the
Section 9 constructions.  Keeping the definition independent of the later
assignment compilers lets literal cut geometry refer to the exact same
family without importing the entire Claim 2 pipeline.
-/

namespace Erdos599
namespace Blueprint

open Set DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath} {X : Set V}

/-- The reference components which stay wholly outside the closed cut. -/
def outsideReference (Y : Set Gamma.DPath) (X : Set V) : Set Gamma.DPath :=
  {p | p ∈ Y ∧ Disjoint p.support X}

@[simp] theorem mem_outsideReference {p : Gamma.DPath} :
    p ∈ outsideReference Y X ↔ p ∈ Y ∧ Disjoint p.support X :=
  Iff.rfl

end Blueprint
end Erdos599
