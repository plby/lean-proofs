/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos622.Core

/-!
# Canonical finite vertex types for Erdős Problem 622

`Core` proves that an isomorphism transports the induced Hamiltonian-cycle
witness for a cyclic set and consequently preserves the number of cyclic
sets.  This file records the remaining regularity invariance and packages
both invariants for Mathlib's canonical finite vertex type `Fin n`.
-/

namespace Erdos622

attribute [local instance] Classical.propDecidable

variable {V W : Type*} [Fintype V] [Fintype W]
variable [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

omit [DecidableEq V] [DecidableEq W] in
/-- Regular degree is invariant under a graph isomorphism. -/
theorem isRegularOfDegree_iff_of_iso (e : G ≃g H) (d : ℕ) :
    G.IsRegularOfDegree d ↔ H.IsRegularOfDegree d := by
  constructor
  · intro h w
    simpa using (e.degree_eq (e.symm w)).trans (h (e.symm w))
  · intro h v
    simpa using (e.degree_eq v).symm.trans (h (e v))

/-- Passing to Mathlib's canonical finite vertex type preserves the number of
cyclic subsets. -/
theorem card_cycleSpannedSubsets_overFin (hc : Fintype.card V = n) :
    (cycleSpannedSubsets G).card = (cycleSpannedSubsets (G.overFin hc)).card :=
  card_cycleSpannedSubsets_congr (G.overFinIso hc)

omit [DecidableEq V] in
/-- Passing to Mathlib's canonical finite vertex type preserves regularity. -/
theorem isRegularOfDegree_overFin_iff (hc : Fintype.card V = n) (d : ℕ) :
    G.IsRegularOfDegree d ↔ (G.overFin hc).IsRegularOfDegree d :=
  isRegularOfDegree_iff_of_iso (G.overFinIso hc) d

end Erdos622
