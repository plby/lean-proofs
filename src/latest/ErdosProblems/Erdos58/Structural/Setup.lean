/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos58.Structural.HamiltonianBranch
import ErdosProblems.Erdos58.Structural.LongestPath

/-!
# Longest-cycle/longest-exterior-path setup for Erdős 58

This file packages the first genuine dichotomy in Gyárfás's proof.  The
Hamiltonian fan count ensures that the longest odd cycle has a nonempty
exterior.  That exterior is either independent, or it has a positive-length
longest path whose endpoints satisfy the maximality lemmas in
`LongestPath`.
-/

namespace Erdos58.Structural

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The independent-exterior versus positive longest-exterior-path split. -/
theorem independentExterior_or_exists_positive_longestExteriorPath
    {j : ℕ} (hj : 0 < j) (C : LongestOddCycle G)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard ≤ j) :
    HasIndependentExterior C ∨
      ∃ P : LongestExteriorPath C, 0 < P.path.length := by
  by_cases hind : HasIndependentExterior C
  · exact Or.inl hind
  · exact Or.inr
      (LongestExteriorPath.exists_positive_of_not_independent (C := C) hind)

/-- Even in the independent branch there is at least one exterior vertex. -/
theorem independentExterior_has_vertex {j : ℕ} (hj : 0 < j)
    (C : LongestOddCycle G)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard ≤ j)
    (_hind : HasIndependentExterior C) :
    C.carrierᶜ.Nonempty :=
  longestOddCycle_exterior_nonempty hj C hdegree hodd

end Erdos58.Structural
