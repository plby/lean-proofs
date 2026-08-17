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
import ErdosProblems.Erdos58.Independent
import Mathlib.Tactic

/-!
# Existence of a longest odd cycle

This file supplies the finite-choice step used at the start of Gyárfás's
structural argument.  If the finite graph has a positive number of distinct
odd cycle lengths, that finite nonempty set has a largest element.  Membership
of the largest length in `oddCycleLengths` supplies an actual copy of the
corresponding cycle graph, hence a value of the concrete structure
`Erdos58.LongestOddCycle` from `Independent.lean`.
-/

open Set
open scoped SimpleGraph

namespace Erdos58.Structural

noncomputable section

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- A finite graph with a positive number of distinct odd cycle lengths has
a designated longest odd cycle.

The returned object contains an actual injective graph homomorphism from the
cycle graph of the selected length, as required by `LongestOddCycle`; it is
not merely a maximum natural number. -/
theorem exists_longestOddCycle [Finite V] {j : ℕ} (hj : 0 < j)
    (hcard : (oddCycleLengths G).ncard = j) :
    Nonempty (LongestOddCycle G) := by
  classical
  have hfinite : (oddCycleLengths G).Finite := oddCycleLengths_finite G
  have hpositive : 0 < (oddCycleLengths G).ncard := by
    omega
  have hnonempty : (oddCycleLengths G).Nonempty :=
    (Set.ncard_pos hfinite).mp hpositive
  let lengths : Finset ℕ := hfinite.toFinset
  have hlengths : lengths.Nonempty := by
    obtain ⟨n, hn⟩ := hnonempty
    exact ⟨n, hfinite.mem_toFinset.mpr hn⟩
  let n : ℕ := lengths.max' hlengths
  have hn : n ∈ oddCycleLengths G := by
    exact hfinite.mem_toFinset.mp (lengths.max'_mem hlengths)
  have hn3 : 3 ≤ n := three_le_of_mem_oddCycleLengths hn
  have hncopy : SimpleGraph.cycleGraph n ⊑ G :=
    ((mem_oddCycleLengths_iff_cycleGraph_isContained (G := G) hn3).mp hn).2
  refine ⟨{
    length := n
    three_le := hn3
    odd := odd_of_mem_oddCycleLengths hn
    copy := hncopy.some
    maximal := ?_ }⟩
  intro m hm
  exact Finset.le_max' lengths m (hfinite.mem_toFinset.mpr hm)

end

end Erdos58.Structural
