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
import ErdosProblems.Erdos76.PentagonBlobStructure

/-!
# Uniform consequences of the Section 7 blob-size tables

The packing lemmas do not need to know which displayed row occurs.  They only
use the uniform facts recorded here: `B₁` sizes are at least two and any two
differ by at most two; `B₂` sizes are at least three and any two differ by at
most one.
-/

open Finset
open scoped BigOperators

namespace Erdos76

private lemma value_mem_fiveSizeMultiset (x : Fin 5 → ℕ) (i : Fin 5) :
    x i ∈ fiveSizeMultiset x := by
  fin_cases i <;> simp [fiveSizeMultiset]

theorem pentagonB1Sizes_lower_bound
    {x : Fin 5 → ℕ} (hx : PentagonB1Sizes x) (i : Fin 5) :
    2 ≤ x i := by
  rcases hx with h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h <;>
    have hi := value_mem_fiveSizeMultiset x i <;>
    rw [h] at hi <;>
    simp at hi <;>
    omega

theorem pentagonB1Sizes_pair_bound
    {x : Fin 5 → ℕ} (hx : PentagonB1Sizes x) (i j : Fin 5) :
    x i ≤ x j + 2 := by
  rcases hx with h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h <;>
    have hi := value_mem_fiveSizeMultiset x i <;>
    have hj := value_mem_fiveSizeMultiset x j <;>
    rw [h] at hi hj <;>
    simp at hi hj <;>
    omega

theorem pentagonB2Sizes_lower_bound
    {x : Fin 5 → ℕ} (hx : PentagonB2Sizes x) (i : Fin 5) :
    3 ≤ x i := by
  rcases hx with h | h | h | h | h <;>
    have hi := value_mem_fiveSizeMultiset x i <;>
    rw [h] at hi <;>
    simp at hi <;>
    omega

theorem pentagonB2Sizes_pair_bound
    {x : Fin 5 → ℕ} (hx : PentagonB2Sizes x) (i j : Fin 5) :
    x i ≤ x j + 1 := by
  rcases hx with h | h | h | h | h <;>
    have hi := value_mem_fiveSizeMultiset x i <;>
    have hj := value_mem_fiveSizeMultiset x j <;>
    rw [h] at hi hj <;>
    simp at hi hj <;>
    omega

end Erdos76
