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
import Mathlib

/-!
# The finite pentagon blob-size tables

The Section 7 families `B₁` and `B₂` are most naturally stated up to a
permutation of the five blobs.  We express this by equality of multiplicity
functions.  The two table checks below range over the `5^5` vectors whose
entries lie in `{1,...,5}` and use ordinary kernel reduction (`decide`).
-/

open Finset
open scoped BigOperators

namespace Erdos76

/-- Multiplicity of a natural number among five labelled blob sizes. -/
def fiveSizeMultiplicity (x : Fin 5 → ℕ) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 5)).filter fun i ↦ x i = k).card

/-- The unordered multiset of the five displayed sizes. -/
def fiveSizeMultiset (x : Fin 5 → ℕ) : Multiset ℕ :=
  (Finset.univ : Finset (Fin 5)).val.map x

/-- Equality, up to permutation, with a displayed five-tuple. -/
def SameFiveSizes (x : Fin 5 → ℕ) (a b c d e : ℕ) : Prop :=
  fiveSizeMultiset x = (([a, b, c, d, e] : List ℕ) : Multiset ℕ)

instance instDecidableSameFiveSizes (x : Fin 5 → ℕ) (a b c d e : ℕ) :
    Decidable (SameFiveSizes x a b c d e) := by
  unfold SameFiveSizes
  infer_instance

/-- The sixteen pentagon-blow-up size multisets in the paper's family `B₁`. -/
def PentagonB1Sizes (x : Fin 5 → ℕ) : Prop :=
  SameFiveSizes x 3 3 3 4 4 ∨
  SameFiveSizes x 2 3 4 4 4 ∨
  SameFiveSizes x 3 3 3 3 5 ∨
  SameFiveSizes x 3 3 4 4 4 ∨
  SameFiveSizes x 2 4 4 4 4 ∨
  SameFiveSizes x 3 3 3 4 5 ∨
  SameFiveSizes x 3 4 4 4 4 ∨
  SameFiveSizes x 3 3 4 4 5 ∨
  SameFiveSizes x 4 4 4 4 4 ∨
  SameFiveSizes x 3 4 4 4 5 ∨
  SameFiveSizes x 4 4 4 4 5 ∨
  SameFiveSizes x 3 4 4 5 5 ∨
  SameFiveSizes x 4 4 4 5 5 ∨
  SameFiveSizes x 4 4 5 5 5 ∨
  SameFiveSizes x 4 5 5 5 5 ∨
  SameFiveSizes x 5 5 5 5 5

instance instDecidablePentagonB1Sizes (x : Fin 5 → ℕ) :
    Decidable (PentagonB1Sizes x) := by
  unfold PentagonB1Sizes
  infer_instance

/-- The five one-edge-flip size multisets in the paper's family `B₂`. -/
def PentagonB2Sizes (x : Fin 5 → ℕ) : Prop :=
  SameFiveSizes x 3 3 3 4 4 ∨
  SameFiveSizes x 3 3 4 4 4 ∨
  SameFiveSizes x 3 4 4 4 4 ∨
  SameFiveSizes x 4 4 4 4 4 ∨
  SameFiveSizes x 4 4 4 4 5

instance instDecidablePentagonB2Sizes (x : Fin 5 → ℕ) :
    Decidable (PentagonB2Sizes x) := by
  unfold PentagonB2Sizes
  infer_instance

def fiveSizeSum (x : Fin 5 → ℕ) : ℕ := ∑ i, x i

def fivePairSum (x : Fin 5 → ℕ) : ℕ := ∑ i, (x i).choose 2

/-- Turn a `Fin 5`-valued vector into sizes in `{1,...,5}`. -/
def shiftedFiveSizes (y : Fin 5 → Fin 5) : Fin 5 → ℕ :=
  fun i ↦ (y i : ℕ) + 1

/-- An explicitly displayed five-vector.  Keeping the first two coordinates
fixed lets the kernel check each finite table in 25 independent `5^3`
shards, well below the stock recursion-depth limit. -/
private def fiveVector (a b c d e : Fin 5) : Fin 5 → Fin 5 :=
  ![a, b, c, d, e]

private theorem fiveVector_coordinates (y : Fin 5 → Fin 5) :
    y = fiveVector (y 0) (y 1) (y 2) (y 3) (y 4) := by
  funext i
  fin_cases i <;> rfl

private theorem pentagonB1_finite_table_prefix (a b : Fin 5) :
    ∀ c d e : Fin 5,
      let x := shiftedFiveSizes (fiveVector a b c d e)
      let n := fiveSizeSum x
      17 ≤ n → 12 * fivePairSum x ≤ n * (n - 1) → PentagonB1Sizes x := by
  fin_cases a <;> fin_cases b <;> decide

private theorem pentagonB2_finite_table_prefix (a b : Fin 5) :
    ∀ c d e : Fin 5,
      let x := shiftedFiveSizes (fiveVector a b c d e)
      let n := fiveSizeSum x
      17 ≤ n → 12 * (fivePairSum x + 1) ≤ n * (n - 1) →
        PentagonB2Sizes x := by
  fin_cases a <;> fin_cases b <;> decide

/-- The natural-number inequality forced by
`3 * sum choose(xᵢ,2) ≤ n(n-1)/4` leaves exactly the `B₁` table. -/
theorem pentagonB1_finite_table :
    ∀ y : Fin 5 → Fin 5,
      let x := shiftedFiveSizes y
      let n := fiveSizeSum x
      17 ≤ n → 12 * fivePairSum x ≤ n * (n - 1) → PentagonB1Sizes x := by
  intro y
  rw [fiveVector_coordinates y]
  exact pentagonB1_finite_table_prefix _ _ _ _ _

/-- With the extra unit contributed by a flipped monochromatic triangle,
the same inequality leaves exactly the `B₂` table. -/
theorem pentagonB2_finite_table :
    ∀ y : Fin 5 → Fin 5,
      let x := shiftedFiveSizes y
      let n := fiveSizeSum x
      17 ≤ n → 12 * (fivePairSum x + 1) ≤ n * (n - 1) →
        PentagonB2Sizes x := by
  intro y
  rw [fiveVector_coordinates y]
  exact pentagonB2_finite_table_prefix _ _ _ _ _

/-- Apply the first finite table to an arbitrary natural-valued size vector
once the human argument has established the bounds `1 ≤ xᵢ ≤ 5`. -/
theorem pentagonB1Sizes_of_bounded
    (x : Fin 5 → ℕ) (hpos : ∀ i, 1 ≤ x i) (hle : ∀ i, x i ≤ 5)
    (hn : 17 ≤ fiveSizeSum x)
    (hineq : 12 * fivePairSum x ≤ fiveSizeSum x * (fiveSizeSum x - 1)) :
    PentagonB1Sizes x := by
  let y : Fin 5 → Fin 5 := fun i ↦ ⟨x i - 1, by
    have hi := hle i
    omega⟩
  have hy : shiftedFiveSizes y = x := by
    funext i
    simp only [shiftedFiveSizes, y]
    have hi := hpos i
    omega
  have htable := pentagonB1_finite_table y
  rw [hy] at htable
  exact htable hn hineq

/-- Apply the one-edge-flip table after the same pointwise bounds. -/
theorem pentagonB2Sizes_of_bounded
    (x : Fin 5 → ℕ) (hpos : ∀ i, 1 ≤ x i) (hle : ∀ i, x i ≤ 5)
    (hn : 17 ≤ fiveSizeSum x)
    (hineq : 12 * (fivePairSum x + 1) ≤
      fiveSizeSum x * (fiveSizeSum x - 1)) :
    PentagonB2Sizes x := by
  let y : Fin 5 → Fin 5 := fun i ↦ ⟨x i - 1, by
    have hi := hle i
    omega⟩
  have hy : shiftedFiveSizes y = x := by
    funext i
    simp only [shiftedFiveSizes, y]
    have hi := hpos i
    omega
  have htable := pentagonB2_finite_table y
  rw [hy] at htable
  exact htable hn hineq

end Erdos76
