import Mathlib

namespace Erdos424

open Set

def nextGeneration (A : Set ℕ) : Set ℕ :=
  {z : ℕ | ∃ x y, x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ z = x * y - 1}

def sequenceSet (n : ℕ) : Set ℕ :=
  Nat.rec {2, 3} (fun _ previous => previous ∪ nextGeneration previous) n

def generatedSet : Set ℕ := ⋃ n : ℕ, sequenceSet n

open Classical in
theorem erdos_424_lower_density :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) ≤
        (((Finset.Icc 1 x).filter fun n ↦ n ∈ generatedSet).card : ℝ) := by
  sorry

end Erdos424
