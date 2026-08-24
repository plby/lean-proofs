/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

namespace Erdos178

theorem erdos_178 (a : ℕ → ℕ → ℕ)
    (ha : ∀ i, StrictMono (a i)) :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ d : ℕ, ∃ C : ℕ, ∀ m i : ℕ, i < d →
        |∑ j ∈ range m, f (a i j)| ≤ ↑C := by
  sorry

end Erdos178
