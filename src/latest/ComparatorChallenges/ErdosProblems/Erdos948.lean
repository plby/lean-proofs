/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos948

theorem not_erdos_948 :
    ¬ (∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧
      ∀ colouring : ℤ → Fin k,
        ∃ a : ℕ → ℤ, StrictMono a ∧
          {n | a n < (f n : ℤ)}.Infinite ∧
          ∃ omitted : Fin k, ∀ I : Finset ℕ,
            colouring (∑ i ∈ I, a i) ≠ omitted) := by
  sorry

end Erdos948
