/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos124b

theorem erdos_124 : ∀ k, ∀ d : Fin k → ℕ,
    (∀ i, 2 ≤ d i) → 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1) →
    ∀ n, ∃ a : Fin k → ℕ,
    ∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1} ∧
    n = ∑ i, a i := by
  sorry

theorem formal_conjectures_erdos_124_corrected :
    (∀ k, ∀ d : Fin k → ℕ,
        (∀ i, 3 ≤ d i) →  StrictMono d → 1 ≤ ∑ i : Fin k, (1 : ℚ) / (d i - 1) →
        ∀ᶠ n in atTop, ∃ c : Fin k → ℕ, ∃ a : Fin k → ℕ,
        ∀ i, c i ∈ ({0, 1} : Finset ℕ) ∧
        ∀ i, ((d i).digits (a i)).toFinset ⊆ {0, 1} ∧
        n = ∑ i, c i * a i) := by
  sorry

end Erdos124b
