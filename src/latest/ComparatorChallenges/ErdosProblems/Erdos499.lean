/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos499

theorem erdos_499 :
    (∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n), ∃ σ : Equiv.Perm (Fin n),
      n ^ (- n : ℤ) ≤ ∏ i, M i (σ i)) := by
  sorry

end Erdos499
