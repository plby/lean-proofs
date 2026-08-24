/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos268

def harmonicSubseriesSet : Set (Fin 3 → ℝ) :=
  { p | ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
    Summable (fun (n : A) => (1 : ℝ) / (n : ℕ)) ∧
    ∀ i : Fin 3, p i = ∑' (n : A), 1 / (((n : ℕ) : ℝ) + ((i : ℕ) : ℝ)) }

theorem erdos_268 :
    (interior harmonicSubseriesSet).Nonempty := by
  sorry

end Erdos268
