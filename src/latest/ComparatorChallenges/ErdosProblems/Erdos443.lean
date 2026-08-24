/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos443

def A (k : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 k).image (fun r => r * (k - r))

theorem erdos_443 (s : ℕ) :
  ∃ m n : ℕ, n < m ∧ s ≤ ((A n ∩ A m).card : ℝ) := by
  sorry

theorem erdos_443_part_two (ε : ℝ) (hε : 0 < ε) :
  ∃ n₀ : ℕ, ∀ m n : ℕ, n₀ < n → n < m →
  ((A n ∩ A m).card : ℝ) < ((m : ℝ) * n) ^ (ε) := by
  sorry

end Erdos443
