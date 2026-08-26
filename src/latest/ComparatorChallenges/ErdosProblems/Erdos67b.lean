import Mathlib

open scoped BigOperators

namespace Erdos67b

/-- Every real sign sequence has arbitrarily large homogeneous-progression sums. -/
theorem erdos_67 (f : ℕ → ℝ) (hf : ∀ n, f n = -1 ∨ f n = 1)
    (C : ℝ) (hC : 0 < C) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧ C < |∑ k ∈ Finset.Icc 1 m, f (k * d)| := by
  sorry

/-- The same discrepancy theorem for sequences valued in the sign subtype. -/
theorem erdos_67_subtype (f : ℕ → {x : ℝ // x = -1 ∨ x = 1})
    (C : ℝ) (hC : 0 < C) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧ C < |∑ k ∈ Finset.Icc 1 m, (f (k * d)).val| := by
  sorry

end Erdos67b
