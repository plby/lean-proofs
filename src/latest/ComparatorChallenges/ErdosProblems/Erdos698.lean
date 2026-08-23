import Mathlib


namespace Erdos698

open scoped Classical in
theorem binomial_gcd_lower_bound (n i j : ℕ) (h2 : 2 ≤ i) (hij : i < j)
    (hjn : j ≤ n / 2) :
    (Nat.gcd (Nat.choose n i) (Nat.choose n j) : ℝ) >
      (2 ^ i * Real.sqrt n) / (4 * i * Real.sqrt (i - 1)) := by
  sorry

end Erdos698
