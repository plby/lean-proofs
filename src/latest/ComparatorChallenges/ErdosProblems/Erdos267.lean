import Mathlib

namespace Erdos267

/-- Every positive increasing index sequence with a uniform ratio gap
greater than one has an irrational reciprocal Fibonacci sum. -/
theorem erdos_267 (n : ℕ → ℕ)
    (hpos : ∀ k : ℕ, 0 < n k) (hmono : StrictMono n)
    (hgap : ∃ c : ℝ, 1 < c ∧
      ∀ k : ℕ, c ≤ (n (k + 1) : ℝ) / (n k : ℝ)) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  sorry

end Erdos267
