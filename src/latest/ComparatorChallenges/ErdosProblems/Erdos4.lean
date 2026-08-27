import Mathlib

namespace Erdos4

theorem erdos_4 (C : ℝ) (hC : 0 < C) :
    {n : ℕ | (n + 1).nth Nat.Prime - n.nth Nat.Prime >
      C * Real.log (Real.log n) * Real.log (Real.log (Real.log (Real.log n))) /
        (Real.log (Real.log (Real.log n))) ^ 2 * Real.log n}.Infinite := by
  sorry

theorem fgkmt18 :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      ∃ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ X ∧
        C * (Real.log X * Real.log (Real.log X) *
          Real.log (Real.log (Real.log (Real.log X))) /
            Real.log (Real.log (Real.log X))) ≤
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  sorry

theorem Tilted.all_endpoint_consecutive_prime_gaps :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∃ n : ℕ,
      (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ X ∧
      C * Real.log X * Real.log (Real.log X) /
        Real.log (Real.log (Real.log (Real.log X))) ≤
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  sorry

end Erdos4
