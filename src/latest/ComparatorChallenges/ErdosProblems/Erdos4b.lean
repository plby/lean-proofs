import Mathlib

namespace Erdos4b

theorem erdos_4 (C : ℝ) (hC : 0 < C) :
    {n : ℕ | (n + 1).nth Nat.Prime - n.nth Nat.Prime >
      C * Real.log (Real.log n) * Real.log (Real.log (Real.log (Real.log n))) /
        (Real.log (Real.log (Real.log n))) ^ 2 * Real.log n}.Infinite := by
  sorry

theorem fgkmt18 :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∃ n : ℕ,
      (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ X ∧
      c * Real.log X * Real.log (Real.log X) *
        Real.log (Real.log (Real.log (Real.log X))) / Real.log (Real.log (Real.log X)) ≤
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  sorry

theorem fgkmt18_index :
    ∃ c : ℝ, 0 < c ∧
      {n : ℕ | (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n >
        c * Real.log (Real.log (n : ℝ)) * Real.log (Real.log (Real.log (Real.log (n : ℝ)))) /
          Real.log (Real.log (Real.log (n : ℝ))) * Real.log (n : ℝ)}.Infinite := by
  sorry

end Erdos4b
