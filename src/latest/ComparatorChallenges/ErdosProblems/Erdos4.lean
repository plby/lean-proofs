import Mathlib

namespace Erdos4

theorem erdos_4 (C : ℝ) (hC : 0 < C) :
    {n : ℕ | (n + 1).nth Nat.Prime - n.nth Nat.Prime >
      C * Real.log (Real.log n) * Real.log (Real.log (Real.log (Real.log n))) /
        (Real.log (Real.log (Real.log n))) ^ 2 * Real.log n}.Infinite := by
  sorry

theorem fgkmt18 :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in Filter.atTop,
      ∃ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ X ∧
        c * (Real.log X * Real.log (Real.log X) *
          Real.log (Real.log (Real.log (Real.log X))) /
            Real.log (Real.log (Real.log X))) ≤
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  sorry

theorem fgkmt18_forall_ge :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      ∃ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ X ∧
        c * (Real.log X * Real.log (Real.log X) *
          Real.log (Real.log (Real.log (Real.log X))) /
            Real.log (Real.log (Real.log X))) ≤
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  sorry

end Erdos4
