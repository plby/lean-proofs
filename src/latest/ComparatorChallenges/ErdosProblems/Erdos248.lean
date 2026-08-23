import Mathlib

open scoped ArithmeticFunction.omega

namespace Erdos248

theorem erdos_248 :
    ∃ C > (0 : ℝ),
      {n : ℕ | ∀ k ≥ 1, ω (n + k) ≤ C * k}.Infinite := by
  sorry

end Erdos248
