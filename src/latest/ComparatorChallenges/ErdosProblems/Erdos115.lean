/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos115

noncomputable def extremal_polynomial (n : ℕ) : Polynomial ℂ :=
  (Polynomial.Chebyshev.T ℂ n).comp (Polynomial.C (((2 : ℕ) : ℂ) ^ ((1 : ℂ) / n - 1)) * Polynomial.X + 1)

theorem erdos_115 (n : ℕ) :
    (n ≠ 0 → ∀ p : Polynomial ℂ, p.Monic → p.degree = n →
      IsConnected {z | ‖p.eval z‖ ≤ 1} →
      ∀ z, ‖p.eval z‖ ≤ 1 → ‖p.derivative.eval z‖ ≤ ((2 : ℕ) : ℝ) ^ ((1 : ℝ) / n - 1) * (n : ℝ) ^ 2) ∧
    (n ≠ 0 → ‖(extremal_polynomial n).derivative.eval 0‖ = ((2 : ℕ) : ℝ) ^ ((1 : ℝ) / n - 1) * (n : ℝ) ^ 2) := by
  sorry

end Erdos115
