/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

namespace Erdos512

/-- The integral norm of an exponential sum grows at least logarithmically in its size. -/
theorem erdos_512 :
    ∃ K : ℝ, 0 < K ∧ ∀ A : Finset ℤ,
      K * Real.log A.card
        ≤ ∫ θ in (0:ℝ)..1, ‖∑ n ∈ A, Complex.exp (2 * Real.pi * Complex.I * n * θ)‖ := by
  sorry

end Erdos512
