import Mathlib

namespace Erdos906

/-- A transcendental entire function with dense derivative zeros along every subsequence. -/
theorem erdos_906 :
    ∃ f : ℂ → ℂ, f ≠ 0 ∧ Differentiable ℂ f ∧
      (¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, p.eval z = f z) ∧
      ∀ s : ℕ → ℕ, StrictMono s →
        Dense {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0} := by
  sorry

/-- One witness obeys a growth bound and has zeros of all sufficiently high derivatives
in each nonempty open set. -/
theorem erdos_906_cofinite :
    ∃ f : ℂ → ℂ, f ≠ 0 ∧ AnalyticOnNhd ℂ f Set.univ ∧ Differentiable ℂ f ∧
      (¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, p.eval z = f z) ∧
      (∀ z : ℂ, ‖f z‖ ≤ Real.sqrt 2 * Real.exp (‖z‖ ^ 2)) ∧
      (∀ U : Set ℂ, IsOpen U → U.Nonempty →
        ∃ N, ∀ n ≥ N, ∃ z ∈ U, iteratedDeriv n f z = 0) ∧
      (∀ s : ℕ → ℕ, StrictMono s →
        Dense {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0}) := by
  sorry

end Erdos906
