import ErdosProblems.Erdos906.Proof

/-!
Lean version: 4.33.0 (ported from 4.28.0).
Formalization: Eric Hou and GPT-5.6 Sol. See Erdos906/README.md for the pinned
source and Erdos906/COPYRIGHT for the upstream copyright notice.
-/

namespace Erdos906

/-- The original density assertion, with the witness also required to be nonpolynomial. -/
theorem erdos_906 :
    ∃ f : ℂ → ℂ, f ≠ 0 ∧ Differentiable ℂ f ∧
      (¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, p.eval z = f z) ∧
      ∀ s : ℕ → ℕ, StrictMono s →
        Dense {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0} := by
  obtain ⟨f, hzero, _, hdiff, hpoly, _, _, hdense⟩ :=
    CofiniteDerivatives.exists_transcendental_entire_with_explicit_derivative_zeros_and_growth
  exact ⟨f, hzero, hdiff, hpoly, hdense⟩

/-- The same witness satisfies the cofinite zero condition and an explicit growth bound. -/
theorem erdos_906_cofinite :
    ∃ f : ℂ → ℂ, f ≠ 0 ∧ AnalyticOnNhd ℂ f Set.univ ∧ Differentiable ℂ f ∧
      (¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, p.eval z = f z) ∧
      (∀ z : ℂ, ‖f z‖ ≤ Real.sqrt 2 * Real.exp (‖z‖ ^ 2)) ∧
      (∀ U : Set ℂ, IsOpen U → U.Nonempty →
        ∃ N, ∀ n ≥ N, ∃ z ∈ U, iteratedDeriv n f z = 0) ∧
      (∀ s : ℕ → ℕ, StrictMono s →
        Dense {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0}) :=
  CofiniteDerivatives.exists_transcendental_entire_with_explicit_derivative_zeros_and_growth

end Erdos906

#print axioms Erdos906.erdos_906
#print axioms Erdos906.erdos_906_cofinite
