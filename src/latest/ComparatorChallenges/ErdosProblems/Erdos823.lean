import Mathlib

open Filter Topology
open scoped ArithmeticFunction.sigma

noncomputable section


namespace Erdos823

open scoped Classical in
theorem erdos_823 : True ↔
    ∀ α : ℝ, 1 ≤ α →
      ∃ n m : ℕ → ℕ,
        (∀ k, 0 < n k) ∧
        (∀ k, 0 < m k) ∧
        (∀ k, σ 1 (n k) = σ 1 (m k)) ∧
        Tendsto (fun k ↦ (n k : ℝ) / (m k : ℝ)) atTop (nhds α) := by
  sorry

end Erdos823

end
