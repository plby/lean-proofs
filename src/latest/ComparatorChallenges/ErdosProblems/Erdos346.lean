import Mathlib

namespace Erdos346

/-- Finite sums of distinct terms whose indices belong to the allowed set. -/
def subsetSums (a : ℕ → ℕ) (I : Set ℕ) : Set ℕ :=
  {t | ∃ F : Finset ℕ, ↑F ⊆ I ∧ ∑ i ∈ F, a i = t}

/-- A sequence with the two deletion properties and nonconvergent quotients. -/
theorem erdos_346_counterexample :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 0 < a n) ∧
      (∀ D : Set ℕ, D.Finite →
        ∃ H, ∀ n, H ≤ n → n ∈ subsetSums a Dᶜ) ∧
      (∀ D : Set ℕ, D.Infinite →
        ∀ H, ∃ n, H ≤ n ∧ n ∉ subsetSums a Dᶜ) ∧
      (∀ n, (6 : ℝ) / 5 ≤ (a (n + 1) : ℝ) / a n) ∧
      (∃ N : ℕ → ℕ, StrictMono N ∧
        Filter.Tendsto (fun j => (a (N j) : ℝ) / a (N j - 1)) Filter.atTop
          (nhds Real.goldenRatio) ∧
        Filter.Tendsto (fun j => (a (N j + 1) : ℝ) / a (N j)) Filter.atTop
          (nhds (Real.goldenRatio + (1 : ℝ) / 4))) ∧
      ¬ ∃ x : ℝ, Filter.Tendsto (fun n => (a (n + 1) : ℝ) / a n)
        Filter.atTop (nhds x) := by
  sorry

/-- The deletion hypotheses and a uniform ratio gap do not force convergence. -/
theorem not_erdos_346 :
    ¬ ∀ a : ℕ → ℕ, StrictMono a → (∀ n, 0 < a n) →
      (∀ D : Set ℕ, D.Finite →
        ∃ H, ∀ n, H ≤ n → n ∈ subsetSums a Dᶜ) →
      (∀ D : Set ℕ, D.Infinite →
        ∀ H, ∃ n, H ≤ n ∧ n ∉ subsetSums a Dᶜ) →
      (∃ ε : ℝ, 0 < ε ∧ ∀ n, 1 + ε ≤ (a (n + 1) : ℝ) / a n) →
      Filter.Tendsto (fun n => (a (n + 1) : ℝ) / a n) Filter.atTop
        (nhds Real.goldenRatio) := by
  sorry

end Erdos346
