/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos347

open scoped Classical in
def has_asymptotic_density_one (S : Set ℕ) : Prop :=
  Filter.Tendsto (fun n => ((Finset.range n).filter (· ∈ S)).card / (n : ℝ)) Filter.atTop (nhds 1)
def subset_sums_of_set (S : Set ℕ) : Set ℕ :=
  {s | ∃ (B : Finset ℕ), (∀ x ∈ B, x ∈ S) ∧ s = B.sum id}

theorem erdos_347 : ∃ A : ℕ → ℕ, Monotone A ∧ (Filter.Tendsto (fun n => (A (n + 1) : ℝ) / A n) Filter.atTop (nhds 2)) ∧ (∀ S, S ⊆ Set.range A ∧ (Set.range A \ S).Finite → has_asymptotic_density_one (subset_sums_of_set S)) := by
  sorry

end Erdos347
