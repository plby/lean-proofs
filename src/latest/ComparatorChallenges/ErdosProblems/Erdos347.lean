/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos347

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise


set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical in
def has_asymptotic_density_one (S : Set ℕ) : Prop :=
  Filter.Tendsto (fun n => ((Finset.range n).filter (· ∈ S)).card / (n : ℝ)) Filter.atTop (nhds 1)
open scoped Classical in
def subset_sums_of_set (S : Set ℕ) : Set ℕ :=
  {s | ∃ (B : Finset ℕ), (∀ x ∈ B, x ∈ S) ∧ s = B.sum id}
end Erdos347


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos347

open scoped Classical in
theorem answer_is_yes : ∃ A : ℕ → ℕ, Monotone A ∧ (Filter.Tendsto (fun n => (A (n + 1) : ℝ) / A n) Filter.atTop (nhds 2)) ∧ (∀ S, S ⊆ Set.range A ∧ (Set.range A \ S).Finite → has_asymptotic_density_one (subset_sums_of_set S)) := by
  sorry

end Erdos347
