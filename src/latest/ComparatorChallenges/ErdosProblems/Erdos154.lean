import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos154

def IsSidonSetNat (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d
end Erdos154


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos154

open scoped Classical in
theorem sidon_density_limit
  (m : ℕ) (hm : 2 ≤ m)
  (n_seq : ℕ → ℕ) (A_seq : ℕ → Finset ℕ)
  (h_n_tendsto : Filter.Tendsto (fun k => (n_seq k : ℝ)) Filter.atTop Filter.atTop)
  (h_subset : ∀ k, ∀ x ∈ A_seq k, x ≤ n_seq k)
  (h_sidon : ∀ k, IsSidonSetNat (A_seq k : Set ℕ))
  (h_card : Filter.Tendsto (fun k => ((A_seq k).card : ℝ) / Real.sqrt (n_seq k)) Filter.atTop (nhds 1)) :
  ∀ i < m, Filter.Tendsto (fun k => (((A_seq k).filter (fun a => a % m = i)).card : ℝ) / Real.sqrt (n_seq k)) Filter.atTop (nhds (1 / m)) := by
  sorry

end Erdos154
