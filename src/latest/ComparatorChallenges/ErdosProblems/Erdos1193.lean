import Mathlib

open Finset Nat

namespace Erdos1193

open scoped Classical in
noncomputable def conv_ind (A : Set ℕ) (n : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun k => k ∈ A ∧ (n - k) ∈ A)).card
end Erdos1193


open Finset Nat

namespace Erdos1193

open scoped Classical in
theorem erdos_convolution_counterexample :
    ∀ n : ℕ, conv_ind Set.univ n = n + 1 := by
  sorry

end Erdos1193
