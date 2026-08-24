/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

namespace Erdos1193

open scoped Classical in
noncomputable def conv_ind (A : Set ℕ) (n : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun k => k ∈ A ∧ (n - k) ∈ A)).card

theorem not_erdos_1193 :
    ∀ n : ℕ, conv_ind Set.univ n = n + 1 := by
  sorry

end Erdos1193
