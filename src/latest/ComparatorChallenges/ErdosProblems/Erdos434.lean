/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat

namespace Erdos434

def S (E : Set ℕ) : AddSubsemigroup ℕ := AddSubsemigroup.closure E
noncomputable def non_representable_count (A : Set ℕ) : ℕ :=
  (Set.univ \ (S A : Set ℕ)).ncard
def A_opt (n k : ℕ) : Finset ℕ := Finset.Icc (n - k + 1) n
end Erdos434


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos434

open scoped Classical in
theorem main_theorem_final (n k : ℕ) (hk : k ≤ n) (hk_ge_2 : k ≥ 2) :
  ∀ A : Finset ℕ, (A : Set ℕ) ⊆ Set.Icc 1 n → A.card = k →
    Finset.gcd A id = 1 →
    non_representable_count A ≤ non_representable_count (A_opt n k) := by
  sorry

end Erdos434
