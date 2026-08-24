/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos434

def S (E : Set ℕ) : AddSubsemigroup ℕ := AddSubsemigroup.closure E
noncomputable def non_representable_count (A : Set ℕ) : ℕ :=
  (Set.univ \ (S A : Set ℕ)).ncard
def A_opt (n k : ℕ) : Finset ℕ := Finset.Icc (n - k + 1) n

theorem erdos_434 (n k : ℕ) (hk : k ≤ n) (hk_ge_2 : k ≥ 2) :
  ∀ A : Finset ℕ, (A : Set ℕ) ⊆ Set.Icc 1 n → A.card = k →
    Finset.gcd A id = 1 →
    non_representable_count A ≤ non_representable_count (A_opt n k) := by
  sorry

end Erdos434
