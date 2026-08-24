/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 847

-/

namespace Erdos847

/-- `HasFew3APs A` is the local positive-proportion hypothesis in the upstream statement. -/
def HasFew3APs (A : Set ℕ) : Prop :=
  ∃ ε : ℝ, ε > 0 ∧ ∀ B : Set ℕ, B ⊆ A → Finite B →
    ∃ C : Set ℕ, C ⊆ B ∧ C.ncard ≥ ε * B.ncard ∧ ThreeAPFree C

theorem not_erdos_847 :
    ¬ ∀ A : Set ℕ, Infinite A → HasFew3APs A →
      ∃ n, ∃ S : Fin n → Set ℕ,
        (∀ i, ThreeAPFree (S i)) ∧ A = ⋃ i : Fin n, S i := by
  sorry
