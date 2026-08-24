/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1185

/-- `A` contains a nonconstant `k`-term arithmetic progression whose
positive common difference is a difference of two elements of `B`. -/
def HasAPWithStepInDiff (k : ℕ) (A B : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧
    (∀ j : ℕ, j < k → a + j * d ∈ A) ∧
    ∃ b₁ ∈ B, ∃ b₂ ∈ B, d = b₁ - b₂

/-! ## The rapidly divisible sequence -/

theorem not_erdos_1185 :
    ¬ (∀ δ : ℝ, 0 < δ → ∀ k : ℕ, 3 ≤ k →
      ∃ m : ℕ, 1 ≤ m ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ A B : Finset ℕ,
          A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
          δ * (N : ℝ) ≤ (A.card : ℝ) → m ≤ B.card →
          Erdos1185.HasAPWithStepInDiff k A B) := by
  sorry

end Erdos1185
