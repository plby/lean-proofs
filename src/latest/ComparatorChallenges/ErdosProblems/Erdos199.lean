/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Real.Basic

namespace Erdos199

def IsThreeTermAP (a b c : ℝ) : Prop :=
  a + c = 2 * b ∧ a ≠ c
def IsInfiniteAP (S : Set ℝ) : Prop :=
  ∃ a b : ℝ, b ≠ 0 ∧ S = {x | ∃ n : ℕ, x = a + n * b}

end Erdos199

theorem Erdos199.not_erdos_199 :
    Not (∀ A : Set ℝ, (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ¬ Erdos199.IsThreeTermAP a b c) →
      (∃ S : Set ℝ, Erdos199.IsInfiniteAP S ∧ S ⊆ (Set.univ \ A))) := by
  sorry
