/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos157

def IsSidon (S : Set ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def IsAsymptoticBasisOfOrderThree (S : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, n = a + b + c

theorem erdos_157 :
    ∃ S : Set ℕ, S.Infinite ∧ IsSidon S ∧ IsAsymptoticBasisOfOrderThree S := by
  sorry

end Erdos157
