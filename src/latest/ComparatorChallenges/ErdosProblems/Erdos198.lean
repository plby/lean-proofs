/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos198

def IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d
variable {α : Type*} [AddCommMonoid α]

def IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}
def IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, IsAPOfLengthWith s l a d

theorem not_erdos_198 : ¬ ∀ A : Set ℕ, IsSidon A → (∃ Y, IsAPOfLength Y ⊤ ∧ Y ⊆ Aᶜ) := by
  sorry

end Erdos198
