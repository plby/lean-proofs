/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Pointwise

namespace Erdos42

def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

def IsMaximalSidonSetIn (A : Set ℕ) (N : ℕ) : Prop :=
  A ⊆ Set.Icc 1 N ∧ IsSidon A ∧
    ∀ x ∈ Set.Icc 1 N, x ∉ A → ¬ IsSidon (insert x A)
namespace FormalConjecturesShape

universe u

end FormalConjecturesShape

theorem theorem_1_1_via_cayley :
    ∀ M : ℕ, 1 ≤ M → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Set ℕ, A ⊆ Set.Icc 1 N → IsSidon A → A.Nonempty →
        ∃ B : Set ℕ, B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
          ((A - A) ∩ (B - B) : Set ℕ) = {0} := by
  sorry

theorem erdos_42 :
    ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N),
      ∃ (B : Set ℕ), B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
        ((A - A) ∩ (B - B) : Set ℕ) = {0} := by
  sorry

end Erdos42
