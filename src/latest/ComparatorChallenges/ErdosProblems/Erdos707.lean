/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.Prime.Defs

namespace Erdos707

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ ⦃i₁ i₂ j₁ j₂ : α⦄, i₁ ∈ A → i₂ ∈ A → j₁ ∈ A → j₂ ∈ A →
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

def IsPerfectDifferenceSetModulo (B : Set ℤ) (v : ℕ) : Prop :=
  B.offDiag.BijOn (fun (a, b) => (a - b : ZMod v)) {x : ZMod v | x ≠ 0}

end Erdos707

theorem Erdos707.not_erdos_707P :
    Not (∀ (A : Set ℕ), A.Finite → Erdos707.IsSidon A →
      ∃ (B : Set ℤ) (p : ℕ),
        Nat.Prime p ∧
        (↑) '' A ⊆ B ∧
        Erdos707.IsPerfectDifferenceSetModulo B (p * p + p + 1)) := by
  sorry
theorem Erdos707.not_erdos_707H :
    Not (∀ A : Set ℤ, A.Finite → Erdos707.IsSidon A →
      ∃ (B : Set ℤ) (v : ℕ),
        v ≠ 0 ∧
        A ⊆ B ∧
        Erdos707.IsPerfectDifferenceSetModulo B v) := by
  sorry
theorem Erdos707.not_erdos_707 :
    Not (∀ A : Set ℕ, A.Finite → Erdos707.IsSidon A →
      ∃ (B : Set ℤ) (v : ℕ),
        v ≠ 0 ∧
        (↑) '' A ⊆ B ∧
        Erdos707.IsPerfectDifferenceSetModulo B v) := by
  sorry
