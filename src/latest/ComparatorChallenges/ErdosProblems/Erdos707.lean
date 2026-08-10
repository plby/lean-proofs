import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.Prime.Defs

namespace Erdos707

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ ⦃i₁ i₂ j₁ j₂ : α⦄, i₁ ∈ A → i₂ ∈ A → j₁ ∈ A → j₂ ∈ A →
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

def IsPerfectDifferenceSetModulo (B : Set ℤ) (v : ℕ) : Prop :=
  B.offDiag.BijOn (fun (a, b) => (a - b : ZMod v)) {x : ZMod v | x ≠ 0}

def erdos_707 : Prop :=
  ∀ A : Set ℕ, A.Finite → IsSidon A →
    ∃ (B : Set ℤ) (v : ℕ),
      v ≠ 0 ∧
      (↑) '' A ⊆ B ∧
      IsPerfectDifferenceSetModulo B v

def erdos_707_prime : Prop :=
  ∀ (A : Set ℕ), A.Finite → IsSidon A →
    ∃ (B : Set ℤ) (p : ℕ),
      Nat.Prime p ∧
      (↑) '' A ⊆ B ∧
      IsPerfectDifferenceSetModulo B (p * p + p + 1)

def erdos_707_integer : Prop :=
  ∀ A : Set ℤ, A.Finite → IsSidon A →
    ∃ (B : Set ℤ) (v : ℕ),
      v ≠ 0 ∧
      A ⊆ B ∧
      IsPerfectDifferenceSetModulo B v
end Erdos707

open Erdos707

attribute [local instance] Classical.propDecidable

theorem Erdos707.not_erdos_707P :
    Not Erdos707.erdos_707_prime
  := by
  sorry
theorem Erdos707.not_erdos_707H :
    Not Erdos707.erdos_707_integer
  := by
  sorry
theorem Erdos707.not_erdos_707H2 :
    Not Erdos707.erdos_707
  := by
  sorry
theorem Erdos707.not_erdos_707AM :
    Not Erdos707.erdos_707
  := by
  sorry
