/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Order.Filter.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace Erdos123

def Smooth3 (a b c : ℕ) : Set ℕ :=
  {x | ∃ k l m : ℕ, x = a ^ k * b ^ l * c ^ m}

def IsPrimitive (s : Finset ℕ) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ¬x ∣ y

def IsDComplete (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ s : Finset ℕ,
      (∀ x ∈ s, x ∈ A) ∧ IsPrimitive s ∧ s.sum id = n

def PairwiseCoprime3 (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c

end Erdos123

theorem Erdos123.erdos_123 :
    ∀ a b c : ℕ, 1 < a → 1 < b → 1 < c → Erdos123.PairwiseCoprime3 a b c →
      Erdos123.IsDComplete (Erdos123.Smooth3 a b c) := by
  sorry
