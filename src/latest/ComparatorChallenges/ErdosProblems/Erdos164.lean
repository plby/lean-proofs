/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos164

noncomputable def erdosWeight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log n)
def primeSet : Set ℕ :=
  { p | p.Prime }
def PrimitiveSet (A : Set ℕ) : Prop :=
  (∀ ⦃a : ℕ⦄, a ∈ A → 2 ≤ a) ∧
    ∀ ⦃a b : ℕ⦄, a ∈ A → b ∈ A → a ∣ b → a = b
noncomputable def primitiveWeightSum (A : Set ℕ) : ℝ :=
  ∑' a : A, erdosWeight (a : ℕ)
noncomputable def primeWeightSum : ℝ :=
  primitiveWeightSum primeSet

def IsPRough (p m : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ∣ m → p ≤ q
def erdos_strong (n : ℕ) : Prop :=
  ∀ ⦃A : Set ℕ⦄, PrimitiveSet A →
    A ⊆ {m : ℕ | n ∣ m ∧ IsPRough n (m / n)} →
    primitiveWeightSum A ≤ erdosWeight n

theorem erdos_164 :
    PrimitiveSet primeSet ∧
      primitiveWeightSum primeSet = primeWeightSum ∧
      ∀ A : Set ℕ, PrimitiveSet A → primitiveWeightSum A ≤ primitiveWeightSum primeSet := by
  sorry

theorem erdos_strong_of_two : erdos_strong 2 := by
  sorry

end Erdos164
theorem Erdos164.erdos_strong_of_prime :
    ∀ {p : Nat}, Nat.Prime p → Erdos164.erdos_strong p
  := by
  sorry
