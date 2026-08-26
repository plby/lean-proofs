import Mathlib

namespace Erdos477

def IsTiling (A B : Set ℤ) : Prop :=
  ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n

def OriginalStatement : Prop :=
  ∃ f : Polynomial ℤ, 2 ≤ f.natDegree ∧
    ∃ A : Set ℤ, IsTiling A (Set.range (fun k : ℤ => f.eval k))

theorem erdos477_sixth_power :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ,
      p.1 ∈ A ∧ p.2 ∈ Set.range (fun k : ℤ => k ^ 6) ∧ p.1 + p.2 = n := by
  sorry

theorem erdos_477 : OriginalStatement := by
  sorry

end Erdos477
