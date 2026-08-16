import Mathlib

attribute [local instance] Classical.propDecidable

namespace Erdos871

theorem not_erdos_871 :
    ∃ (A : Set ℕ),
      (∀ᶠ n in Filter.atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
      (∀ t, ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
        pairs.card ≥ t ∧
          ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2) ∧
      ¬∃ (B C : Set ℕ),
        (∀ x, x ∈ A ↔ x ∈ B ∨ x ∈ C) ∧
        Disjoint B C ∧
        (∀ᶠ n in Filter.atTop, ∃ a ∈ B, ∃ b ∈ B, a + b = n) ∧
        (∀ᶠ n in Filter.atTop, ∃ a ∈ C, ∃ b ∈ C, a + b = n) := by
  sorry

end Erdos871
