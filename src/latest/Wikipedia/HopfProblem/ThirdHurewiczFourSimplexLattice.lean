import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Partition-of-unity identities for two piecewise-affine cube fillings
-/

namespace Wikipedia.HopfProblem.ThirdHurewicz

theorem fourSimplex_three_order_cases (a b c : ℝ) :
    (a ≤ b ∧ b ≤ c) ∨ (a ≤ c ∧ c ≤ b) ∨ (b ≤ a ∧ a ≤ c) ∨
      (b ≤ c ∧ c ≤ a) ∨ (c ≤ a ∧ a ≤ b) ∨ (c ≤ b ∧ b ≤ a) := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact Or.inl ⟨hab, hbc⟩
    · rcases le_total a c with hac | hca
      · exact Or.inr (Or.inl ⟨hac, hcb⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hca, hab⟩))))
  · rcases le_total a c with hac | hca
    · exact Or.inr (Or.inr (Or.inl ⟨hba, hac⟩))
    · rcases le_total b c with hbc | hcb
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hbc, hca⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hcb, hba⟩))))

theorem fourSimplex_coordinates_sum_A (a b c : ℝ) :
    (1 - max a b) + (a - min a (max b c)) + (b - min b c) +
      (min b c - min a (min b c)) + min a c = 1 := by
  rcases fourSimplex_three_order_cases a b c with
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  all_goals
    have h₃ := h₁.trans h₂
    simp_all only [min_eq_left, min_eq_right, max_eq_left, max_eq_right]
    ring

theorem fourSimplex_coordinates_sum_B (a b c : ℝ) :
    (a - min a b) + (1 - max a (max b c)) + (b - min b c) +
      min a (min b c) + (c - min a c) = 1 := by
  rcases fourSimplex_three_order_cases a b c with
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  all_goals
    have h₃ := h₁.trans h₂
    simp_all only [min_eq_left, min_eq_right, max_eq_left, max_eq_right]
    ring

end Wikipedia.HopfProblem.ThirdHurewicz
