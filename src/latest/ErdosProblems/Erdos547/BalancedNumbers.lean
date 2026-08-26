import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A two-bin proportional allocation inequality

The two orientations of the second allocation share a common coefficient.
-/

namespace Erdos547.DPRS

theorem exists_balanced_coefficient_of_le (a₁ a₂ b₁ b₂ M : ℝ)
    (hb : b₁ ≤ b₂) (hsum : a₁ + a₂ + b₁ + b₂ ≤ 2 * M)
    (h₁ : a₁ + b₁ ≤ M) (h₂ : a₂ + b₁ ≤ M) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      a₁ + t * b₁ + (1 - t) * b₂ ≤ M ∧
      a₂ + t * b₂ + (1 - t) * b₁ ≤ M := by
  by_cases he : b₁ = b₂
  · refine ⟨0, le_rfl, zero_le_one, ?_, ?_⟩ <;> simp only [zero_mul, sub_zero, one_mul, add_zero]
    · simpa only [← he] using h₁
    · exact h₂
  have hD : 0 < b₂ - b₁ := sub_pos.mpr (lt_of_le_of_ne hb he)
  let s := max 0 (a₁ + b₂ - M)
  have hs : 0 ≤ s := le_max_left _ _
  have hsD : s ≤ b₂ - b₁ := max_le (by linarith) (by linarith)
  have hsU : s ≤ M - a₂ - b₁ := max_le (by linarith) (by linarith)
  have hsL : a₁ + b₂ - M ≤ s := le_max_right _ _
  let t := s / (b₂ - b₁)
  have ht0 : 0 ≤ t := div_nonneg hs hD.le
  have ht1 : t ≤ 1 := (div_le_one hD).mpr hsD
  have hmul : t * (b₂ - b₁) = s := div_mul_cancel₀ s (ne_of_gt hD)
  refine ⟨t, ht0, ht1, ?_, ?_⟩ <;> nlinarith only [hsL, hsU, hmul]

theorem exists_balanced_coefficient (a₁ a₂ b₁ b₂ M : ℝ)
    (hsum : a₁ + a₂ + b₁ + b₂ ≤ 2 * M)
    (hbound : max a₁ a₂ + min b₁ b₂ ≤ M) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      a₁ + t * b₁ + (1 - t) * b₂ ≤ M ∧
      a₂ + t * b₂ + (1 - t) * b₁ ≤ M := by
  rcases le_total b₁ b₂ with hb | hb
  · rw [min_eq_left hb] at hbound
    exact exists_balanced_coefficient_of_le a₁ a₂ b₁ b₂ M hb hsum
      (by linarith [le_max_left a₁ a₂]) (by linarith [le_max_right a₁ a₂])
  · rw [min_eq_right hb] at hbound
    obtain ⟨t, ht0, ht1, h₁, h₂⟩ := exists_balanced_coefficient_of_le a₁ a₂ b₂ b₁ M hb
      (by linarith) (by linarith [le_max_left a₁ a₂]) (by linarith [le_max_right a₁ a₂])
    refine ⟨1 - t, by linarith, by linarith, ?_, ?_⟩ <;> nlinarith only [h₁, h₂]

theorem residual_orientation_dichotomy (a₁ a₂ b₁ b₂ M : ℝ)
    (h : a₁ + a₂ + b₁ + b₂ = 2 * M) :
    max a₁ a₂ + min b₁ b₂ ≤ M ∨ max b₁ b₂ + min a₁ a₂ ≤ M := by
  by_cases ha : max a₁ a₂ + min b₁ b₂ ≤ M
  · exact Or.inl ha
  · right
    linarith [min_add_max a₁ a₂, min_add_max b₁ b₂]

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_balanced_coefficient
