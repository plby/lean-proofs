/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-! # Orienting a finite symmetric off-diagonal sum -/

namespace Erdos822

open scoped BigOperators Classical

theorem sum_erase_symmetric_eq_twice_ordered (B : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ a b, f a b = f b a) :
    (∑ a ∈ B, ∑ b ∈ B.erase a, f a b) =
      2 * ∑ a ∈ B, ∑ b ∈ B, if a < b then f a b else 0 := by
  have hpoint (a b : ℕ) :
      (if b ≠ a then f a b else 0) =
        (if a < b then f a b else 0) + (if b < a then f b a else 0) := by
    rcases lt_trichotomy a b with h | h | h
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
    · subst b
      simp
    · simp [h, ne_of_lt h, not_lt_of_ge h.le, hf a b]
  calc
    _ = ∑ a ∈ B, ∑ b ∈ B, if b ≠ a then f a b else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.filter_ne', Finset.sum_filter]
    _ = (∑ a ∈ B, ∑ b ∈ B, if a < b then f a b else 0) +
        ∑ a ∈ B, ∑ b ∈ B, if b < a then f b a else 0 := by
      simp_rw [hpoint, Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.sum_comm (f := fun a b ↦ if b < a then f b a else 0)]
      ring

end Erdos822
