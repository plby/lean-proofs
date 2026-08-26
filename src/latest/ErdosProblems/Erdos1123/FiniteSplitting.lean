import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite weighted splitting for the CH construction in Erdős problem 1123

These estimates do not use CH. A finite collection of atoms, each of mass at most
`δ`, can approximate a prescribed mass from below with error at most `δ`.
-/

namespace Erdos1123

open Finset

/-- Approximate a target mass by a subset of a finite weighted set. -/
theorem exists_subset_sum_near {α : Type*} (s : Finset α) (w : α → ℝ)
    {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t) (hts : t ≤ ∑ a ∈ s, w a)
    (hw : ∀ a ∈ s, w a ≤ δ) :
    ∃ u ⊆ s, (∑ a ∈ u, w a) ≤ t ∧ t - (∑ a ∈ u, w a) ≤ δ := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty =>
      refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
      · simpa using ht
      · simpa using (show t ≤ δ by simpa using le_trans hts hδ)
  | @insert a s has ih =>
      by_cases hsmall : t ≤ ∑ b ∈ s, w b
      · obtain ⟨u, hus, hut, htu⟩ := ih ht hsmall (fun b hb => hw b (by simp [hb]))
        exact ⟨u, fun b hb => Finset.mem_insert_of_mem (hus hb), hut, htu⟩
      · refine ⟨s, Finset.subset_insert _ _, le_of_lt (lt_of_not_ge hsmall), ?_⟩
        have ha : w a ≤ δ := hw a (Finset.mem_insert_self _ _)
        rw [Finset.sum_insert has] at hts
        linarith

/-- Splitting one target cell controls both the chosen part and its complement. -/
theorem exists_subset_two_errors {α : Type*} (s : Finset α) (w : α → ℝ)
    {a t δ : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t) (hta : t ≤ a)
    (hw₀ : ∀ x ∈ s, 0 ≤ w x) (hwδ : ∀ x ∈ s, w x ≤ δ) :
    ∃ u ⊆ s,
      |(∑ x ∈ u, w x) - t| ≤ |a - (∑ x ∈ s, w x)| + δ ∧
      |((∑ x ∈ s, w x) - (∑ x ∈ u, w x)) - (a - t)| ≤
        |a - (∑ x ∈ s, w x)| + δ := by
  let b := ∑ x ∈ s, w x
  have hb : 0 ≤ b := Finset.sum_nonneg hw₀
  obtain ⟨u, hus, hu, he⟩ := exists_subset_sum_near s w hδ
    (le_min ht hb) (min_le_right t b) hwδ
  refine ⟨u, hus, ?_, ?_⟩
  · rw [abs_le]
    have h₁ := le_abs_self (a - b)
    have h₂ := neg_le_abs (a - b)
    have h₃ := min_le_left t b
    by_cases htb : t ≤ b
    · rw [min_eq_left htb] at hu he
      constructor <;> linarith [abs_nonneg (a - b)]
    · rw [min_eq_right (le_of_not_ge htb)] at hu he
      constructor <;> linarith
  · rw [abs_le]
    have h₁ := le_abs_self (a - b)
    have h₂ := neg_le_abs (a - b)
    by_cases htb : t ≤ b
    · rw [min_eq_left htb] at hu he
      constructor <;> linarith
    · rw [min_eq_right (le_of_not_ge htb)] at hu he
      constructor <;> linarith

end Erdos1123
