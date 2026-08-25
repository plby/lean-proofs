import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# A finite sharp-cutoff error bound for complex coefficients
-/

open scoped Classical

namespace Bernays

theorem sum_subset_eq_indicator {α E : Type*} [DecidableEq α] [AddCommMonoid E]
    (A B : Finset α) (hAB : A ⊆ B) (a : α → E) :
    (∑ x ∈ A, a x) = ∑ x ∈ B, if x ∈ A then a x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨hAB h, h⟩, fun h => h.2⟩

theorem norm_mul_real_le {z : ℂ} {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    ‖z * (r : ℂ)‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr₀]
  exact mul_le_of_le_one_right (norm_nonneg z) hr₁

theorem norm_sub_mul_real_le {z : ℂ} {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    ‖z - z * (r : ℂ)‖ ≤ ‖z‖ := by
  have hid : z - z * (r : ℂ) = z * ((1 - r : ℝ) : ℂ) := by push_cast; ring
  rw [hid]
  exact norm_mul_real_le (by linarith) (by linarith)

theorem finite_cutoff_error {α : Type*} [DecidableEq α] (A B S : Finset α) (hAB : A ⊆ B) (hSB : S ⊆ B)
    (a : α → ℂ) (r : α → ℝ)
    (hr : ∀ x ∈ B, 0 ≤ r x ∧ r x ≤ 1)
    (hone : ∀ x ∈ A, x ∉ S → r x = 1) :
    ‖(∑ x ∈ A, a x) - ∑ x ∈ B, a x * (r x : ℂ)‖ ≤
      (∑ x ∈ S, ‖a x‖) + ∑ x ∈ B \ A, ‖a x‖ := by
  rw [sum_subset_eq_indicator A B hAB, ← Finset.sum_sub_distrib,
    sum_subset_eq_indicator S B hSB,
    sum_subset_eq_indicator (B \ A) B Finset.sdiff_subset, ← Finset.sum_add_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨hr₀, hr₁⟩ := hr x hx
  by_cases hxA : x ∈ A
  · have hxBA : x ∉ B \ A := by simp [hxA]
    rw [if_pos hxA, if_neg hxBA, add_zero]
    by_cases hxS : x ∈ S
    · rw [if_pos hxS]
      exact norm_sub_mul_real_le hr₀ hr₁
    · rw [if_neg hxS, hone x hxA hxS, Complex.ofReal_one, mul_one, sub_self, norm_zero]
  · have hxBA : x ∈ B \ A := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
    rw [if_neg hxA, if_pos hxBA, zero_sub, norm_neg]
    apply (norm_mul_real_le hr₀ hr₁).trans
    exact le_add_of_nonneg_left (by split_ifs <;> positivity)

end Bernays
