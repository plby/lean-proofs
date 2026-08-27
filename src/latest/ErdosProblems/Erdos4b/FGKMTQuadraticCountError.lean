/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonCoefficientBound

/-!
# Summing interval errors in a finite coefficient quadratic

A uniform entrywise counting error costs at most the squared l1 norm
of the literal coefficient vector. The coefficients may have either sign.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem quadratic_count_error {β : Type*} [Fintype β]
    (l : β → ℝ) (N K : β → β → ℝ) (L E : ℝ)
    (herror : ∀ d e, |N d e - L * K d e| ≤ E) :
    |(∑ d, ∑ e, l d * l e * N d e) - L * (∑ d, ∑ e, l d * l e * K d e)| ≤
      E * (∑ d, |l d|) ^ 2 := by
  have hid :
      (∑ d, ∑ e, l d * l e * N d e) - L * (∑ d, ∑ e, l d * l e * K d e) =
        ∑ d, ∑ e, l d * l e * (N d e - L * K d e) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _he
    ring
  rw [hid]
  calc
    _ ≤ ∑ d, |∑ e, l d * l e * (N d e - L * K d e)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d, ∑ e, |l d * l e * (N d e - L * K d e)| :=
      Finset.sum_le_sum fun d _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d, ∑ e, |l d| * |l e| * E := by
      apply Finset.sum_le_sum
      intro d _hd
      apply Finset.sum_le_sum
      intro e _he
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (herror d e) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.quadratic_count_error
