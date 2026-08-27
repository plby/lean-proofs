/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFiniteTransform

/-!
# Exact diagonal and profile-variation error of normalized coefficients

On every nonzero kernel term the two assignments use the same labels,
so their denominator products agree. Thus the error involves the change
of the original profile, not a change of its normalization.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι]

def normalizedCoefficientTransform (v : α → ℝ) (F : (α → Option ι) → ℝ) :
    (α → Option ι) → ℝ :=
  finiteCoefficientTransform v (fun r => F r / assignmentRowWeight v r)

theorem square_div_mul_cancel (a b : ℝ) : (a / b) ^ 2 * b = a ^ 2 / b := by
  by_cases hb : b = 0
  · simp [hb]
  · field_simp [hb]

omit [DecidableEq α] in
theorem normalized_kernel_variation_identity (v : α → ℝ) (F : (α → Option ι) → ℝ)
    (r s : α → Option ι) :
    (F r / assignmentRowWeight v r) *
        (F s / assignmentRowWeight v s - F r / assignmentRowWeight v r) *
          assignmentQuadraticKernel v r s =
      F r * (F s - F r) * assignmentQuadraticKernel v r s /
        (assignmentRowWeight v r * assignmentRowWeight v s) := by
  by_cases h : assignmentQuadraticKernel v r s = 0
  · simp [h]
  · rw [← assignmentRowWeight_eq_of_kernel_ne_zero v h]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem normalizedCoefficientTransform_diagonal_error {v : α → ℝ}
    (hv : ∀ p, v p ≠ 0) (F : (α → Option ι) → ℝ) :
    finiteSieveQuadratic v (normalizedCoefficientTransform v F) =
      (∑ r, F r ^ 2 / assignmentRowWeight v r) +
        ∑ r, ∑ s, F r * (F s - F r) * assignmentQuadraticKernel v r s /
          (assignmentRowWeight v r * assignmentRowWeight v s) := by
  rw [normalizedCoefficientTransform, finiteSieveQuadratic_diagonal_error hv]
  congr 1
  · apply Finset.sum_congr rfl
    intro r _hr
    exact square_div_mul_cancel (F r) (assignmentRowWeight v r)
  · apply Finset.sum_congr rfl
    intro r _hr
    apply Finset.sum_congr rfl
    intro s _hs
    exact normalized_kernel_variation_identity v F r s

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.normalizedCoefficientTransform_diagonal_error
