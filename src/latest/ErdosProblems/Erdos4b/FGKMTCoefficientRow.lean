/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTNormalizedTransform
import Mathlib.Tactic

/-!
# Absolute row sums and individual normalized coefficients

Fixing a divisor assignment, each local absolute normalized row sums
to `v / (v - k)`. Tensorization gives a dimension-explicit bound for
each coefficient, without the radius loss of the squared l1 estimate.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι]

omit [DecidableEq α] [Fintype α] in
theorem sum_abs_localDivisorCoeff_div_row {v : ℝ}
    (hv : (Fintype.card ι : ℝ) < v) (d : Option ι) :
    (∑ r, |localDivisorCoeff v d r| / localRowWeight v r) =
      v / (v - Fintype.card ι) := by
  have hv0 : 0 ≤ v := (Nat.cast_nonneg (Fintype.card ι)).trans hv.le
  have hden : v - Fintype.card ι ≠ 0 := (sub_pos.mpr hv).ne'
  cases d with
  | none =>
    simp only [Fintype.sum_option, localDivisorCoeff, abs_one, localRowWeight,
      div_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hden]
    ring
  | some i =>
    simp [localDivisorCoeff, localRowWeight, apply_ite abs,
      ite_div, abs_of_nonneg hv0]

theorem sum_abs_assignmentCoeffKernel_div_row {v : α → ℝ}
    (hv : ∀ q, (Fintype.card ι : ℝ) < v q) (d : α → Option ι) :
    (∑ r, |assignmentCoeffKernel v d r| / assignmentRowWeight v r) =
      ∏ q, v q / (v q - Fintype.card ι) := by
  simp only [assignmentCoeffKernel, assignmentRowWeight, Finset.abs_prod,
    ← Finset.prod_div_distrib]
  rw [← Fintype.prod_sum
    (fun q r => |localDivisorCoeff (v q) (d q) r| / localRowWeight (v q) r)]
  simp only [sum_abs_localDivisorCoeff_div_row (hv _)]

theorem normalizedCoefficientTransform_abs_le {v : α → ℝ}
    (hv : ∀ q, (Fintype.card ι : ℝ) < v q)
    {F : (α → Option ι) → ℝ} (hF : ∀ r, |F r| ≤ 1) (d : α → Option ι) :
    |normalizedCoefficientTransform v F d| ≤
      ∏ q, v q / (v q - Fintype.card ι) := by
  have hrow (r : α → Option ι) : 0 < assignmentRowWeight v r := by
    apply Finset.prod_pos
    intro q _hq
    cases r q with
    | none => exact zero_lt_one
    | some i => exact sub_pos.mpr (hv q)
  calc
    _ ≤ ∑ r, |assignmentCoeffKernel v d r * (F r / assignmentRowWeight v r)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, |assignmentCoeffKernel v d r| / assignmentRowWeight v r := by
      apply Finset.sum_le_sum
      intro r _hr
      rw [abs_mul, abs_div, abs_of_pos (hrow r), ← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hF r) (abs_nonneg (assignmentCoeffKernel v d r)))
        (hrow r).le
    _ = _ := sum_abs_assignmentCoeffKernel_div_row hv d

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sum_abs_assignmentCoeffKernel_div_row
#print axioms Erdos4b.FGKMT.normalizedCoefficientTransform_abs_le
