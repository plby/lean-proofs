import Mathlib

/-!
# Scalar arithmetic for the constant-platform block reduction

The analytic part of the block reduction supplies one inequality for each
quantile block.  This file isolates and proves the remaining minimization in
the local radius and the final finite summation.
-/

open scoped BigOperators

namespace Erdos1038

noncomputable section

def blockRadiusExpression (q r C E R : ℝ) : ℝ :=
  r * (-q * Real.log R - C - q) + E + 2 * R

theorem block_radius_minimum {q r C E R : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hR : 0 < R) :
    E - q * r * Real.log (q * r / 2) - C * r ≤
      blockRadiusExpression q r C E R := by
  have hqr : 0 < q * r := mul_pos hq hr
  have hx : 0 < 2 * R / (q * r) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hx
  have hlogIdentity :
      Real.log (2 * R / (q * r)) =
        Real.log R - Real.log (q * r / 2) := by
    have hqr2 : 0 < q * r / 2 := by positivity
    have heq : 2 * R / (q * r) = R / (q * r / 2) := by
      field_simp [hqr.ne']
    rw [heq, Real.log_div hR.ne' hqr2.ne']
  rw [hlogIdentity] at hlog
  unfold blockRadiusExpression
  have hscaled := mul_le_mul_of_nonneg_left hlog hqr.le
  field_simp [hqr.ne'] at hscaled
  nlinarith

theorem block_expression_nonneg_of_energy_bound
    {q r C Ceff E R : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hR : 0 < R)
    (henergy : q * r * Real.log (q * r / 2) + Ceff * r ≤ E) :
    (Ceff - C) * r ≤ blockRadiusExpression q r C E R := by
  have hmin := block_radius_minimum (C := C) (E := E) hq hr hR
  linarith

theorem finite_block_reduction
    {ι : Type*} [Fintype ι]
    (q r E R : ι → ℝ) {C Ceff M0 L R0 : ℝ}
    (hq : ∀ i, 0 < q i) (hr : ∀ i, 0 < r i)
    (hR : ∀ i, 0 < R i)
    (hrsum : ∑ i, r i = R0)
    (henergy : ∀ i,
      q i * r i * Real.log (q i * r i / 2) + Ceff * r i ≤ E i)
    (hcalibration : M0 + (Ceff - C) * R0 = L) :
    L ≤ M0 + ∑ i, blockRadiusExpression (q i) (r i) C (E i) (R i) := by
  have hsum :
      ∑ i, (Ceff - C) * r i ≤
        ∑ i, blockRadiusExpression (q i) (r i) C (E i) (R i) := by
    exact Finset.sum_le_sum fun i hi ↦
      block_expression_nonneg_of_energy_bound
        (hq i) (hr i) (hR i) (henergy i)
  rw [← Finset.mul_sum, hrsum] at hsum
  linarith

theorem finite_block_reduction_of_effective_constant
    {ι : Type*} [Fintype ι]
    (q r E R : ι → ℝ) {C M0 L R0 : ℝ}
    (hq : ∀ i, 0 < q i) (hr : ∀ i, 0 < r i)
    (hR : ∀ i, 0 < R i) (hR0 : R0 ≠ 0)
    (hrsum : ∑ i, r i = R0)
    (henergy : ∀ i,
      q i * r i * Real.log (q i * r i / 2) +
          (C + (L - M0) / R0) * r i ≤ E i) :
    L ≤ M0 + ∑ i, blockRadiusExpression (q i) (r i) C (E i) (R i) := by
  apply finite_block_reduction q r E R hq hr hR hrsum henergy
  field_simp [hR0]
  ring

end

end Erdos1038
