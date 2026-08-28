import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximationGeometric

/-!
# Uniform finite-product approximation of the double Cauchy kernel

Subtracting the product of the explicit finite geometric sums splits the
error into two scalar remainders.  The previously proved scalar bounds
give a geometric estimate independent of both boundary coordinates.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximation

/-- Uniform approximation of the actual double Cauchy kernel on a smaller
closed bidisc by the product of its two finite geometric sums. -/
theorem cauchyProduct_error_norm_le (N : ℕ) {r R : ℝ} {ξ η z w : ℂ}
    (hr : 0 ≤ r) (hrR : r < R) (hξ : ‖ξ‖ = R) (hη : ‖η‖ = R)
    (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖(ξ - z)⁻¹ * (η - w)⁻¹ - cauchyPartial N ξ z * cauchyPartial N η w‖ ≤
      3 * (r / R) ^ N / (R - r) ^ 2 := by
  have hR : 0 < R := hr.trans_lt hrR
  have hgap : 0 < R - r := sub_pos.mpr hrR
  have heq :
      (ξ - z)⁻¹ * (η - w)⁻¹ - cauchyPartial N ξ z * cauchyPartial N η w =
        ((ξ - z)⁻¹ - cauchyPartial N ξ z) * (η - w)⁻¹ +
          cauchyPartial N ξ z * ((η - w)⁻¹ - cauchyPartial N η w) := by ring
  rw [heq]
  calc
    _ ≤ ‖((ξ - z)⁻¹ - cauchyPartial N ξ z) * (η - w)⁻¹‖ +
        ‖cauchyPartial N ξ z * ((η - w)⁻¹ - cauchyPartial N η w)‖ := norm_add_le _ _
    _ = ‖(ξ - z)⁻¹ - cauchyPartial N ξ z‖ * ‖(η - w)⁻¹‖ +
        ‖cauchyPartial N ξ z‖ * ‖(η - w)⁻¹ - cauchyPartial N η w‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ((r / R) ^ N / (R - r)) * (1 / (R - r)) +
        (2 / (R - r)) * ((r / R) ^ N / (R - r)) :=
      add_le_add
        (mul_le_mul (cauchyPartial_error_norm_le N hr hrR hξ hz)
          (cauchyKernel_norm_le hrR hη hw) (norm_nonneg _) (by positivity))
        (mul_le_mul (cauchyPartial_norm_le N hr hrR hξ hz)
          (cauchyPartial_error_norm_le N hr hrR hη hw) (norm_nonneg _) (by positivity))
    _ = _ := by
      simp only [div_eq_mul_inv, ← inv_pow]
      ring

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximation
