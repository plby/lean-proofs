import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real parameters for the standard conifold boundary

The boundary coordinate change uses the coefficient `r⁻²` and its inverse
normalization factor.  For `1 < r`, both parameters are defined with a
nonzero denominator, and the determinant and squared-norm formulas simplify
to the required boundary values.
-/

namespace Wikipedia.HopfProblem.ConifoldStandardBoundary

/-- The coefficient of the adjoint term in the boundary coordinate change. -/
noncomputable def coefficient (r : ℝ) : ℝ := (r ^ 2)⁻¹

/-- The real normalization factor for the inverse boundary coordinate change. -/
noncomputable def inverseScale (r : ℝ) : ℝ := (1 - coefficient r ^ 2)⁻¹

theorem r_pos {r : ℝ} (hr : 1 < r) : 0 < r := by
  linarith

theorem r_ne_zero {r : ℝ} (hr : 1 < r) : r ≠ 0 :=
  ne_of_gt (r_pos hr)

theorem one_lt_sq {r : ℝ} (hr : 1 < r) : 1 < r ^ 2 := by
  nlinarith

theorem coefficient_mul_sq {r : ℝ} (hr : 1 < r) :
    coefficient r * r ^ 2 = 1 := by
  exact inv_mul_cancel₀ (pow_ne_zero 2 (r_ne_zero hr))

theorem coefficient_ne_zero {r : ℝ} (hr : 1 < r) :
    coefficient r ≠ 0 :=
  inv_ne_zero (pow_ne_zero 2 (r_ne_zero hr))

theorem coefficient_pos {r : ℝ} (hr : 1 < r) :
    0 < coefficient r := by
  exact inv_pos.mpr (sq_pos_of_pos (r_pos hr))

theorem coefficient_lt_one {r : ℝ} (hr : 1 < r) :
    coefficient r < 1 := by
  have hmul := coefficient_mul_sq hr
  have hpos := coefficient_pos hr
  have hsq := one_lt_sq hr
  nlinarith

theorem coefficient_sq_lt_one {r : ℝ} (hr : 1 < r) :
    coefficient r ^ 2 < 1 := by
  have hpos := coefficient_pos hr
  have hlt := coefficient_lt_one hr
  nlinarith

theorem one_sub_coefficient_sq_pos {r : ℝ} (hr : 1 < r) :
    0 < 1 - coefficient r ^ 2 := by
  linarith [coefficient_sq_lt_one hr]

theorem one_sub_coefficient_sq_ne_zero {r : ℝ} (hr : 1 < r) :
    1 - coefficient r ^ 2 ≠ 0 :=
  ne_of_gt (one_sub_coefficient_sq_pos hr)

theorem inverseScale_pos {r : ℝ} (hr : 1 < r) :
    0 < inverseScale r :=
  inv_pos.mpr (one_sub_coefficient_sq_pos hr)

theorem inverseScale_ne_zero {r : ℝ} (hr : 1 < r) :
    inverseScale r ≠ 0 :=
  ne_of_gt (inverseScale_pos hr)

theorem inverseScale_mul_one_sub_sq {r : ℝ} (hr : 1 < r) :
    inverseScale r * (1 - coefficient r ^ 2) = 1 := by
  exact inv_mul_cancel₀ (one_sub_coefficient_sq_ne_zero hr)

theorem coefficient_sq_eq_inv_pow_four (r : ℝ) :
    coefficient r ^ 2 = (r ^ 4)⁻¹ := by
  simp only [coefficient, ← inv_pow, ← pow_mul]

theorem forward_norm_scalar {r : ℝ} (hr : 1 < r) :
    (1 + coefficient r ^ 2) * r ^ 2 = r ^ 2 + (r ^ 2)⁻¹ := by
  unfold coefficient
  field_simp [r_ne_zero hr]

theorem inverse_determinant_scalar {r : ℝ} (hr : 1 < r) :
    1 - coefficient r * (r ^ 2 + (r ^ 2)⁻¹) + coefficient r ^ 2 = 0 := by
  unfold coefficient
  field_simp [r_ne_zero hr]
  ring

theorem inverse_norm_scalar {r : ℝ} (hr : 1 < r) :
    inverseScale r ^ 2 *
      ((1 + coefficient r ^ 2) * (r ^ 2 + (r ^ 2)⁻¹) - 4 * coefficient r) =
        r ^ 2 := by
  have hden := one_sub_coefficient_sq_ne_zero hr
  unfold inverseScale
  field_simp [hden]
  unfold coefficient
  field_simp [r_ne_zero hr]
  ring

end Wikipedia.HopfProblem.ConifoldStandardBoundary
