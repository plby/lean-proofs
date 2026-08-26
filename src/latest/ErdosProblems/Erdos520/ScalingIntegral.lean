import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory Set

namespace Erdos
namespace Problem520

/-- Dilation on the positive half-line, written in the division convention
used in the fresh-prime-block argument. -/
theorem integral_comp_div_Ioi (g : ℝ → ℝ) {d : ℝ} (hd : 0 < d) :
    (∫ z in Ioi (0 : ℝ), g (z / d)) =
      d * ∫ w in Ioi (0 : ℝ), g w := by
  simpa only [div_eq_mul_inv, mul_comm, inv_inv, mul_zero,
      smul_eq_mul] using!
    (integral_comp_mul_left_Ioi g 0 (inv_pos.mpr hd))

/-- Scaling identity for the inverse-square energy measure on `(0, ∞)`.

This is the generic change of variables used in equation (21): after the
substitution `z = d * w`, the Jacobian contributes `d`, while the weight
`z⁻²` contributes `d⁻²`, leaving the factor `d⁻¹`.

No integrability assumption is needed for the identity itself: Mathlib's
Bochner integral and its dilation formula agree on the nonintegrable case as
well.  In applications, integrability is supplied separately to obtain a
finite nonnegative energy.
-/
theorem integral_comp_div_mul_inv_sq_Ioi (g : ℝ → ℝ) {d : ℝ}
    (hd : 0 < d) :
    (∫ z in Ioi (0 : ℝ), g (z / d) / z ^ 2) =
      d⁻¹ * ∫ w in Ioi (0 : ℝ), g w / w ^ 2 := by
  have hscale := integral_comp_div_Ioi (fun w : ℝ => g w / w ^ 2) hd
  calc
    (∫ z in Ioi (0 : ℝ), g (z / d) / z ^ 2)
        = ∫ z in Ioi (0 : ℝ), d⁻¹ ^ 2 * (g (z / d) / (z / d) ^ 2) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro z hz
            have hz0 : z ≠ 0 := ne_of_gt hz
            field_simp [hd.ne', hz0]
    _ = d⁻¹ ^ 2 * ∫ z in Ioi (0 : ℝ), g (z / d) / (z / d) ^ 2 := by
          rw [integral_const_mul]
    _ = d⁻¹ ^ 2 * (d * ∫ w in Ioi (0 : ℝ), g w / w ^ 2) := by
          rw [hscale]
    _ = d⁻¹ * ∫ w in Ioi (0 : ℝ), g w / w ^ 2 := by
          field_simp [hd.ne']

end Problem520
end Erdos
