import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stretching heights while fixing the whole lower ray

This elementary homeomorphism is used to extend a regular-level product to
a homeomorphism of closed sublevels, without moving points below a fixed
lower regular level.
-/

noncomputable section

open Set

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

/-- Stretch the ray above `c` by the positive factor `k`, fixing all heights below `c`. -/
def stretchHeight (c k r : ℝ) : ℝ := r + (k - 1) * max 0 (r - c)

theorem stretchHeight_of_le {c k r : ℝ} (hr : r ≤ c) : stretchHeight c k r = r := by
  simp only [stretchHeight, max_eq_left (sub_nonpos.mpr hr), mul_zero, add_zero]

theorem stretchHeight_of_ge {c k r : ℝ} (hr : c ≤ r) :
    stretchHeight c k r = c + k * (r - c) := by
  rw [stretchHeight, max_eq_right (sub_nonneg.mpr hr)]
  ring

theorem stretchHeight_le_center_iff {c k r : ℝ} (hk : 0 < k) :
    stretchHeight c k r ≤ c ↔ r ≤ c := by
  by_cases hr : r ≤ c
  · rw [stretchHeight_of_le hr]
  · have hcr : c < r := lt_of_not_ge hr
    have hs : c < stretchHeight c k r := by
      rw [stretchHeight_of_ge hcr.le]
      exact lt_add_of_pos_right c (mul_pos hk (sub_pos.mpr hcr))
    exact iff_of_false (not_le_of_gt hs) hr

theorem stretchHeight_inverse {c k : ℝ} (hk : 0 < k) (r : ℝ) :
    stretchHeight c k⁻¹ (stretchHeight c k r) = r := by
  by_cases hr : r ≤ c
  · rw [stretchHeight_of_le hr, stretchHeight_of_le hr]
  · have hcr : c < r := lt_of_not_ge hr
    have hs : c ≤ stretchHeight c k r := by
      rw [stretchHeight_of_ge hcr.le]
      exact le_add_of_nonneg_right (mul_nonneg hk.le (sub_nonneg.mpr hcr.le))
    rw [stretchHeight_of_ge hs, stretchHeight_of_ge hcr.le]
    field_simp
    ring

theorem continuous_stretchHeight (c k : ℝ) : Continuous (stretchHeight c k) :=
  continuous_id.add
    (continuous_const.mul (continuous_const.max (continuous_id.sub continuous_const)))

/-- The height stretch is an actual homeomorphism of the real line. -/
def stretchHeightHomeomorph (c k : ℝ) (hk : 0 < k) : ℝ ≃ₜ ℝ where
  toFun := stretchHeight c k
  invFun := stretchHeight c k⁻¹
  left_inv := stretchHeight_inverse hk
  right_inv r := by
    simpa only [inv_inv] using stretchHeight_inverse (c := c) (inv_pos.mpr hk) r
  continuous_toFun := continuous_stretchHeight c k
  continuous_invFun := continuous_stretchHeight c k⁻¹

/-- Choosing the ratio of the two band lengths sends the upper endpoint to its prescribed value. -/
theorem stretchHeight_endpoint {c a b : ℝ} (hca : c < a) :
    stretchHeight c ((b - c) / (a - c)) a = b := by
  rw [stretchHeight_of_ge hca.le, div_mul_cancel₀ _ (sub_ne_zero.mpr hca.ne')]
  ring

/-- Only the old endpoint maps to the new endpoint. -/
theorem stretchHeight_endpoint_iff {c a b r : ℝ} (hca : c < a) (hcb : c < b) :
    stretchHeight c ((b - c) / (a - c)) r = b ↔ r = a := by
  have hk : 0 < (b - c) / (a - c) := div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)
  constructor
  · intro h
    exact (stretchHeightHomeomorph c ((b - c) / (a - c)) hk).injective
      (h.trans (stretchHeight_endpoint hca).symm)
  · rintro rfl
    exact stretchHeight_endpoint hca

/-- The stretch sends a closed sublevel of the height coordinate into the new closed sublevel. -/
theorem stretchHeight_le_target {c a b r : ℝ} (hca : c < a) (hcb : c < b) (hr : r ≤ a) :
    stretchHeight c ((b - c) / (a - c)) r ≤ b := by
  by_cases hrc : r ≤ c
  · rw [stretchHeight_of_le hrc]
    exact hrc.trans hcb.le
  · have hcr : c ≤ r := le_of_not_ge hrc
    have hk : 0 ≤ (b - c) / (a - c) := (div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)).le
    rw [stretchHeight_of_ge hcr]
    calc
      _ ≤ c + ((b - c) / (a - c)) * (a - c) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right hr c) hk)
      _ = b := by rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hca.ne')]; ring

end Wikipedia.SmoothSixDPoincare.FlowConstruction
