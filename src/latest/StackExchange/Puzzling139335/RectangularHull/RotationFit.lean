import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A rectangle of height at least one half cannot fit at an oblique angle

For a unit rotation with positive coefficients, the two bounding-box widths
of a `1 × h` rectangle cannot both be at most one when `h ≥ 1/2`.
-/

namespace Puzzling139335.RectangularHull

theorem half_rectangle_rotation_impossible {c s : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hunit : c ^ 2 + s ^ 2 = 1)
    (hwidth : c + s / 2 ≤ 1) (hheight : s + c / 2 ≤ 1) : False := by
  have hc1 : c < 1 := by
    nlinarith only [hunit, sq_pos_of_pos hs, sq_nonneg (c - 1)]
  have hs1 : s < 1 := by
    nlinarith only [hunit, sq_pos_of_pos hc, sq_nonneg (s - 1)]
  have hw := mul_le_mul_of_nonneg_left hwidth hc.le
  have hh := mul_le_mul_of_nonneg_left hheight hs.le
  have hpos := mul_pos (sub_pos.mpr hc1) (sub_pos.mpr hs1)
  nlinarith only [hunit, hw, hh, hpos]

theorem rectangle_rotation_impossible {c s h : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hunit : c ^ 2 + s ^ 2 = 1)
    (hh : 1 / 2 ≤ h) (hwidth : c + h * s ≤ 1)
    (hheight : s + h * c ≤ 1) : False := by
  apply half_rectangle_rotation_impossible hc hs hunit
  · have hmul := mul_le_mul_of_nonneg_right hh hs.le
    nlinarith only [hmul, hwidth]
  · have hmul := mul_le_mul_of_nonneg_right hh hc.le
    nlinarith only [hmul, hheight]

/-- The signed rotation coefficients of any fitting rectangle must describe
an axis-aligned placement. -/
theorem rotation_fit_axis_aligned {c s h : ℝ}
    (hunit : c ^ 2 + s ^ 2 = 1) (hh : 1 / 2 ≤ h)
    (hwidth : |c| + h * |s| ≤ 1) (hheight : |s| + h * |c| ≤ 1) :
    c = 0 ∨ s = 0 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    by_contra hs
    have habs : |c| ^ 2 + |s| ^ 2 = 1 := by
      simpa only [sq_abs] using hunit
    exact rectangle_rotation_impossible (abs_pos.mpr hc) (abs_pos.mpr hs)
      habs hh hwidth hheight

end Puzzling139335.RectangularHull
