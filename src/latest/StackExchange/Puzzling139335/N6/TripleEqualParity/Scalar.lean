import Mathlib.Tactic

/-!
# The equal-parity triangle does not fit the quadrilateral's height strip

The two endpoints of the quadrilateral's diameter are `(0,0)` and `(1,t)`.
A point at the required equal distances from them would have height
`(t+1)/2` or `(t-1)/2`.  Neither height belongs to `[0,1/2]`.
-/

namespace Puzzling139335.N6.TripleEqualParity

/-- Exact scalar obstruction for the third vertex of the forced right
isosceles triangle. -/
theorem no_equal_legs_in_low_strip {t x y : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (ht : t ^ 2 - 4 * t + 1 = 0)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hleft : x ^ 2 + y ^ 2 = (1 - t) ^ 2)
    (hright : (x - 1) ^ 2 + (y - t) ^ 2 = (1 - t) ^ 2) : False := by
  have hnorm : x ^ 2 + y ^ 2 = (1 + t ^ 2) / 2 := by
    nlinarith only [hleft, ht]
  have hline : 2 * x + 2 * t * y = 1 + t ^ 2 := by
    nlinarith only [hleft, hright]
  have hproduct : (1 + t ^ 2) * ((2 * y - t) ^ 2 - 1) = 0 := by
    linear_combination 4 * hnorm - (2 * x - 2 * t * y + (1 + t ^ 2)) * hline
  have hfactor : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have hdisc : (2 * y - t) ^ 2 = 1 := by
    have := (mul_eq_zero.mp hproduct).resolve_left hfactor
    linarith only [this]
  have hlo : -1 < 2 * y - t := by linarith only [hy0, ht1]
  have hhi : 2 * y - t < 1 := by linarith only [hy1, ht0]
  have hpos := mul_pos (sub_pos.mpr hhi) (show 0 < 1 + (2 * y - t) by
    linarith only [hlo])
  nlinarith only [hpos, hdisc]

end Puzzling139335.N6.TripleEqualParity
