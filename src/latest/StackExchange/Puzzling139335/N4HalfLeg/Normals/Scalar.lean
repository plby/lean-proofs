import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Scalar bound from a half-leg span

A point in the positive quadrant of the unit circle whose weighted span
`s + c / 2` is strictly below one has `c > 4 / 5`.
-/

namespace Puzzling139335.N4HalfLeg

/-- The strict half-leg span bound forces the cosine above `4 / 5`. -/
theorem cos_gt_four_fifths_of_halfleg_span {c s : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hunit : c ^ 2 + s ^ 2 = 1)
    (hspan : s + c / 2 < 1) : (4 / 5 : ℝ) < c := by
  have hdiff : 0 < 1 - c / 2 - s := by
    linarith only [hspan]
  have hsum : 0 < 1 - c / 2 + s := by
    linarith only [hspan, hs]
  have hproduct : 0 < c * (5 * c - 4) := by
    nlinarith only [hunit, mul_pos hdiff hsum]
  have hfactor : 0 < 5 * c - 4 := (mul_pos_iff_of_pos_left hc).mp hproduct
  linarith only [hfactor]

end Puzzling139335.N4HalfLeg
