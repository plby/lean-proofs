import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The elementary power integral in the GS A.9 contour estimate

After the contour and maximum-modulus estimates, the remaining real integral
is the integral of `σ⁻³ᐟ²` over a positive interval.  We record both its exact
value and the one-sided bound used by the quantitative argument.
-/

open Set

namespace Erdos67

noncomputable section

/-- Exact evaluation of the positive-interval integral of `σ⁻³ᐟ²`. -/
theorem integral_rpow_neg_three_halves_eq {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ σ in a..b, σ ^ (-3 / 2 : ℝ)) =
      2 * (a ^ (-1 / 2 : ℝ) - b ^ (-1 / 2 : ℝ)) := by
  rw [integral_rpow (r := (-3 / 2 : ℝ))]
  · ring_nf
  · right
    constructor
    · norm_num
    · exact notMem_uIcc_of_lt ha (ha.trans_le hab)

/-- The scalar form needed after the GS A.9 contour estimate. -/
theorem integral_inv_rpow_three_halves_le {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ σ in a..b, σ ^ (-3 / 2 : ℝ)) ≤
      2 * a ^ (-1 / 2 : ℝ) := by
  rw [integral_rpow_neg_three_halves_eq ha hab]
  have hb : 0 ≤ b ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (ha.trans_le hab).le _
  linarith

end

end Erdos67
