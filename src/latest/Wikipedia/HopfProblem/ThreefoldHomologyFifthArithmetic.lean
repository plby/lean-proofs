import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

/-!
# The integral residual calculation in fifth homology

The cusp coefficient is left as an arbitrary integer.  The actual signed
elliptic coefficients and the common regular-fibre equation force the
remaining Wang integer to vanish, regardless of that cusp coefficient.
-/

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FifthDegree

/-- No value for the integral cusp coefficient is needed in the residual calculation. -/
theorem signed_residual_coordinate_zero (k u v d : ℤ)
    (hthree : 3 * u = k) (hfour : -4 * v = k)
    (hregular : u + v = d * k) : k = 0 := by
  have h : (12 * d - 1) * k = 0 := by
    linear_combination 4 * hthree - 3 * hfour - 12 * hregular
  have hn : 12 * d - 1 ≠ 0 := by omega
  exact (mul_eq_zero.mp h).resolve_left hn

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FifthDegree
