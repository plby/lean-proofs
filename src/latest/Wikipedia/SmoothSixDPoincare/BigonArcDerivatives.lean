import Wikipedia.SmoothSixDPoincare.BigonStripCoordinates
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The actual parametrized bigon boundary arcs and their derivatives
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

def lowerBoundaryArc (t : ℝ) : ℝ × ℝ := (2 * t - 1, 0)

def upperBoundaryArc (h t : ℝ) : ℝ × ℝ := (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))

theorem hasDerivAt_lowerBoundaryArc (t : ℝ) :
    HasDerivAt lowerBoundaryArc (2, 0) t := by
  have hs : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
  exact hs.prodMk (hasDerivAt_const t (0 : ℝ))

theorem hasDerivAt_upperBoundaryArc (h t : ℝ) :
    HasDerivAt (upperBoundaryArc h) (2, -4 * h * (2 * t - 1)) t := by
  have hs : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
  have hy : HasDerivAt (fun s : ℝ => h * (1 - (2 * s - 1) ^ 2))
      (-4 * h * (2 * t - 1)) t := by
    convert HasDerivAt.const_mul h ((hasDerivAt_const t (1 : ℝ)).sub (hs.pow 2)) using 1 <;>
      first | rfl | ring
  exact hs.prodMk hy

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
