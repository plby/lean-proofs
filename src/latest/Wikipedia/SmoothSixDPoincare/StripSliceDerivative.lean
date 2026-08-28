import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Derivatives of horizontal and vertical strip slices

The scalar derivatives of actual slices are evaluations of the full planar
derivative at the corresponding coordinate directions.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare.StripCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_verticalSlice {F : (ℝ × ℝ) → E} {t s : ℝ}
    (hF : DifferentiableAt ℝ F (t, s)) :
    HasDerivAt (fun u : ℝ => F (t, u)) (fderiv ℝ F (t, s) (0, 1)) s := by
  have hi : HasDerivAt (fun u : ℝ => (t, u)) (0, 1) s :=
    (hasDerivAt_const s t).prodMk (hasDerivAt_id s)
  exact hF.hasFDerivAt.comp_hasDerivAt s hi

theorem hasDerivAt_horizontalSlice {F : (ℝ × ℝ) → E} {t s : ℝ}
    (hF : DifferentiableAt ℝ F (t, s)) :
    HasDerivAt (fun u : ℝ => F (u, s)) (fderiv ℝ F (t, s) (1, 0)) t := by
  have hi : HasDerivAt (fun u : ℝ => (u, s)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t s)
  exact hF.hasFDerivAt.comp_hasDerivAt t hi

end Wikipedia.SmoothSixDPoincare.StripCoordinates
