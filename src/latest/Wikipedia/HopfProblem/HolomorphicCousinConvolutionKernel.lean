import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Local integrability of the complex Cauchy kernel

The inverse function on `ℂ` has norm `‖z‖⁻¹`, which is locally integrable
in real dimension two.  This proof uses the total inverse function, whose
value at zero is zero, without removing any points from the domain.
-/

noncomputable section

open MeasureTheory Metric

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- The complex inverse kernel is locally integrable for planar Lebesgue measure. -/
theorem locallyIntegrable_complex_inv : LocallyIntegrable (fun z : ℂ => z⁻¹) := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
    (by simp [Complex.finrank_real_complex])
    (by norm_num [Complex.finrank_real_complex]) ?_ ?_
  · filter_upwards with z
    simp only [norm_inv, Real.rpow_neg_one, one_mul, le_refl]
  · exact Measurable.aestronglyMeasurable (by fun_prop)

/-- The inverse kernel is integrable on every compact subset of the plane. -/
theorem integrableOn_complex_inv_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    IntegrableOn (fun z : ℂ => z⁻¹) K :=
  locallyIntegrable_complex_inv.integrableOn_isCompact hK

/-- Closed discs of any center and radius have an integrable inverse kernel. -/
theorem integrableOn_complex_inv_closedBall (c : ℂ) (R : ℝ) :
    IntegrableOn (fun z : ℂ => z⁻¹) (closedBall c R) :=
  integrableOn_complex_inv_of_isCompact (isCompact_closedBall c R)

/-- Open discs of any center and radius have an integrable inverse kernel. -/
theorem integrableOn_complex_inv_ball (c : ℂ) (R : ℝ) :
    IntegrableOn (fun z : ℂ => z⁻¹) (ball c R) :=
  (integrableOn_complex_inv_closedBall c R).mono_set ball_subset_closedBall

end Wikipedia.HopfProblem.HolomorphicCousin
