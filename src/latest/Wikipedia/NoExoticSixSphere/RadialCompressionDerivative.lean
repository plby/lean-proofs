import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The differential of radial compression at zero

Compression into the ball of radius `r > 0` has differential `r` times the
identity at zero. This records the precise positive scaling of a normal frame.
-/

open scoped ContDiff

namespace NoExoticSixSphere

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem hasFDerivAt_univUnitBall_zero :
    HasFDerivAt (OpenPartialHomeomorph.univUnitBall : K → K)
      (ContinuousLinearMap.id ℝ K) 0 := by
  have hs : ContDiff ℝ ∞ (fun v : K ↦ (Real.sqrt (1 + ‖v‖ ^ 2))⁻¹) := by
    refine ContDiff.inv ?_ (fun v ↦ Real.sqrt_ne_zero'.mpr (by positivity))
    exact (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun v ↦ by positivity)
  have hd := (hs.differentiable (by simp) (0 : K)).hasFDerivAt.smul
    (hasFDerivAt_id (0 : K))
  change HasFDerivAt (fun v : K ↦ (Real.sqrt (1 + ‖v‖ ^ 2))⁻¹ • v)
    (ContinuousLinearMap.id ℝ K) 0
  simpa [Pi.smul_def'] using hd

theorem hasFDerivAt_univBall_zero (r : ℝ) (hr : 0 < r) :
    HasFDerivAt (OpenPartialHomeomorph.univBall (0 : K) r)
      (r • ContinuousLinearMap.id ℝ K) 0 := by
  rw [OpenPartialHomeomorph.univBall, dif_pos hr]
  change HasFDerivAt (fun v : K ↦ r • OpenPartialHomeomorph.univUnitBall v + 0)
    (r • ContinuousLinearMap.id ℝ K) 0
  exact (hasFDerivAt_univUnitBall_zero.const_smul r).add_const 0

end NoExoticSixSphere
