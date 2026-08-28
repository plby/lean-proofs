import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The literal two-variable Cauchy formula from slice hypotheses

The two hypotheses concern only one-variable differentiability and
continuity on the closures of the corresponding discs.  Applying the
ordinary Cauchy formula twice gives the actual iterated contour integral;
no joint analyticity or interchange of integrals is assumed.
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalytic

/-- The normalized double Cauchy integral recovers a function whose two
families of coordinate slices satisfy the one-variable Cauchy hypotheses.
The first coordinate is integrated first. -/
theorem doubleCircleIntegral_eq_of_diffContOnCl_slices
    {f : ℂ × ℂ → ℂ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (h₁ : ∀ w ∈ closedBall (0 : ℂ) R,
      DiffContOnCl ℂ (fun v : ℂ => f (v, w)) (ball 0 r))
    (h₂ : ∀ v ∈ closedBall (0 : ℂ) r,
      DiffContOnCl ℂ (fun w : ℂ => f (v, w)) (ball 0 R))
    {z : ℂ × ℂ} (hz : z ∈ ball 0 r ×ˢ ball 0 R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 2 *
      (∮ η in C(0, R), ∮ ζ in C(0, r),
        (ζ - z.1)⁻¹ * (η - z.2)⁻¹ * f (ζ, η)) = f z := by
  have hinner (η : ℂ) (hη : η ∈ sphere (0 : ℂ) R) :
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ ζ in C(0, r), (ζ - z.1)⁻¹ * (η - z.2)⁻¹ * f (ζ, η)) =
          (η - z.2)⁻¹ * f (z.1, η) := by
    have hfirst :
        (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (∮ ζ in C(0, r), (ζ - z.1)⁻¹ * f (ζ, η)) = f (z.1, η) := by
      simpa only [smul_eq_mul] using
        (h₁ η (sphere_subset_closedBall hη)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz.1
    have hfactor :
        (∮ ζ in C(0, r), (ζ - z.1)⁻¹ * (η - z.2)⁻¹ * f (ζ, η)) =
          (η - z.2)⁻¹ * (∮ ζ in C(0, r), (ζ - z.1)⁻¹ * f (ζ, η)) := by
      calc
        _ = ∮ ζ in C(0, r), (η - z.2)⁻¹ * ((ζ - z.1)⁻¹ * f (ζ, η)) := by
          apply circleIntegral.integral_congr hr.le
          intro ζ hζ
          ring
        _ = _ := circleIntegral.integral_const_mul _ _ _ _
    rw [hfactor]
    calc
      _ = (η - z.2)⁻¹ *
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
            (∮ ζ in C(0, r), (ζ - z.1)⁻¹ * f (ζ, η))) := by ring
      _ = _ := by rw [hfirst]
  have hsecond :
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ η in C(0, R), (η - z.2)⁻¹ * f (z.1, η)) = f z := by
    simpa only [smul_eq_mul, Prod.eta] using
      (h₂ z.1 (ball_subset_closedBall hz.1)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz.2
  calc
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ η in C(0, R), (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (∮ ζ in C(0, r), (ζ - z.1)⁻¹ * (η - z.2)⁻¹ * f (ζ, η))) := by
      rw [circleIntegral.integral_const_mul]
      ring
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ η in C(0, R), (η - z.2)⁻¹ * f (z.1, η)) := by
      congr 1
      exact circleIntegral.integral_congr hR.le hinner
    _ = f z := hsecond

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalytic
