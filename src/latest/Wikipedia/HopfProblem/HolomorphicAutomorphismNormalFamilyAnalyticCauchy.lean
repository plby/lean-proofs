import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyAnalyticIntegral
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticCauchy

/-!
# The literal three-variable Cauchy formula

The existing double Cauchy formula handles the second and third
coordinates.  The ordinary Cauchy formula then handles the first
coordinate.  All integrals are actual contour integrals; no interchange
of integrals or pre-existing joint power-series expansion is assumed.
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold

open PeriodTorusLineBundleClassificationPolydiscAnalytic

/-- Three applications of the one-variable Cauchy formula, with the
second coordinate integrated first, then the third, then the first. -/
theorem tripleCircleIntegral_eq_of_diffContOnCl_slices
    {f : ℂ × (ℂ × ℂ) → ℂ} {r : ℝ} (hr : 0 < r)
    (h₁ : ∀ w ∈ closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r,
      DiffContOnCl ℂ (fun ξ : ℂ => f (ξ, w)) (ball 0 r))
    (h₂ : ∀ ξ ∈ closedBall (0 : ℂ) r, ∀ η ∈ closedBall (0 : ℂ) r,
      DiffContOnCl ℂ (fun ζ : ℂ => f (ξ, (ζ, η))) (ball 0 r))
    (h₃ : ∀ ξ ∈ closedBall (0 : ℂ) r, ∀ ζ ∈ closedBall (0 : ℂ) r,
      DiffContOnCl ℂ (fun η : ℂ => f (ξ, (ζ, η))) (ball 0 r))
    {z : ℂ × (ℂ × ℂ)} (hz : z ∈ ball 0 r ×ˢ (ball 0 r ×ˢ ball 0 r)) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 3 *
      (∮ ξ in C(0, r), ∮ η in C(0, r), ∮ ζ in C(0, r),
        (ξ - z.1)⁻¹ * (ζ - z.2.1)⁻¹ * (η - z.2.2)⁻¹ * f (ξ, (ζ, η))) = f z := by
  have hinner (ξ : ℂ) (hξ : ξ ∈ sphere (0 : ℂ) r) :
      (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 2 *
        (∮ η in C(0, r), ∮ ζ in C(0, r),
          (ξ - z.1)⁻¹ * (ζ - z.2.1)⁻¹ * (η - z.2.2)⁻¹ * f (ξ, (ζ, η))) =
            (ξ - z.1)⁻¹ * f (ξ, z.2) := by
    have hpair :
        (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 2 *
          (∮ η in C(0, r), ∮ ζ in C(0, r),
            (ζ - z.2.1)⁻¹ * (η - z.2.2)⁻¹ * f (ξ, (ζ, η))) = f (ξ, z.2) :=
      doubleCircleIntegral_eq_of_diffContOnCl_slices
        (f := fun w : ℂ × ℂ => f (ξ, w)) hr hr
        (h₂ ξ (sphere_subset_closedBall hξ))
        (h₃ ξ (sphere_subset_closedBall hξ)) (z := z.2) hz.2
    have hfactor :
        (∮ η in C(0, r), ∮ ζ in C(0, r),
          (ξ - z.1)⁻¹ * (ζ - z.2.1)⁻¹ * (η - z.2.2)⁻¹ * f (ξ, (ζ, η))) =
            (ξ - z.1)⁻¹ *
              (∮ η in C(0, r), ∮ ζ in C(0, r),
                (ζ - z.2.1)⁻¹ * (η - z.2.2)⁻¹ * f (ξ, (ζ, η))) := by
      calc
        _ = ∮ η in C(0, r), ∮ ζ in C(0, r),
            (ξ - z.1)⁻¹ * ((ζ - z.2.1)⁻¹ * (η - z.2.2)⁻¹ * f (ξ, (ζ, η))) := by
          apply circleIntegral.integral_congr hr.le
          intro η hη
          apply circleIntegral.integral_congr hr.le
          intro ζ hζ
          ring
        _ = _ := by simp only [circleIntegral.integral_const_mul]
    rw [hfactor]
    calc
      _ = (ξ - z.1)⁻¹ *
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 2 *
            (∮ η in C(0, r), ∮ ζ in C(0, r),
              (ζ - z.2.1)⁻¹ * (η - z.2.2)⁻¹ * f (ξ, (ζ, η)))) := by ring
      _ = _ := by rw [hpair]
  have hfirst :
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ ξ in C(0, r), (ξ - z.1)⁻¹ * f (ξ, z.2)) = f z := by
    have hslice :=
      h₁ z.2 ⟨ball_subset_closedBall hz.2.1, ball_subset_closedBall hz.2.2⟩
    simpa only [smul_eq_mul, Prod.eta] using
      hslice.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz.1
  calc
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ ξ in C(0, r), (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 2 *
          (∮ η in C(0, r), ∮ ζ in C(0, r),
            (ξ - z.1)⁻¹ * (ζ - z.2.1)⁻¹ * (η - z.2.2)⁻¹ * f (ξ, (ζ, η)))) := by
      rw [circleIntegral.integral_const_mul]
      ring
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ ξ in C(0, r), (ξ - z.1)⁻¹ * f (ξ, z.2)) := by
      congr 1
      exact circleIntegral.integral_congr hr.le hinner
    _ = f z := hfirst

/-- Complex differentiability on the actual closed cube supplies every
slice hypothesis of the normalized triple Cauchy identity. -/
theorem tripleCircleIntegral_eq_of_differentiableOn
    {f : ℂ × (ℂ × ℂ) → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f
      (closedBall 0 r ×ˢ (closedBall 0 r ×ˢ closedBall 0 r)))
    {z : ℂ × (ℂ × ℂ)} (hz : z ∈ ball 0 r ×ˢ (ball 0 r ×ˢ ball 0 r)) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 3 *
      (∮ ξ in C(0, r), ∮ η in C(0, r), ∮ ζ in C(0, r),
        (ξ - z.1)⁻¹ * (ζ - z.2.1)⁻¹ * (η - z.2.2)⁻¹ * f (ξ, (ζ, η))) = f z := by
  apply tripleCircleIntegral_eq_of_diffContOnCl_slices (f := f) hr ?_ ?_ ?_ hz
  · intro w hw
    exact (hf.comp (differentiable_id.prodMk (differentiable_const w)).differentiableOn
      (fun ξ hξ => ⟨hξ, hw⟩)).diffContOnCl_ball (subset_refl _)
  · intro ξ hξ η hη
    exact (hf.comp ((differentiable_const ξ).prodMk
      (differentiable_id.prodMk (differentiable_const η))).differentiableOn
      (fun ζ hζ => ⟨hξ, hζ, hη⟩)).diffContOnCl_ball (subset_refl _)
  · intro ξ hξ ζ hζ
    exact (hf.comp ((differentiable_const ξ).prodMk
      ((differentiable_const ζ).prodMk differentiable_id)).differentiableOn
      (fun η hη => ⟨hξ, hζ, hη⟩)).diffContOnCl_ball (subset_refl _)

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold
