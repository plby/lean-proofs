import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneApproximationBoundary

/-!
# Joint analytic Laurent contours for local disc–annulus data
-/

noncomputable section

open Complex Set Metric

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne

open Laurent CuspNormalization.Germs.NormalIntegral

theorem positiveContour_local_eq_functional {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r ×ˢ sphere 0 R))
    {q : ℂ × ℂ} (hq : q ∈ ball (0 : ℂ) r ×ˢ ball 0 R) :
    positiveContour f R q = (2 * Real.pi * I : ℂ)⁻¹ ^ 2 *
      doubleCircleIntegralCLM r hr R hR
        (boundaryKernel r R (circleBoundaryData hf.continuousOn) q) := by
  have hI := doubleCircleIntegralCLM_apply_restrict r hr R hR
    (boundaryKernel r R (circleBoundaryData hf.continuousOn) q)
    (fun w : ℂ × ℂ => (w.1 - q.1)⁻¹ * (w.2 - q.2)⁻¹ * f w)
    (by
      intro ζ η hζ hη
      rw [boundaryKernel_apply _ hq]
      rfl)
  rw [hI]
  exact (weightedDoubleCircleIntegral_eq hr hR hf hq.1 (fun η => (η - q.2)⁻¹)).symm

theorem reciprocalContour_local_eq_functional {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r ×ˢ sphere 0 R))
    {q : ℂ × ℂ} (hq : q ∈ ball (0 : ℂ) r ×ˢ ball 0 R⁻¹) :
    reciprocalContour f R q = (2 * Real.pi * I : ℂ)⁻¹ ^ 2 *
      doubleCircleIntegralCLM r hr R hR
        (reciprocalBoundaryKernel r R (circleBoundaryData hf.continuousOn) q) := by
  have hI := doubleCircleIntegralCLM_apply_restrict r hr R hR
    (reciprocalBoundaryKernel r R (circleBoundaryData hf.continuousOn) q)
    (fun w : ℂ × ℂ => (w.1 - q.1)⁻¹ * ((-q.2) * (1 - w.2 * q.2)⁻¹) * f w)
    (by
      intro ζ η hζ hη
      rw [reciprocalBoundaryKernel_apply hR _ hq]
      rfl)
  rw [hI]
  exact (weightedDoubleCircleIntegral_eq hr hR hf hq.1
    (fun η => (-q.2) * (1 - η * q.2)⁻¹)).symm

theorem positiveContour_local_analytic {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r ×ˢ sphere 0 R)) :
    AnalyticOnNhd ℂ (positiveContour f R) (ball 0 r ×ˢ ball 0 R) := by
  have ha : AnalyticOnNhd ℂ
      (fun q => (2 * Real.pi * I : ℂ)⁻¹ ^ 2 * doubleCircleIntegralCLM r hr R hR
        (boundaryKernel r R (circleBoundaryData hf.continuousOn) q))
      (ball 0 r ×ˢ ball 0 R) :=
    analyticOnNhd_const.mul (analyticOnNhd_boundaryKernel_functional r R
      (circleBoundaryData hf.continuousOn) (doubleCircleIntegralCLM r hr R hR))
  apply AnalyticOnNhd.congr (isOpen_ball.prod isOpen_ball) ha
  intro q hq
  exact (positiveContour_local_eq_functional hr hR hf hq).symm

theorem reciprocalContour_local_analytic {f : ℂ × ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r ×ˢ sphere 0 R)) :
    AnalyticOnNhd ℂ (reciprocalContour f R) (ball 0 r ×ˢ ball 0 R⁻¹) := by
  have ha : AnalyticOnNhd ℂ
      (fun q => (2 * Real.pi * I : ℂ)⁻¹ ^ 2 * doubleCircleIntegralCLM r hr R hR
        (reciprocalBoundaryKernel r R (circleBoundaryData hf.continuousOn) q))
      (ball 0 r ×ˢ ball 0 R⁻¹) :=
    analyticOnNhd_const.mul (analyticOnNhd_reciprocalBoundaryKernel_functional r R hR
      (circleBoundaryData hf.continuousOn) (doubleCircleIntegralCLM r hr R hR))
  apply AnalyticOnNhd.congr (isOpen_ball.prod isOpen_ball) ha
  intro q hq
  exact (reciprocalContour_local_eq_functional hr hR hf hq).symm

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne
