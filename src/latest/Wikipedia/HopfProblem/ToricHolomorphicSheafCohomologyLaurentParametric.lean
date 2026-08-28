import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLaurentReciprocalKernel

/-!
# Genuine joint holomorphicity of the fixed-radius Laurent integrals

The parameter-dependent integrals equal bounded linear functionals applied
to the joint analytic boundary kernels. This proves analyticity in both
complex coordinates at once, including the reciprocal coordinate zero.
-/

noncomputable section

open Complex Set Metric

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Laurent

open HolomorphicCousin CuspNormalization.Germs.NormalIntegral

def positiveContour (f : ℂ × ℂ → ℂ) (R : ℝ) (q : ℂ × ℂ) : ℂ :=
  cauchyTransform (fun w => f (q.1, w)) R q.2

def reciprocalContour (f : ℂ × ℂ → ℂ) (R : ℝ) (q : ℂ × ℂ) : ℂ :=
  infinityKernel (fun w => f (q.1, w)) R q.2

theorem positiveContour_eq_functional {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {q : ℂ × ℂ} (hq : q ∈ ball (0 : ℂ) r ×ˢ ball 0 R) :
    positiveContour f R q = (2 * Real.pi * I : ℂ)⁻¹ ^ 2 *
      doubleCircleIntegralCLM r hr R hR (boundaryKernel r R (boundaryData hf r R hR) q) := by
  have hI := doubleCircleIntegralCLM_apply_restrict r hr R hR
    (boundaryKernel r R (boundaryData hf r R hR) q)
    (fun w : ℂ × ℂ => (w.1 - q.1)⁻¹ * (w.2 - q.2)⁻¹ * f w)
    (by
      intro ζ η hζ hη
      rw [boundaryKernel_apply _ hq]
      rfl)
  rw [hI]
  exact (weighted_doubleCircleIntegral_eq hf hr hR hq.1
    (fun η => (η - q.2)⁻¹)).symm

theorem reciprocalContour_eq_functional {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {q : ℂ × ℂ} (hq : q ∈ ball (0 : ℂ) r ×ˢ ball 0 R⁻¹) :
    reciprocalContour f R q = (2 * Real.pi * I : ℂ)⁻¹ ^ 2 *
      doubleCircleIntegralCLM r hr R hR
        (reciprocalBoundaryKernel r R (boundaryData hf r R hR) q) := by
  have hI := doubleCircleIntegralCLM_apply_restrict r hr R hR
    (reciprocalBoundaryKernel r R (boundaryData hf r R hR) q)
    (fun w : ℂ × ℂ => (w.1 - q.1)⁻¹ * ((-q.2) * (1 - w.2 * q.2)⁻¹) * f w)
    (by
      intro ζ η hζ hη
      rw [reciprocalBoundaryKernel_apply hR _ hq]
      rfl)
  rw [hI]
  exact (weighted_doubleCircleIntegral_eq hf hr hR hq.1
    (fun η => (-q.2) * (1 - η * q.2)⁻¹)).symm

/-- The outer Cauchy projection is genuinely jointly holomorphic on each
parameter disc times its interior coordinate disc. -/
theorem positiveContour_analyticOnNhd {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    AnalyticOnNhd ℂ (positiveContour f R) (ball 0 r ×ˢ ball 0 R) := by
  have ha : AnalyticOnNhd ℂ
      (fun q => (2 * Real.pi * I : ℂ)⁻¹ ^ 2 * doubleCircleIntegralCLM r hr R hR
        (boundaryKernel r R (boundaryData hf r R hR) q))
      (ball 0 r ×ˢ ball 0 R) :=
    analyticOnNhd_const.mul (analyticOnNhd_boundaryKernel_functional r R
      (boundaryData hf r R hR) (doubleCircleIntegralCLM r hr R hR))
  apply AnalyticOnNhd.congr (isOpen_ball.prod isOpen_ball) ha
  intro q hq
  exact (positiveContour_eq_functional hf hr hR hq).symm

/-- The inner Cauchy projection is genuinely jointly holomorphic in the
parameter and reciprocal coordinates, including at reciprocal zero. -/
theorem reciprocalContour_analyticOnNhd {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    AnalyticOnNhd ℂ (reciprocalContour f R) (ball 0 r ×ˢ ball 0 R⁻¹) := by
  have ha : AnalyticOnNhd ℂ
      (fun q => (2 * Real.pi * I : ℂ)⁻¹ ^ 2 * doubleCircleIntegralCLM r hr R hR
        (reciprocalBoundaryKernel r R (boundaryData hf r R hR) q))
      (ball 0 r ×ˢ ball 0 R⁻¹) :=
    analyticOnNhd_const.mul (analyticOnNhd_reciprocalBoundaryKernel_functional r R hR
      (boundaryData hf r R hR) (doubleCircleIntegralCLM r hr R hR))
  apply AnalyticOnNhd.congr (isOpen_ball.prod isOpen_ball) ha
  intro q hq
  exact (reciprocalContour_eq_functional hf hr hR hq).symm

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Laurent
