import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegralKernels
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegralOperator
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegralCauchy

/-!
# Joint analyticity of the actual fixed-circle quotient extension

The quotient need not be defined holomorphically inside the integration
circle.  Nonvanishing of the denominator is required only on the boundary
cylinder.  A second application of the one-variable Cauchy formula turns
the extension into the bounded linear image of a jointly analytic
continuous-function-valued kernel.
-/

noncomputable section

open Set Metric Filter Topology
open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.NormalIntegral

variable {f g : ℂ × ℂ → ℂ} {r R : ℝ}

/-- The literal quotient restricted to the two boundary circles. -/
def quotientBoundaryData
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r ×ˢ closedBall 0 R))
    (hg0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, g p ≠ 0) :
    C(BoundaryTorus r R, ℂ) := by
  let e : BoundaryTorus r R → ℂ × ℂ := fun w => (w.1.1, w.2.1)
  have he : Continuous e :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hemem (w : BoundaryTorus r R) : e w ∈ closedBall 0 r ×ˢ closedBall 0 R :=
    ⟨sphere_subset_closedBall w.1.2, sphere_subset_closedBall w.2.2⟩
  refine ⟨fun w => f (e w) / g (e w), ?_⟩
  exact (hf.continuousOn.comp_continuous he hemem).div
    (hg.continuousOn.comp_continuous he hemem)
    (fun w => hg0 (e w) ⟨sphere_subset_closedBall w.1.2, w.2.2⟩)

@[simp] theorem quotientBoundaryData_apply
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r ×ˢ closedBall 0 R))
    (hg0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, g p ≠ 0)
    (w : BoundaryTorus r R) :
    quotientBoundaryData hf hg hg0 w = f (w.1.1, w.2.1) / g (w.1.1, w.2.1) := rfl

/-- The bounded functional computes the actual double Cauchy quotient. -/
theorem doubleCauchyQuotient_eq_functional (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r ×ˢ closedBall 0 R))
    (hg0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, g p ≠ 0)
    {z : ℂ × ℂ} (hz : z ∈ ball 0 r ×ˢ ball 0 R) :
    doubleCauchyQuotient f g r R z =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 2 *
        doubleCircleIntegralCLM r hr R hR
          (boundaryKernel r R (quotientBoundaryData hf hg hg0) z) := by
  have h := doubleCircleIntegralCLM_apply_restrict r hr R hR
    (boundaryKernel r R (quotientBoundaryData hf hg hg0) z)
    (fun w : ℂ × ℂ => (w.1 - z.1)⁻¹ * (w.2 - z.2)⁻¹ * (f w / g w))
    (by
      intro ζ η hζ hη
      rw [boundaryKernel_apply _ hz]
      rfl)
  unfold doubleCauchyQuotient
  rw [h]

/-- The double quotient integral is genuinely analytic in both variables. -/
theorem doubleCauchyQuotient_analyticOnNhd (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r ×ˢ closedBall 0 R))
    (hg0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, g p ≠ 0) :
    AnalyticOnNhd ℂ (doubleCauchyQuotient f g r R) (ball 0 r ×ˢ ball 0 R) := by
  have hL := analyticOnNhd_boundaryKernel_functional r R
    (quotientBoundaryData hf hg hg0) (doubleCircleIntegralCLM r hr R hR)
  have hscaled : AnalyticOnNhd ℂ
      (fun z => (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 2 *
        doubleCircleIntegralCLM r hr R hR
          (boundaryKernel r R (quotientBoundaryData hf hg hg0) z))
      (ball 0 r ×ˢ ball 0 R) := analyticOnNhd_const.mul hL
  intro z hz
  apply (hscaled z hz).congr
  filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds hz] with w hw
  exact (doubleCauchyQuotient_eq_functional hr hR hf hg hg0 hw).symm

/-- The actual fixed-circle quotient extension is jointly analytic on the
open bidisc.  Only the boundary cylinder must avoid the denominator's zeros. -/
theorem cauchyQuotient_analyticOnNhd (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r ×ˢ closedBall 0 R))
    (hg0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, g p ≠ 0) :
    AnalyticOnNhd ℂ (cauchyQuotient f g R) (ball 0 r ×ˢ ball 0 R) := by
  intro z hz
  apply (doubleCauchyQuotient_analyticOnNhd hr hR hf hg hg0 z hz).congr
  filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds hz] with w hw
  exact (cauchyQuotient_eq_doubleCauchyQuotient hr hR hf hg hg0 hw).symm

/-- In particular, the fixed-circle extension defines an actual analytic
germ at the origin of `ℂ × ℂ`. -/
theorem cauchyQuotient_analyticAt_zero (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r ×ˢ closedBall 0 R))
    (hg0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, g p ≠ 0) :
    AnalyticAt ℂ (cauchyQuotient f g R) 0 :=
  cauchyQuotient_analyticOnNhd hr hR hf hg hg0 0
    ⟨mem_ball_self hr, mem_ball_self hR⟩

end Wikipedia.HopfProblem.CuspNormalization.Germs.NormalIntegral
