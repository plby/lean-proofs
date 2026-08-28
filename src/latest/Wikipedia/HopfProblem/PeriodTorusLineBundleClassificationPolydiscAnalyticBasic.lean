import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticCauchy
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegralKernels
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegralOperator

/-!
# Separate holomorphicity implies joint analyticity on a bidisc

Continuous boundary data define an actual double circle integral.  The
two one-variable Cauchy formulas identify this integral with the original
function.  The already proved continuous-function-valued kernel theorem
therefore gives genuine joint analyticity without assuming it of the input.
-/

noncomputable section

open Set Metric Filter Topology

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalytic

open CuspNormalization.Germs.NormalIntegral

variable {f : ℂ × ℂ → ℂ} {r R : ℝ}

/-- Literal restriction of continuous data to the actual boundary torus. -/
def boundaryValues (hf : ContinuousOn f (closedBall 0 r ×ˢ closedBall 0 R)) :
    C(BoundaryTorus r R, ℂ) := by
  let e : BoundaryTorus r R → ℂ × ℂ := fun w => (w.1.1, w.2.1)
  have he : Continuous e :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  refine ⟨fun w => f (e w), hf.comp_continuous he ?_⟩
  intro w
  exact ⟨sphere_subset_closedBall w.1.2, sphere_subset_closedBall w.2.2⟩

@[simp] theorem boundaryValues_apply
    (hf : ContinuousOn f (closedBall 0 r ×ˢ closedBall 0 R))
    (w : BoundaryTorus r R) : boundaryValues hf w = f (w.1.1, w.2.1) := rfl

/-- The bounded functional is the literal iterated integral of these data. -/
theorem boundaryIntegral_eq_doubleCircleIntegral (hr : 0 < r) (hR : 0 < R)
    (hf : ContinuousOn f (closedBall 0 r ×ˢ closedBall 0 R))
    {z : ℂ × ℂ} (hz : z ∈ ball 0 r ×ˢ ball 0 R) :
    doubleCircleIntegralCLM r hr R hR (boundaryKernel r R (boundaryValues hf) z) =
      ∮ η in C(0, R), ∮ ζ in C(0, r),
        (ζ - z.1)⁻¹ * (η - z.2)⁻¹ * f (ζ, η) := by
  have h := doubleCircleIntegralCLM_apply_restrict r hr R hR
    (boundaryKernel r R (boundaryValues hf) z)
    (fun w : ℂ × ℂ => (w.1 - z.1)⁻¹ * (w.2 - z.2)⁻¹ * f w)
    (by
      intro ζ η hζ hη
      rw [boundaryKernel_apply _ hz]
      rfl)
  exact h

/-- The normalized actual double-contour integral as a bounded functional. -/
def normalizedDoubleCircleIntegralCLM (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 < R) :
    C(BoundaryTorus r R, ℂ) →L[ℂ] ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 2 • doubleCircleIntegralCLM r hr R hR

@[simp] theorem normalizedDoubleCircleIntegralCLM_apply (r : ℝ) (hr : 0 < r)
    (R : ℝ) (hR : 0 < R) (u : C(BoundaryTorus r R, ℂ)) :
    normalizedDoubleCircleIntegralCLM r hr R hR u =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 2 * doubleCircleIntegralCLM r hr R hR u := rfl

/-- The original function equals the actual bounded functional applied to
the two geometric Cauchy kernels and its continuous boundary values. -/
theorem eq_boundaryKernel_functional (hr : 0 < r) (hR : 0 < R)
    (hf : ContinuousOn f (closedBall 0 r ×ˢ closedBall 0 R))
    (h₁ : ∀ w ∈ closedBall (0 : ℂ) R,
      DiffContOnCl ℂ (fun v => f (v, w)) (ball 0 r))
    (h₂ : ∀ v ∈ closedBall (0 : ℂ) r,
      DiffContOnCl ℂ (fun w => f (v, w)) (ball 0 R))
    {z : ℂ × ℂ} (hz : z ∈ ball 0 r ×ˢ ball 0 R) :
    f z = normalizedDoubleCircleIntegralCLM r hr R hR
      (boundaryKernel r R (boundaryValues hf) z) := by
  rw [normalizedDoubleCircleIntegralCLM_apply,
    boundaryIntegral_eq_doubleCircleIntegral hr hR hf hz]
  exact (doubleCircleIntegral_eq_of_diffContOnCl_slices hr hR h₁ h₂ hz).symm

/-- Joint analyticity derived from continuous data and the actual
holomorphic coordinate slices, rather than assumed in a Cauchy wrapper. -/
theorem analyticOnNhd_of_diffContOnCl_slices (hr : 0 < r) (hR : 0 < R)
    (hf : ContinuousOn f (closedBall 0 r ×ˢ closedBall 0 R))
    (h₁ : ∀ w ∈ closedBall (0 : ℂ) R,
      DiffContOnCl ℂ (fun v => f (v, w)) (ball 0 r))
    (h₂ : ∀ v ∈ closedBall (0 : ℂ) r,
      DiffContOnCl ℂ (fun w => f (v, w)) (ball 0 R)) :
    AnalyticOnNhd ℂ f (ball 0 r ×ˢ ball 0 R) := by
  have hL := analyticOnNhd_boundaryKernel_functional r R (boundaryValues hf)
    (doubleCircleIntegralCLM r hr R hR)
  have hscaled : AnalyticOnNhd ℂ
      (fun z => (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 2 *
        doubleCircleIntegralCLM r hr R hR (boundaryKernel r R (boundaryValues hf) z))
      (ball 0 r ×ˢ ball 0 R) := analyticOnNhd_const.mul hL
  apply AnalyticOnNhd.congr (isOpen_ball.prod isOpen_ball) hscaled
  intro z hz
  dsimp only
  rw [boundaryIntegral_eq_doubleCircleIntegral hr hR hf hz]
  exact doubleCircleIntegral_eq_of_diffContOnCl_slices hr hR h₁ h₂ hz

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalytic
