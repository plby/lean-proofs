import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Iterating the Cauchy integral for an analytic quotient

If an analytic denominator is nonzero on the product of a closed disk
and a boundary circle, the Cauchy integral in the second variable equals
the iterated Cauchy integral.  The integrals are actual complex circle
integrals, and the equality uses the one-variable formula on each slice.
-/

noncomputable section

open Set Metric
open scoped Complex

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.NormalIntegral

/-- The Cauchy integral of an actual quotient in the second variable. -/
def cauchyQuotient (f g : ℂ × ℂ → ℂ) (R : ℝ) (z : ℂ × ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∮ w in C(0, R), (w - z.2)⁻¹ * (f (z.1, w) / g (z.1, w))

/-- The actual iterated Cauchy integral, first in the first variable. -/
def doubleCauchyQuotient (f g : ℂ × ℂ → ℂ) (r R : ℝ) (z : ℂ × ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 2 *
    ∮ w in C(0, R), ∮ v in C(0, r),
      (v - z.1)⁻¹ * (w - z.2)⁻¹ * (f (v, w) / g (v, w))

/-- Iteration only needs the first coordinate to be inside its disk. -/
theorem cauchyQuotient_eq_doubleCauchyQuotient_of_fst_mem
    {f g : ℂ × ℂ → ℂ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r ×ˢ closedBall 0 R))
    (hg0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, g p ≠ 0)
    {z : ℂ × ℂ} (hz : z.1 ∈ ball 0 r) :
    cauchyQuotient f g R z = doubleCauchyQuotient f g r R z := by
  have hslice (w : ℂ) (hw : w ∈ sphere 0 R) :
      AnalyticOnNhd ℂ (fun v : ℂ =>
        (w - z.2)⁻¹ * (f (v, w) / g (v, w))) (closedBall 0 r) := by
    intro v hv
    have hmem : (v, w) ∈ closedBall 0 r ×ˢ closedBall 0 R :=
      ⟨hv, sphere_subset_closedBall hw⟩
    exact analyticAt_const.mul
      (((hf (v, w) hmem).comp₂ analyticAt_id analyticAt_const).div
        ((hg (v, w) hmem).comp₂ analyticAt_id analyticAt_const)
        (hg0 (v, w) ⟨hv, hw⟩))
  have hinner (w : ℂ) (hw : w ∈ sphere 0 R) :
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ v in C(0, r), (v - z.1)⁻¹ * (w - z.2)⁻¹ *
          (f (v, w) / g (v, w))) =
        (w - z.2)⁻¹ * (f (z.1, w) / g (z.1, w)) := by
    have hdc : DiffContOnCl ℂ
        (fun v : ℂ => (w - z.2)⁻¹ * (f (v, w) / g (v, w)))
        (ball 0 r) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball (0 : ℂ) hr.ne']
      exact (hslice w hw).differentiableOn
    simpa only [smul_eq_mul, mul_assoc] using
      hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz
  unfold cauchyQuotient doubleCauchyQuotient
  calc
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ w in C(0, R), (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (∮ v in C(0, r), (v - z.1)⁻¹ * (w - z.2)⁻¹ *
            (f (v, w) / g (v, w)))) := by
      congr 1
      exact circleIntegral.integral_congr hR.le fun w hw => (hinner w hw).symm
    _ = _ := by
      simp only [circleIntegral.integral_const_mul, pow_two, mul_assoc]

/-- On the open bidisk the single and iterated Cauchy quotients agree. -/
theorem cauchyQuotient_eq_doubleCauchyQuotient
    {f g : ℂ × ℂ → ℂ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r ×ˢ closedBall 0 R))
    (hg0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, g p ≠ 0)
    {z : ℂ × ℂ} (hz : z ∈ ball 0 r ×ˢ ball 0 R) :
    cauchyQuotient f g R z = doubleCauchyQuotient f g r R z :=
  cauchyQuotient_eq_doubleCauchyQuotient_of_fst_mem hr hR hf hg hg0 hz.1

end Wikipedia.HopfProblem.CuspNormalization.Germs.NormalIntegral
