import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCompactDbar
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarOperations
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationMixedDbar

/-!
# The first correction of a two-variable local antiholomorphic primitive

A cutoff is applied only in the second coordinate.  The resulting integral
solves that component globally.  The remaining first component is proved
holomorphic in the second coordinate wherever the cutoff is one.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

/-- The data for the integral solving the second component. -/
def secondLocalizedData (χ : ℂ → ℂ) (g : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  χ q.2 * g q

/-- The first correction is an actual partial Cauchy–Green integral. -/
def firstCorrection (χ : ℂ → ℂ) (g : ℂ × ℂ → ℂ) : ℂ × ℂ → ℂ :=
  cauchySecond (secondLocalizedData χ g)

/-- The as-yet unsolved component after the first correction. -/
def firstResidual (χ : ℂ → ℂ) (f g : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  f q - dbarFirst (firstCorrection χ g) q

theorem contDiff_secondLocalizedData {χ : ℂ → ℂ} {g : ℂ × ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (secondLocalizedData χ g) :=
  (hχ.comp contDiff_snd).mul hg

theorem secondLocalizedData_eq_zero {χ : ℂ → ℂ} {g : ℂ × ℂ → ℂ}
    (z w : ℂ) (hw : w ∉ tsupport χ) : secondLocalizedData χ g (z, w) = 0 := by
  rw [secondLocalizedData, image_eq_zero_of_notMem_tsupport hw, zero_mul]

theorem contDiff_firstCorrection {χ : ℂ → ℂ} {g : ℂ × ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (firstCorrection χ g) :=
  contDiff_cauchySecond (contDiff_secondLocalizedData hχ hg) hcχ
    (fun z w hw => secondLocalizedData_eq_zero z w hw)

theorem dbarSecond_firstCorrection {χ : ℂ → ℂ} {g : ℂ × ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hg : ContDiff ℝ ∞ g)
    (q : ℂ × ℂ) :
    dbarSecond (firstCorrection χ g) q = secondLocalizedData χ g q :=
  dbarSecond_cauchySecond ((contDiff_secondLocalizedData hχ hg).of_le (by simp)) hcχ
    (fun z w hw => secondLocalizedData_eq_zero z w hw) q

theorem contDiff_firstResidual {χ : ℂ → ℂ} {f g : ℂ × ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (firstResidual χ f g) :=
  hf.sub (contDiff_dbarFirst (contDiff_firstCorrection hχ hcχ hg))

/-- The remaining component has zero antiholomorphic second derivative on
every strip where the original cutoff is exactly one. -/
theorem dbarSecond_firstResidual_eq_zero {χ : ℂ → ℂ} {f g : ℂ × ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hclosed : IsDbarClosed f g) (q : ℂ × ℂ) (hq : χ q.2 = 1) :
    dbarSecond (firstResidual χ f g) q = 0 := by
  have hu := contDiff_firstCorrection hχ hcχ hg
  have he : dbarSecond (firstCorrection χ g) = secondLocalizedData χ g :=
    funext (dbarSecond_firstCorrection hχ hcχ hg)
  change dbarSecond (fun x => f x - dbarFirst (firstCorrection χ g) x) q = 0
  rw [dbarSecond_sub ((hf.differentiable (by simp)) q)
      (((contDiff_dbarFirst hu).differentiable (by simp)) q),
    ← dbarFirst_dbarSecond hu q, he]
  change dbarSecond f q - dbarFirst (fun x => χ x.2 * g x) q = 0
  rw [dbarFirst_mul (f := fun x => χ x.2)
      (((hχ.comp contDiff_snd).differentiable (by simp)) q)
      ((hg.differentiable (by simp)) q), dbarFirst_snd, hq,
    one_mul, mul_zero, add_zero, hclosed q, sub_self]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
