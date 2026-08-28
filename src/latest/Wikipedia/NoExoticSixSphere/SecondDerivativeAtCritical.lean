import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The second derivative along a curve at a critical point

At a critical point, the curve-acceleration term in the second chain rule
vanishes. The actual second derivative is the Hessian evaluated twice on the
actual tangent vector.
-/

open Filter
open scoped Topology ContDiff

namespace NoExoticSixSphere.SecondDerivativeAtCritical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem deriv_deriv_comp {f : E → ℝ} {γ : ℝ → E} {s : ℝ}
    (hf : ContDiffAt ℝ 2 f (γ s)) (hγ : ContDiffAt ℝ 2 γ s)
    (hcrit : fderiv ℝ f (γ s) = 0) :
    deriv (deriv (fun t ↦ f (γ t))) s =
      fderiv ℝ (fderiv ℝ f) (γ s) (deriv γ s) (deriv γ s) := by
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) (γ s) := hf.fderiv_right (by norm_num)
  have hdγ : ContDiffAt ℝ 1 (deriv γ) s := hγ.derivWithin (by norm_num)
  have hF : HasDerivAt (fun t ↦ fderiv ℝ f (γ t))
      (fderiv ℝ (fderiv ℝ f) (γ s) (deriv γ s)) s :=
    (hdf.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt s
      (hγ.differentiableAt (by norm_num)).hasDerivAt
  have hpair := hF.clm_apply (hdγ.differentiableAt one_ne_zero).hasDerivAt
  simp only [hcrit, zero_apply, add_zero] at hpair
  have heq : deriv (fun t ↦ f (γ t)) =ᶠ[𝓝 s]
      (fun t ↦ fderiv ℝ f (γ t) (deriv γ t)) := by
    filter_upwards [hγ.continuousAt.eventually (hf.eventually (by norm_num)),
      hγ.eventually (by norm_num)] with t hft hγt
    exact ((hft.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (hγt.differentiableAt (by norm_num)).hasDerivAt).deriv
  exact (hpair.congr_of_eventuallyEq heq).deriv

end NoExoticSixSphere.SecondDerivativeAtCritical
