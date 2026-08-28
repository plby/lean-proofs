import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Continuous spatial derivatives of a smooth parameter family

The spatial derivative is the full derivative composed with the actual
source-coordinate inclusion. This proves joint continuity directly from
smoothness of the original family.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.DiskHomotopy

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spatial_fderiv_eq (f : P → E → F) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (t : P) (x : E) :
    fderiv ℝ (f t) x = (fderiv ℝ (Function.uncurry f) (t, x)).comp
      (ContinuousLinearMap.inr ℝ P E) :=
  ((hf.differentiable (by simp) (t, x)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right t x)).fderiv

theorem continuous_spatial_fderiv (f : P → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    Continuous (fun q : P × E ↦ fderiv ℝ (f q.1) q.2) := by
  have he : (fun q : P × E ↦ fderiv ℝ (f q.1) q.2) =
      fun q ↦ (fderiv ℝ (Function.uncurry f) q).comp (ContinuousLinearMap.inr ℝ P E) := by
    funext q
    exact spatial_fderiv_eq f hf q.1 q.2
  rw [he]
  exact (hf.continuous_fderiv (by simp)).clm_comp continuous_const

theorem contDiff_spatial_fderiv (f : P → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (fun q : P × E ↦ fderiv ℝ (f q.1) q.2) := by
  have he : (fun q : P × E ↦ fderiv ℝ (f q.1) q.2) =
      fun q ↦ (fderiv ℝ (Function.uncurry f) q).comp (ContinuousLinearMap.inr ℝ P E) := by
    funext q
    exact spatial_fderiv_eq f hf q.1 q.2
  rw [he]
  exact (hf.fderiv_right (by simp)).clm_comp contDiff_const

end NoExoticSixSphere.DiskHomotopy
