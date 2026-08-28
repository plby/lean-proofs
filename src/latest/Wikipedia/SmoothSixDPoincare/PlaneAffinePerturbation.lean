import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Actual affine perturbations of smooth plane maps

The two vector parameters are the columns of the added linear map. The
derivative formula is proved for the actual Fréchet derivative and will be
used to avoid all singular differentials by a dimension argument.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.PlaneImmersion

abbrev Plane := ℝ × ℝ

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The continuous linear map with the two given columns. -/
def linearMap (A : F × F) : Plane →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight A.1 +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight A.2

theorem linearMap_apply (A : F × F) (v : Plane) : linearMap A v = v.1 • A.1 + v.2 • A.2 := rfl

/-- Add the actual linear map to the original smooth map. -/
def perturb (f : Plane → F) (A : F × F) (x : Plane) : F := f x + linearMap A x

theorem contDiff_perturb_family {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun q : (F × F) × Plane => perturb f q.1 q.2) :=
  (hf.comp contDiff_snd).add
    (((contDiff_fst.comp contDiff_snd).smul (contDiff_fst.comp contDiff_fst)).add
      ((contDiff_snd.comp contDiff_snd).smul (contDiff_snd.comp contDiff_fst)))

/-- The derivative of the perturbed map is exactly the old derivative plus the chosen columns. -/
theorem fderiv_perturb {f : Plane → F} (hf : ContDiff ℝ ∞ f) (A : F × F) (x : Plane) :
    fderiv ℝ (perturb f A) x = fderiv ℝ f x + linearMap A :=
  ((hf.differentiable (by simp) x).hasFDerivAt.add (linearMap A).hasFDerivAt).fderiv

end Wikipedia.SmoothSixDPoincare.PlaneImmersion
