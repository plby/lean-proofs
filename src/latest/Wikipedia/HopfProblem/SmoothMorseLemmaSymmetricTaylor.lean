import Wikipedia.HopfProblem.SmoothMorseLemmaTaylor
import Wikipedia.HopfProblem.SmoothMorseLemmaBilinear

/-!
# The actual Taylor factor valued in symmetric forms

Symmetrization bundles the proved Hessian-integral factor in the genuine
normed subspace of symmetric bilinear forms. It does not alter the factor
of a smooth real function.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integral Taylor factor as an actual symmetric bilinear form. -/
def symmetricTaylorFactor (f : E → ℝ) (x : E) : SymmetricForm E :=
  symmetrize E (secondTaylorFactor f x)

/-- The symmetric-form-valued factor is genuinely smooth. -/
theorem contDiff_symmetricTaylorFactor {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (symmetricTaylorFactor f) :=
  (symmetrize E).contDiff.comp (contDiff_secondTaylorFactor hf)

/-- Bundling in the symmetric subspace leaves the literal integral unchanged. -/
theorem symmetricTaylorFactor_coe {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    (symmetricTaylorFactor f x).val = secondTaylorFactor f x := by
  ext u v
  change (2 : ℝ)⁻¹ * (secondTaylorFactor f x u v + secondTaylorFactor f x v u) =
    secondTaylorFactor f x u v
  rw [secondTaylorFactor_symmetric hf x v u]
  ring

/-- At the center the bundled Taylor factor is the actual Hessian. -/
theorem symmetricTaylorFactor_zero {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    (symmetricTaylorFactor f 0).val = fderiv ℝ (fderiv ℝ f) 0 := by
  rw [symmetricTaylorFactor_coe hf, secondTaylorFactor_zero]

/-- Exact Taylor factorization at a critical point, in the symmetric subspace. -/
theorem map_eq_add_symmetricTaylorFactor {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : fderiv ℝ f 0 = 0) (x : E) :
    f x = f 0 + (1 / 2 : ℝ) * (symmetricTaylorFactor f x).val x x := by
  rw [symmetricTaylorFactor_coe hf]
  simpa only [hc, zero_apply, add_zero] using
    map_eq_add_linear_add_secondTaylorFactor hf x

end Wikipedia.HopfProblem.SmoothMorseLemma
