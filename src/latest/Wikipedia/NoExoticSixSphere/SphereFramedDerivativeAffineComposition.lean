import Wikipedia.NoExoticSixSphere.SphereFramedDerivativeComposition

/-!
# Constant ambient translations disappear from the original framed derivative

This applies to an arbitrary smooth sphere map, not merely a linear
parametrization. The original ambient extension and quaternionic source
frame are retained through the proved germ-level chain rule.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereThreeTangentFrame

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem framedDerivative_postcomp_affine (L : E →L[ℝ] F) (c : F)
    (f : Sphere 3 → E) (hf : ContMDiff (𝓡 3) 𝓘(ℝ, E) ∞ f) (s : Sphere 3) :
    framedDerivative (fun q ↦ c + L (f q)) s = L.comp (framedDerivative f s) := by
  have hg : ContDiff ℝ ∞ (fun v ↦ c + L v) := contDiff_const.add L.contDiff
  have hd : HasFDerivAt (fun v ↦ c + L v) L (f s) := L.hasFDerivAt.const_add c
  change framedDerivative ((fun v ↦ c + L v) ∘ f) s = _
  rw [framedDerivative_postcomp_contDiff _ hg f hf s, hd.fderiv]

end NoExoticSixSphere.SphereThreeTangentFrame
