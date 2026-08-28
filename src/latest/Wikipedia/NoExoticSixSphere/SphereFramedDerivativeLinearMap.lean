import Wikipedia.NoExoticSixSphere.SphereThreeFramedDerivative

/-!
# The original quaternionic sphere derivative commutes with fixed linear maps

The actual cutoff extension commutes with a continuous linear map, because
that map preserves scalar multiplication. Differentiating this identity
retains the original radial extension and quaternionic tangent frame.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothSphereAmbient

variable {n : ℕ} {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem extension_postcomp_clm (L : F →L[ℝ] G) (b : Sphere n) (f : Sphere n → F) :
    extension b (L ∘ f) = L ∘ extension b f := by
  funext x
  simp only [extension, Function.comp_apply, map_smul]

end NoExoticSixSphere.SmoothSphereAmbient

namespace NoExoticSixSphere.SphereThreeTangentFrame

open GLOrthonormalization Stiefel

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem framedDerivative_postcomp_clm (L : F →L[ℝ] G) (f : Sphere 3 → F)
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, F) ∞ f) (s : Sphere 3) :
    framedDerivative (L ∘ f) s = L.comp (framedDerivative f s) := by
  unfold framedDerivative
  rw [SmoothSphereAmbient.extension_postcomp_clm]
  have hE := (SmoothSphereAmbient.contDiff_extension (pole 3) f hf).differentiable
    (by simp) s.val
  rw [(L.hasFDerivAt.comp s.val hE.hasFDerivAt).fderiv]
  exact ContinuousLinearMap.comp_assoc _ _ _

end NoExoticSixSphere.SphereThreeTangentFrame
