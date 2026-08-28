import Wikipedia.NoExoticSixSphere.SphereThreeFramedDerivative

/-!
# The original sphere-frame derivative under a nonlinear smooth ambient map

Near the sphere the actual cutoff vanishes, so the two ambient extensions
agree as germs. The chain rule therefore applies to the original framed
derivative even though a nonlinear map need not commute with the cutoff
extension away from the sphere.
-/

noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothSphereAmbient

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem extension_postcomp_eventuallyEq (b : Sphere n) (g : E → F)
    (f : Sphere n → E) (s : Sphere n) :
    extension b (g ∘ f) =ᶠ[𝓝 s.val] g ∘ extension b f := by
  filter_upwards [extension_eventuallyEq_radial b (g ∘ f) s,
    extension_eventuallyEq_radial b f s] with v hgf hf
  change extension b (g ∘ f) v = g (extension b f v)
  change extension b (g ∘ f) v = g (f (SphereRadialRetraction.retract b v)) at hgf
  change extension b f v = f (SphereRadialRetraction.retract b v) at hf
  rw [hgf, hf]

theorem fderiv_extension_postcomp_contDiff (b : Sphere n) (g : E → F)
    (hg : ContDiff ℝ ∞ g) (f : Sphere n → E) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ f)
    (s : Sphere n) :
    fderiv ℝ (extension b (g ∘ f)) s.val =
      (fderiv ℝ g (f s)).comp (fderiv ℝ (extension b f) s.val) := by
  have hgE : DifferentiableAt ℝ g (extension b f s.val) := by
    rw [extension_coe]
    exact hg.differentiable (by simp) (f s)
  rw [(extension_postcomp_eventuallyEq b g f s).fderiv_eq,
    fderiv_comp s.val hgE ((contDiff_extension b f hf).differentiable (by simp) s.val),
    extension_coe]

end NoExoticSixSphere.SmoothSphereAmbient

namespace NoExoticSixSphere.SphereThreeTangentFrame

open Stiefel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem framedDerivative_postcomp_contDiff (g : E → F) (hg : ContDiff ℝ ∞ g)
    (f : Sphere 3 → E) (hf : ContMDiff (𝓡 3) 𝓘(ℝ, E) ∞ f) (s : Sphere 3) :
    framedDerivative (g ∘ f) s = (fderiv ℝ g (f s)).comp (framedDerivative f s) := by
  unfold framedDerivative
  rw [SmoothSphereAmbient.fderiv_extension_postcomp_contDiff (pole 3) g hg f hf s]
  exact ContinuousLinearMap.comp_assoc _ _ _

end NoExoticSixSphere.SphereThreeTangentFrame
