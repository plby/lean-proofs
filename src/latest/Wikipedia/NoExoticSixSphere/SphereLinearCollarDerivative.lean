import Wikipedia.NoExoticSixSphere.SphereLinearDiskExtension
import Wikipedia.NoExoticSixSphere.SpanningDiskFramedCollar

/-!
# The actual radial collar derivative under a linear sphere isometry

Near each original sphere point, radial retraction intertwines the two
maps. Differentiating this genuine germ identity gives the source-linear
chain rule for the original collar, including its defining height.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereLinearReparametrization

open GLOrthonormalization SmoothSphereAmbient StabilizedSpanningDisk
open Wikipedia.SmoothSixDPoincare.SphereBoundary

variable (L : Vector 4 ≃ₗᵢ[ℝ] Vector 4)

theorem sphereMap_retract (b : Sphere 3) {x : Vector 4} (hx : x ≠ 0) :
    sphereMap L (SphereRadialRetraction.retract b x) =
      SphereRadialRetraction.retract b (L x) := by
  have hLx : L x ≠ 0 := by simpa only [map_zero] using L.injective.ne hx
  apply Subtype.ext
  rw [sphereMap_val]
  simp only [SphereRadialRetraction.retract, dif_neg hx, dif_neg hLx,
    NormedSpace.normalize, map_smul, L.norm_map]

theorem extension_precomp_germ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : Sphere 3) (f : Sphere 3 → F) (s : Sphere 3) :
    extension b (f ∘ sphereMap L) =ᶠ[𝓝 s.val] (extension b f ∘ L) := by
  have hL : Tendsto L (𝓝 s.val) (𝓝 (sphereMap L s).val) := L.continuous.continuousAt
  filter_upwards [extension_eventuallyEq_radial b (f ∘ sphereMap L) s,
    (extension_eventuallyEq_radial b f (sphereMap L s)).comp_tendsto hL,
    eventually_ne_nhds (ne_zero_of_mem_unit_sphere s)] with x h₀ h₁ hx
  dsimp only [comp_apply] at h₀ h₁
  change extension b (f ∘ sphereMap L) x = extension b f (L x)
  rw [h₀, h₁]
  change f (sphereMap L (SphereRadialRetraction.retract b x)) =
    f (SphereRadialRetraction.retract b (L x))
  rw [sphereMap_retract L b hx]

theorem definingFunction_linear (x : Vector 4) : definingFunction (L x) = definingFunction x := by
  simp only [definingFunction, L.norm_map]

theorem collar_precomp_germ {N : ℕ} (b : Sphere 3) (f : Sphere 3 → Vector N)
    (s : Sphere 3) :
    collar b (f ∘ sphereMap L) =ᶠ[𝓝 s.val] (collar b f ∘ L) := by
  filter_upwards [extension_precomp_germ L b f s] with x hx
  dsimp only [comp_apply] at hx
  change coordinates N 4 ((extension b (f ∘ sphereMap L) x, definingFunction x), 0) =
    coordinates N 4 ((extension b f (L x), definingFunction (L x)), 0)
  rw [hx, definingFunction_linear]

theorem fderiv_collar_precomp {N : ℕ} (b : Sphere 3) (f : Sphere 3 → Vector N)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (s : Sphere 3) :
    fderiv ℝ (collar b (f ∘ sphereMap L)) s.val =
      (fderiv ℝ (collar b f) (sphereMap L s).val).comp
        L.toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [(collar_precomp_germ L b f s).fderiv_eq]
  have hc : ContDiff ℝ ∞ (collar b f) :=
    (coordinates N 4).contDiff.comp ((SphereExtensionWithHeight.contDiff_map b f hf).prodMk
      contDiff_const)
  exact ((hc.differentiable (by simp) (L s.val)).hasFDerivAt.comp s.val
    L.toContinuousLinearEquiv.hasFDerivAt).fderiv

end NoExoticSixSphere.SphereLinearReparametrization
