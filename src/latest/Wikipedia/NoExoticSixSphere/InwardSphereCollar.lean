import Wikipedia.NoExoticSixSphere.SmoothSphereRadialDerivative
import Wikipedia.NoExoticSixSphere.SphereExtensionWithHeight

/-!
# A smooth radial collar in a prescribed inward direction

The ambient collar is the radial extension of the sphere map minus
`(‖x‖² - 1)` times the radial extension of the inward vector. Its actual
boundary derivative is injective when a covector separates that vector
from the sphere tangent. No extension into a nonlinear target is assumed.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.InwardSphereCollar

open Wikipedia.SmoothSixDPoincare.SphereBoundary

variable {p : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def map (b : Sphere p) (f ν : Sphere p → F)
    (x : EuclideanSpace ℝ (Fin (p + 1))) : F :=
  SmoothSphereAmbient.extension b f x -
    definingFunction x • SmoothSphereAmbient.extension b ν x

theorem map_coe (b : Sphere p) (f ν : Sphere p → F) (s : Sphere p) :
    map b f ν s.val = f s := by
  rw [map, SmoothSphereAmbient.extension_coe,
    (definingFunction_eq_zero_iff s.val).mpr s.property, zero_smul, sub_zero]

theorem contDiff_map (b : Sphere p) (f ν : Sphere p → F)
    (hf : ContMDiff (𝓡 p) 𝓘(ℝ, F) ∞ f)
    (hν : ContMDiff (𝓡 p) 𝓘(ℝ, F) ∞ ν) : ContDiff ℝ ∞ (map b f ν) :=
  (SmoothSphereAmbient.contDiff_extension b f hf).sub
    (contDiff_definingFunction.smul (SmoothSphereAmbient.contDiff_extension b ν hν))

theorem fderiv_map_coe (b : Sphere p) (f ν : Sphere p → F)
    (hf : ContMDiff (𝓡 p) 𝓘(ℝ, F) ∞ f)
    (hν : ContMDiff (𝓡 p) 𝓘(ℝ, F) ∞ ν) (s : Sphere p)
    (v : EuclideanSpace ℝ (Fin (p + 1))) :
    fderiv ℝ (map b f ν) s.val v =
      fderiv ℝ (SmoothSphereAmbient.extension b f) s.val v -
        fderiv ℝ definingFunction s.val v • ν s := by
  have hF := ((SmoothSphereAmbient.contDiff_extension b f hf).differentiable
    (by simp) s.val).hasFDerivAt
  have hN := ((SmoothSphereAmbient.contDiff_extension b ν hν).differentiable
    (by simp) s.val).hasFDerivAt
  have hρ := (contDiff_definingFunction.differentiable (by simp) s.val).hasFDerivAt
  have hD := hF.sub (hρ.smul hN)
  rw [show fderiv ℝ (map b f ν) s.val = _ from hD.fderiv]
  simp only [sub_apply, ContinuousLinearMap.smulRight_apply,
    SmoothSphereAmbient.extension_coe,
    (definingFunction_eq_zero_iff s.val).mpr s.property, zero_smul, zero_add]

theorem fderiv_map_radial (b : Sphere p) (f ν : Sphere p → F)
    (hf : ContMDiff (𝓡 p) 𝓘(ℝ, F) ∞ f)
    (hν : ContMDiff (𝓡 p) 𝓘(ℝ, F) ∞ ν) (s : Sphere p) :
    fderiv ℝ (map b f ν) s.val s.val = -(2 : ℝ) • ν s := by
  have hρ : fderiv ℝ (definingFunction (E := EuclideanSpace ℝ (Fin (p + 1))))
      s.val s.val = 2 := by
    rw [fderiv_definingFunction, two_smul, add_apply]
    change inner ℝ s.val s.val + inner ℝ s.val s.val = 2
    rw [real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm]
    norm_num
  rw [fderiv_map_coe b f ν hf hν,
    SmoothSphereAmbient.fderiv_extension_radial_zero b f hf, hρ, zero_sub, neg_smul]

theorem covector_extension_zero (b : Sphere p) (f : Sphere p → F)
    (hf : ContMDiff (𝓡 p) 𝓘(ℝ, F) ∞ f) (s : Sphere p) (ξ : F →L[ℝ] ℝ)
    (hξ : ∀ w, ξ (mfderiv (𝓡 p) 𝓘(ℝ, F) f s w) = 0)
    (v : EuclideanSpace ℝ (Fin (p + 1))) :
    ξ (fderiv ℝ (SmoothSphereAmbient.extension b f) s.val v) = 0 := by
  obtain ⟨w, hw⟩ := SmoothSphereAmbient.range_fderiv_extension_le b f hf s ⟨v, rfl⟩
  exact (congrArg ξ hw).symm.trans (hξ w)

theorem injective_fderiv_map_coe (b : Sphere p) (f ν : Sphere p → F)
    (hf : ContMDiff (𝓡 p) 𝓘(ℝ, F) ∞ f)
    (hν : ContMDiff (𝓡 p) 𝓘(ℝ, F) ∞ ν)
    (hi : ∀ s, Injective (mfderiv (𝓡 p) 𝓘(ℝ, F) f s))
    (s : Sphere p) (ξ : F →L[ℝ] ℝ)
    (hξ : ∀ w, ξ (mfderiv (𝓡 p) 𝓘(ℝ, F) f s w) = 0)
    (hξν : ξ (ν s) ≠ 0) : Injective (fderiv ℝ (map b f ν) s.val) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (p + 1))) = p + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hF := SmoothSphereAmbient.contDiff_extension b f hf
  have hk := common_kernel_of_immersive_sphere_extension hF.contMDiff
    (SmoothSphereAmbient.extension_coe b f) hi
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [fderiv_map_coe b f ν hf hν] at hv
  have hz := congrArg ξ hv
  rw [map_sub, map_smul, covector_extension_zero b f hf s ξ hξ, map_zero] at hz
  have hρ : fderiv ℝ definingFunction s.val v = 0 :=
    (mul_eq_zero.mp (neg_eq_zero.mp (by
      simpa only [zero_sub, smul_eq_mul] using hz))).resolve_right hξν
  have hfv : fderiv ℝ (SmoothSphereAmbient.extension b f) s.val v = 0 := by
    simpa only [hρ, zero_smul, sub_zero] using hv
  exact hk s.val ((definingFunction_eq_zero_iff s.val).mpr s.property) v
    (by rw [mfderiv_eq_fderiv]; exact hfv) hρ

end NoExoticSixSphere.InwardSphereCollar
