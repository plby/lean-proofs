import Wikipedia.NoExoticSixSphere.SmoothSphereAmbientExtension
import Wikipedia.SmoothSixDPoincare.SphereBoundaryKernel

/-!
# An immersive boundary collar in one new normal coordinate

A Euclidean-valued sphere map extends smoothly to its ambient space. Adding
the height `‖x‖² - 1` makes its derivative injective on the boundary whenever
the original sphere map is immersive. Every interior point has nonzero
height, so it misses the entire original ambient space.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.SphereExtensionWithHeight

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def map (b : Sphere n) (f : Sphere n → F) (x : EuclideanSpace ℝ (Fin (n + 1))) : F × ℝ :=
  (SmoothSphereAmbient.extension b f x, definingFunction x)

theorem map_coe (b : Sphere n) (f : Sphere n → F) (s : Sphere n) :
    map b f s.val = (f s, 0) := by
  rw [map, SmoothSphereAmbient.extension_coe,
    (definingFunction_eq_zero_iff s.val).mpr s.property]

theorem contDiff_map (b : Sphere n) (f : Sphere n → F)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ f) : ContDiff ℝ ∞ (map b f) :=
  (SmoothSphereAmbient.contDiff_extension b f hf).prodMk contDiff_definingFunction

theorem injOn_map_sphere (b : Sphere n) (f : Sphere n → F) (hi : Injective f) :
    InjOn (map b f) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  intro x hx y hy h
  let sx : Sphere n := ⟨x, hx⟩
  let sy : Sphere n := ⟨y, hy⟩
  have he : f sx = f sy := by
    have h' : map b f sx.val = map b f sy.val := h
    rw [map_coe, map_coe] at h'
    exact congrArg Prod.fst h'
  exact congrArg Subtype.val (hi he)

/-- The height derivative detects exactly the radial direction missing from the sphere tangent. -/
theorem injective_fderiv_map_sphere (b : Sphere n) (f : Sphere n → F)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ f)
    (hi : ∀ s, Injective (mfderiv (𝓡 n) 𝓘(ℝ, F) f s)) (s : Sphere n) :
    Injective (fderiv ℝ (map b f) s.val) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have he := SmoothSphereAmbient.contDiff_extension b f hf
  have hk := common_kernel_of_immersive_sphere_extension he.contMDiff
    (SmoothSphereAmbient.extension_coe b f) hi
  have hρ : DifferentiableAt ℝ
      (definingFunction (E := EuclideanSpace ℝ (Fin (n + 1)))) s.val :=
    contDiff_definingFunction.contDiffAt.differentiableAt (by simp)
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hd := (he.contDiffAt.differentiableAt (by simp)).hasFDerivAt.prodMk hρ.hasFDerivAt
  rw [show fderiv ℝ (map b f) s.val = _ from hd.fderiv] at hv
  apply hk s.val ((definingFunction_eq_zero_iff s.val).mpr s.property) v
  · rw [mfderiv_eq_fderiv]
    exact congrArg Prod.fst hv
  · exact congrArg Prod.snd hv

/-- The open disk misses the entire original Euclidean target, not merely the boundary image. -/
theorem avoids_oldAmbient (b : Sphere n) (f : Sphere n → F)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ ball 0 1) :
    map b f x ∉ (univ : Set F) ×ˢ ({0} : Set ℝ) := by
  intro h
  have hs := (definingFunction_eq_zero_iff x).mp (mem_singleton_iff.mp h.2)
  have he : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hs
  have hl : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
  exact (ne_of_lt hl) he

end NoExoticSixSphere.SphereExtensionWithHeight
