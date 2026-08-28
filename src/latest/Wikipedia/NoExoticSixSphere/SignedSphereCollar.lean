import Wikipedia.NoExoticSixSphere.SmoothSphereRadialCollar
import Wikipedia.NoExoticSixSphere.SmoothSphereRadialDerivative
import Wikipedia.NoExoticSixSphere.SphereExtensionWithHeight
import Wikipedia.NoExoticSixSphere.GLOrthonormalization

/-!
# A smooth sphere collar with arbitrary nonzero signed height coefficient

The time coordinate is `c + slope * (‖x‖² - 1)`. Its actual radial derivative
on the sphere is `2 * slope`, while the spatial radial derivative is zero.
Thus either endpoint sign gives an immersive boundary collar whenever
the original spatial sphere map is immersive.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SignedSphereCollar

open GLOrthonormalization
open Wikipedia.SmoothSixDPoincare.SphereBoundary

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (b : Sphere n) (f : Sphere n → F) (c slope : ℝ)

def map (x : Vector (n + 1)) : ℝ × F :=
  (c + slope * definingFunction x, SmoothSphereAmbient.extension b f x)

theorem map_coe (q : Sphere n) : map b f c slope q.val = (c, f q) := by
  rw [map, (definingFunction_eq_zero_iff q.val).mpr q.property,
    SmoothSphereAmbient.extension_coe]
  simp only [mul_zero, add_zero]

theorem map_radial (u : ℝ) (hu : 1 / 2 ≤ u) (q : Sphere n) :
    map b f c slope (u • q.val) = (c + slope * (u ^ 2 - 1), f q) := by
  have hp : 0 < u := by linarith
  have hn : ‖u • q.val‖ = u := by
    rw [norm_smul, Real.norm_of_nonneg hp.le, ClosedHemisphere.unit_norm, mul_one]
  rw [map, SmoothSphereAmbient.extension_eq_radial_of_half_le b f (by rw [hn]; exact hu),
    SphereRadialRetraction.retract_pos_smul b q hp, definingFunction, hn]

variable (hf : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ f)

include hf

theorem contDiff_map : ContDiff ℝ ∞ (map b f c slope) :=
  (contDiff_const.add (contDiff_const.mul contDiff_definingFunction)).prodMk
    (SmoothSphereAmbient.contDiff_extension b f hf)

theorem fderiv_map (x : Vector (n + 1)) :
    fderiv ℝ (map b f c slope) x =
      (slope • fderiv ℝ (definingFunction (E := Vector (n + 1))) x).prod
        (fderiv ℝ (SmoothSphereAmbient.extension b f) x) := by
  have hρ := (contDiff_definingFunction (E := Vector (n + 1))).differentiable (by simp) x
  have hF := (SmoothSphereAmbient.contDiff_extension b f hf).differentiable (by simp) x
  exact (((hρ.hasFDerivAt.const_mul slope).const_add c).prodMk hF.hasFDerivAt).fderiv

theorem fderiv_map_radial (q : Sphere n) :
    fderiv ℝ (map b f c slope) q.val q.val = (2 * slope, 0) := by
  have hρ : fderiv ℝ (definingFunction (E := Vector (n + 1))) q.val q.val = 2 := by
    rw [fderiv_definingFunction, two_smul, add_apply]
    change inner ℝ q.val q.val + inner ℝ q.val q.val = 2
    rw [real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm]
    norm_num
  rw [fderiv_map b f c slope hf]
  change (slope * fderiv ℝ definingFunction q.val q.val,
    fderiv ℝ (SmoothSphereAmbient.extension b f) q.val q.val) = _
  rw [hρ, SmoothSphereAmbient.fderiv_extension_radial_zero b f hf, mul_comm slope 2]

theorem injective_fderiv_map_sphere (hslope : slope ≠ 0)
    (hi : ∀ q, Injective (mfderiv (𝓡 n) 𝓘(ℝ, F) f q)) (q : Sphere n) :
    Injective (fderiv ℝ (map b f c slope) q.val) := by
  let : Fact (Module.finrank ℝ (Vector (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hF := SmoothSphereAmbient.contDiff_extension b f hf
  have hk := common_kernel_of_immersive_sphere_extension hF.contMDiff
    (SmoothSphereAmbient.extension_coe b f) hi
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [fderiv_map b f c slope hf] at hv
  apply hk q.val ((definingFunction_eq_zero_iff q.val).mpr q.property) v
  · rw [mfderiv_eq_fderiv]
    exact congrArg Prod.snd hv
  · have ht : slope * fderiv ℝ definingFunction q.val v = 0 := congrArg Prod.fst hv
    exact (mul_eq_zero.mp ht).resolve_left hslope

end NoExoticSixSphere.SignedSphereCollar
