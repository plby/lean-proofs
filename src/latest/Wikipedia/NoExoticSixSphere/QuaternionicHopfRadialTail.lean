import Wikipedia.NoExoticSixSphere.QuaternionicHopfSouthTargetChart
import Wikipedia.NoExoticSixSphere.SphereLevelEquations

/-!
# Radial extension retains the computed Hopf tail differential

The quaternion tail is homogeneous of degree two. Radial extension
therefore divides it by the squared norm. On the actual south fiber
the tail vanishes, so its differential is unchanged by that division.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff Topology

namespace NoExoticSixSphere.QuaternionicHopf

theorem tail_polynomial_smul (r : ℝ) (x : V 8) :
    tailQuaternion (polynomial (r • x)) = r ^ 2 • tailQuaternion (polynomial x) := by
  rw [polynomial, tailQuaternion_join, polynomial, tailQuaternion_join]
  simp only [map_smul, Quaternion.star_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  ring

def radialTailExtension (a : Sphere 7) : V 8 → ℍ :=
  SphereLevelEquations.extend a (fun y : Sphere 7 ↦ tailCoordinates (sphereMap y))

theorem radialTailExtension_formula (a : Sphere 7) (x : V 8) (hx : x ≠ 0) :
    radialTailExtension a x = ‖x‖⁻¹ ^ 2 • tailQuaternion (polynomial x) := by
  change tailQuaternion (polynomial (SphereRadialRetraction.retract a x).val) = _
  have hr : (SphereRadialRetraction.retract a x).val = NormedSpace.normalize x := by
    simp only [SphereRadialRetraction.retract, dif_neg hx]
  rw [hr]
  exact tail_polynomial_smul ‖x‖⁻¹ x

theorem contDiffAt_radialTailExtension (a x : Sphere 7) :
    ContDiffAt ℝ ∞ (radialTailExtension a) x.val := by
  let : Fact (Module.finrank ℝ (V 8) = 7 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact SphereLevelEquations.contDiffAt_extend a
    ((contMDiff_tailCoordinates.comp contMDiff_sphereMap) x)

theorem tail_polynomial_eq_zero_south (x : Sphere 7) (hx : first x.val = 0) :
    tailQuaternion (polynomial x.val) = 0 := by
  rw [polynomial, tailQuaternion_join, hx, zero_mul, smul_zero]

theorem radialTailExtension_derivative (a x : Sphere 7) (hx : first x.val = 0) :
    fderiv ℝ (radialTailExtension a) x.val = tailQuaternion.comp (fderiv ℝ polynomial x.val) := by
  have hne : x.val ≠ 0 := ne_zero_of_mem_unit_sphere x
  have hc : ContDiffAt ℝ ∞ (fun z : V 8 ↦ ‖z‖⁻¹ ^ 2) x.val :=
    ((contDiffAt_norm ℝ hne).inv (norm_ne_zero_iff.mpr hne)).pow 2
  have hG := tailQuaternion.hasFDerivAt.comp x.val
    (contDiff_polynomial.differentiable (by simp) x.val).hasFDerivAt
  have hd := ((hc.differentiableAt (by simp)).hasFDerivAt).smul hG
  change HasFDerivAt (𝕜 := ℝ)
    (fun z : V 8 ↦ ‖z‖⁻¹ ^ 2 • tailQuaternion (polynomial z)) _ x.val at hd
  have he : radialTailExtension a =ᶠ[𝓝 x.val]
      (fun z : V 8 ↦ ‖z‖⁻¹ ^ 2 • tailQuaternion (polynomial z)) := by
    filter_upwards [isOpen_ne.mem_nhds hne] with z hz
    exact radialTailExtension_formula a z hz
  rw [he.fderiv_eq, hd.fderiv]
  have hzero := tail_polynomial_eq_zero_south x hx
  apply ContinuousLinearMap.ext
  intro v
  change ‖x.val‖⁻¹ ^ 2 • tailQuaternion (fderiv ℝ polynomial x.val v) +
    (fderiv ℝ (fun z : V 8 ↦ ‖z‖⁻¹ ^ 2) x.val v) • tailQuaternion (polynomial x.val) = _
  rw [hzero, smul_zero, add_zero, mem_sphere_zero_iff_norm.mp x.property,
    inv_one, one_pow, one_smul]
  rfl

end NoExoticSixSphere.QuaternionicHopf
