import Wikipedia.NoExoticSixSphere.ManifoldParityBallRadial
import Mathlib.Analysis.Convex.Contractible

/-!
# The actual punctured open four-ball and its three-sphere

Radial coordinates give a homeomorphism with the product of the unit
three-sphere and the open unit interval. Contracting that interval to one half
gives an actual homotopy equivalence whose inverse is the half-radius sphere.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.PuncturedUnitBall

open GLOrthonormalization

abbrev Space := {z : Vector 4 // ‖z‖ < 1 ∧ z ≠ 0}

def halfRadius : Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩

theorem norm_radius_smul (s : Sphere 3) (r : Ioo (0 : ℝ) 1) :
    ‖r.val • s.val‖ = r.val := by
  have hs : ‖s.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using s.property
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.property.1, hs, mul_one]

def radialHomeomorph : Space ≃ₜ Sphere 3 × Ioo (0 : ℝ) 1 where
  toFun z := (⟨‖z.val‖⁻¹ • z.val, by
    simp only [mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr z.property.2)⟩,
    ⟨‖z.val‖, norm_pos_iff.mpr z.property.2, z.property.1⟩)
  invFun p := ⟨p.2.val • p.1.val, by
    refine ⟨?_, ?_⟩
    · rw [norm_radius_smul]
      exact p.2.property.2
    · apply norm_pos_iff.mp
      rw [norm_radius_smul]
      exact p.2.property.1⟩
  left_inv z := by
    apply Subtype.ext
    change ‖z.val‖ • (‖z.val‖⁻¹ • z.val) = z.val
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr z.property.2), one_smul]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change ‖p.2.val • p.1.val‖⁻¹ • (p.2.val • p.1.val) = p.1.val
      rw [norm_radius_smul, smul_smul, inv_mul_cancel₀ p.2.property.1.ne', one_smul]
    · exact Subtype.ext (norm_radius_smul p.1 p.2)
  continuous_toFun := by
    have hnorm : Continuous (fun z : Space ↦ ‖z.val‖) := continuous_subtype_val.norm
    have hv := (hnorm.inv₀ (fun z ↦ norm_ne_zero_iff.mpr z.property.2)).smul
      continuous_subtype_val
    exact (hv.subtype_mk _).prodMk (hnorm.subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)

def radiusContraction : (ContinuousMap.id (Ioo (0 : ℝ) 1)).Homotopy
    (ContinuousMap.const _ halfRadius) where
  toFun p := ⟨(p.1 : ℝ) * halfRadius.val + (1 - (p.1 : ℝ)) * p.2.val, by
    exact (convex_Ioo (0 : ℝ) 1) halfRadius.property p.2.property
      p.1.property.1 (sub_nonneg.mpr p.1.property.2) (add_sub_cancel _ _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_fst).mul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp continuous_snd))
  map_zero_left r := Subtype.ext (by simp)
  map_one_left r := Subtype.ext (by simp)

def radiusPointEquiv : (Ioo (0 : ℝ) 1) ≃ₕ Unit where
  toFun := ContinuousMap.const _ ()
  invFun := ContinuousMap.const _ halfRadius
  left_inv := ⟨radiusContraction.symm⟩
  right_inv := by
    convert Homotopic.refl (ContinuousMap.id Unit) using 1
    ext u

def productSphereEquiv : (Sphere 3 × Ioo (0 : ℝ) 1) ≃ₕ Sphere 3 :=
  ((ContinuousMap.HomotopyEquiv.refl (Sphere 3)).prodCongr radiusPointEquiv).trans
    (Homeomorph.prodUnique (Sphere 3) Unit).toHomotopyEquiv

def sphereEquiv : Space ≃ₕ Sphere 3 :=
  radialHomeomorph.toHomotopyEquiv.trans productSphereEquiv

theorem sphereEquiv_apply (z : Space) :
    (sphereEquiv z).val = ‖z.val‖⁻¹ • z.val := rfl

theorem sphereEquiv_symm_apply (s : Sphere 3) :
    (sphereEquiv.symm s).val = (1 / 2 : ℝ) • s.val := rfl

end NoExoticSixSphere.PuncturedUnitBall
