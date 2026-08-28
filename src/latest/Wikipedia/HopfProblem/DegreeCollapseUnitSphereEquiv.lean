import Wikipedia.HopfProblem.DegreeCollapseDiskCone
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual unit spheres under a real linear equivalence

Normalize the image of each unit vector. The inverse is normalized in the
same way, so the construction works for arbitrary norms, not only isometries.
-/

noncomputable section

open Set Metric NormedSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.UnitSphereEquiv

open DiskCylinder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
theorem vector_ne_zero (u : Sphere (E := E)) : u.val ≠ 0 := by
  intro h
  have hn := mem_sphere_zero_iff_norm.mp u.property
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem image_ne_zero (L : E ≃L[ℝ] F) (u : Sphere (E := E)) : L u.val ≠ 0 := by
  intro h
  exact vector_ne_zero u (L.injective (h.trans (L.map_zero).symm))

def map (L : E ≃L[ℝ] F) : C(Sphere (E := E), Sphere (E := F)) where
  toFun u := ⟨normalize (L u.val),
    mem_sphere_zero_iff_norm.mpr (norm_normalize (image_ne_zero L u))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((L.continuous.comp continuous_subtype_val).norm.inv₀
      (fun u => norm_ne_zero_iff.mpr (image_ne_zero L u))).smul
      (L.continuous.comp continuous_subtype_val))

theorem map_inverse (L : E ≃L[ℝ] F) (u : Sphere (E := E)) : map L.symm (map L u) = u := by
  apply Subtype.ext
  change normalize (L.symm (‖L u.val‖⁻¹ • L u.val)) = u.val
  rw [map_smul, L.symm_apply_apply,
    normalize_smul_of_pos (inv_pos.mpr (norm_pos_iff.mpr (image_ne_zero L u)))]
  exact normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp u.property)

/-- A genuine homeomorphism of the two literal unit spheres. -/
def homeomorph (L : E ≃L[ℝ] F) : Sphere (E := E) ≃ₜ Sphere (E := F) where
  toFun := map L
  invFun := map L.symm
  left_inv := map_inverse L
  right_inv := map_inverse L.symm
  continuous_toFun := (map L).continuous
  continuous_invFun := (map L.symm).continuous

end Wikipedia.HopfProblem.DegreeCollapse.UnitSphereEquiv
