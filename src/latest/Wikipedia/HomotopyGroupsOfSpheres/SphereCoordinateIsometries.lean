import Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

/-! # Isometries transport the actual centered sphere charts -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def sphereIsometry (e : E ≃ₗᵢ[ℝ] F) : UnitSphere E ≃ₜ UnitSphere F where
  toFun z := ⟨e z.val, mem_sphere_zero_iff_norm.mpr (by simp)⟩
  invFun z := ⟨e.symm z.val, mem_sphere_zero_iff_norm.mpr (by simp)⟩
  left_inv z := Subtype.ext (e.symm_apply_apply z.val)
  right_inv z := Subtype.ext (e.apply_symm_apply z.val)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem tangent_map_mem (e : E ≃ₗᵢ[ℝ] F) (z : UnitSphere E) (w : Tangent z) :
    e w.val ∈ Tangent (sphereIsometry e z) := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at *
  have hw := Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.property
  change inner ℝ (e w.val) (-(e z.val)) = 0
  rw [← map_neg, e.inner_map_map]
  exact hw

def tangentIsometry (e : E ≃ₗᵢ[ℝ] F) (z : UnitSphere E) :
    Tangent z ≃ₗᵢ[ℝ] Tangent (sphereIsometry e z) where
  toFun w := ⟨e w.val, tangent_map_mem e z w⟩
  invFun w := ⟨e.symm w.val, by
    have h := tangent_map_mem e.symm (sphereIsometry e z) w
    change e.symm w.val ∈ (ℝ ∙ -(e.symm (e z.val)))ᗮ at h
    simpa only [e.symm_apply_apply] using h⟩
  left_inv w := Subtype.ext (e.symm_apply_apply w.val)
  right_inv w := Subtype.ext (e.apply_symm_apply w.val)
  map_add' v w := Subtype.ext (e.map_add v.val w.val)
  map_smul' r w := Subtype.ext (e.map_smul r w.val)
  norm_map' w := e.norm_map w.val

theorem inverse_tangentIsometry (e : E ≃ₗᵢ[ℝ] F) (z : UnitSphere E) (w : Tangent z) :
    inverse (sphereIsometry e z) (tangentIsometry e z w) = sphereIsometry e (inverse z w) := by
  apply Subtype.ext
  change stereoInvFunAux (-(e z.val)) (e w.val) = e (stereoInvFunAux (-z.val) w.val)
  simp only [stereoInvFunAux, e.norm_map, map_smul, map_add, map_neg]

end Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates
