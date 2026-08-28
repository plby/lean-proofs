import Wikipedia.NoExoticSixSphere.EquatorDimension

/-!
# The equator as the unit sphere of the actual orthogonal complement

Both directions preserve the underlying ambient vector. This retains the
inner product required to compare the actual chart transition with reflection.
-/

noncomputable section

namespace NoExoticSixSphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def equatorOrthogonalHomeomorph (v : UnitSphere E) :
    Equator v ≃ₜ UnitSphere ((ℝ ∙ v.val)ᗮ) where
  toFun x := ⟨⟨x.val.val, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr x.property⟩, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact ClosedHemisphere.unit_norm x.val⟩
  invFun x := ⟨⟨x.val.val, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact ClosedHemisphere.unit_norm x⟩,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    have h : Continuous (fun x : Equator v ↦ x.val.val) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (h.subtype_mk _).subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun x : UnitSphere ((ℝ ∙ v.val)ᗮ) ↦ (x.val : E)) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (h.subtype_mk _).subtype_mk _

theorem equatorOrthogonalHomeomorph_val (v : UnitSphere E) (x : Equator v) :
    ((equatorOrthogonalHomeomorph v x).val : E) = x.val.val := rfl

end NoExoticSixSphere
