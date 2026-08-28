import Wikipedia.NoExoticSixSphere.CoorientedHypersurfaceNormal

/-!
# The defining differential of the actual lifted unit normal

Orthogonal projection subtracts a hypersurface tangent vector, so it does
not change the defining differential. Normalization multiplies that value
by a positive scalar whenever the transverse differential is nonzero.
-/

noncomputable section

open Function Set

namespace NoExoticSixSphere.CoorientedHypersurfaceNormal

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (D : V →L[ℝ] E) (l : V →L[ℝ] ℝ)

theorem exists_unitNormal_lift (u : V) :
    ∃ v, D v = unitNormal D l u ∧ l v = ‖projected D l u‖⁻¹ * l u := by
  obtain ⟨z, hz, he⟩ := (tangent D l).starProjection_apply_mem (D u)
  have hzero : l z = 0 := hz
  have hp : projected D l u = D u - D z := by
    rw [projected, Submodule.starProjection_orthogonal_val]
    exact congrArg (fun w : E ↦ D u - w) he.symm
  refine ⟨‖projected D l u‖⁻¹ • (u - z), ?_, ?_⟩
  · change D (‖projected D l u‖⁻¹ • (u - z)) =
      ‖projected D l u‖⁻¹ • projected D l u
    rw [map_smul, map_sub, ← hp]
  · rw [map_smul, map_sub, hzero, sub_zero]
    rfl

theorem level_of_unitNormal_lift (hD : Injective D) (u v : V)
    (hv : D v = unitNormal D l u) : l v = ‖projected D l u‖⁻¹ * l u := by
  obtain ⟨w, hw, hl⟩ := exists_unitNormal_lift D l u
  exact (congrArg l (hD (hv.trans hw.symm))).trans hl

theorem level_unitNormal_lift_negative (hD : Injective D) (u v : V)
    (hu : l u < 0) (hv : D v = unitNormal D l u) : l v < 0 := by
  rw [level_of_unitNormal_lift D l hD u v hv]
  have hn : projected D l u ≠ 0 := fun hz ↦ hu.ne
    ((projected_eq_zero_iff D l hD u).mp hz)
  exact mul_neg_of_pos_of_neg (inv_pos.mpr (norm_pos_iff.mpr hn)) hu

theorem exists_negative_unitNormal_lift (hD : Injective D) (u : V) (hu : l u < 0) :
    ∃ v, D v = unitNormal D l u ∧ l v < 0 := by
  obtain ⟨v, hv, _⟩ := exists_unitNormal_lift D l u
  exact ⟨v, hv, level_unitNormal_lift_negative D l hD u v hu hv⟩

end NoExoticSixSphere.CoorientedHypersurfaceNormal
