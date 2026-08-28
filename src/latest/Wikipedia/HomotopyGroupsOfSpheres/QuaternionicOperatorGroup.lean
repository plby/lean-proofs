import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCommutant
import Wikipedia.NoExoticSixSphere.OrthogonalInverseDerivative

/-!
# The original symplectic group as a closed real orthogonal subgroup

The actual matrix group is homeomorphic to the subgroup of real orthogonal
operators commuting with quaternionic right multiplication. Both directions
are given by the checked real action and coefficient extraction.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.OrthogonalPaths

theorem isClosed_commutant (n : ℕ) :
    IsClosed (commutant n : Set (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) := by
  have he : (commutant n : Set (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) =
      ⋂ q, {T | T.comp (rightAction n q) = (rightAction n q).comp T} := by
    ext T
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_commutant_iff n T
  rw [he]
  exact isClosed_iInter (fun _ => isClosed_eq
    (continuous_id.clm_comp continuous_const) (continuous_const.clm_comp continuous_id))

theorem coefficients_unitary (n : ℕ) (a : OrthogonalOperators (4 * n + 4))
    (ha : a.val.val ∈ commutant n) :
    coefficients n a.val.val ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)) := by
  have hrepr := realAction_coefficients n a.val.val ha
  constructor
  · apply realAction_injective n
    rw [realAction_mul, realAction_star, hrepr, realAction_one]
    exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self a.val.val).mp a.property
  · apply realAction_injective n
    rw [realAction_mul, realAction_star, hrepr, realAction_one]
    rw [← NoExoticSixSphere.OrthogonalVelocity.inverse_eq_adjoint a, inverse_operator]
    apply ContinuousLinearMap.ext
    intro v
    exact a.val.property.self_apply_inverse v

/-- The matrix representation's actual subgroup in the real orthogonal group. -/
def symplecticSubgroup (n : ℕ) : Subgroup (OrthogonalOperators (4 * n + 4)) :=
  (orthogonalRepresentation n).range

theorem mem_symplecticSubgroup_iff (n : ℕ) (a : OrthogonalOperators (4 * n + 4)) :
    a ∈ symplecticSubgroup n ↔ a.val.val ∈ commutant n := by
  constructor
  · rintro ⟨A, rfl⟩
    exact realAction_mem_commutant n A.val
  · intro ha
    refine ⟨⟨coefficients n a.val.val, coefficients_unitary n a ha⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact realAction_coefficients n a.val.val ha

theorem isClosed_symplecticSubgroup (n : ℕ) :
    IsClosed (symplecticSubgroup n : Set (OrthogonalOperators (4 * n + 4))) := by
  have he : (symplecticSubgroup n : Set (OrthogonalOperators (4 * n + 4))) =
      {a | a.val.val ∈ commutant n} := by
    ext a
    exact mem_symplecticSubgroup_iff n a
  rw [he]
  exact (isClosed_commutant n).preimage
    (continuous_subtype_val.comp continuous_subtype_val)

/-- The usual matrix and real-operator models agree homeomorphically. -/
def symplecticHomeomorph (n : ℕ) : SpGroup (Fin (n + 1)) ≃ₜ symplecticSubgroup n where
  toFun A := ⟨orthogonalRepresentation n A, ⟨A, rfl⟩⟩
  invFun a := ⟨coefficients n a.val.val.val,
    coefficients_unitary n a.val ((mem_symplecticSubgroup_iff n a.val).mp a.property)⟩
  left_inv A := Subtype.ext (coefficients_realAction n A.val)
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact realAction_coefficients n a.val.val.val
      ((mem_symplecticSubgroup_iff n a.val).mp a.property)
  continuous_toFun := (continuous_orthogonalRepresentation n).subtype_mk _
  continuous_invFun := ((continuous_coefficients n).comp
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _

/-- The identification preserves the original matrix multiplication. -/
def symplecticMulEquiv (n : ℕ) : SpGroup (Fin (n + 1)) ≃* symplecticSubgroup n where
  toEquiv := (symplecticHomeomorph n).toEquiv
  map_mul' A B := Subtype.ext ((orthogonalRepresentation n).map_mul A B)

instance symplecticSubgroup_compactSpace (n : ℕ) : CompactSpace (symplecticSubgroup n) :=
  isCompact_iff_compactSpace.mp (isClosed_symplecticSubgroup n).isCompact

/-- Compactness concerns the original matrix-subspace topology. -/
instance spGroup_compactSpace (n : ℕ) : CompactSpace (SpGroup (Fin (n + 1))) :=
  (symplecticHomeomorph n).symm.compactSpace

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
