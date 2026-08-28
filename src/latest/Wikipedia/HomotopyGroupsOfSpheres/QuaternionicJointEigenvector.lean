import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicJointEigenvectorAlgebra
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSpectralSplitting
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureDirections
import Wikipedia.HomotopyGroupsOfSpheres.ComplexStructureRotationAlgebra

/-! # Actual joint unit eigenvectors for a quaternionic generator and a complex structure -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.SkewSpectralPlane
open ComplexStructures

variable {n : ℕ}

theorem exists_nonnegative_unit_i_eigenvector (K : SkewSpace n) :
    ∃ (α : ℝ) (v : Vector (4 * n + 4)), 0 ≤ α ∧ ‖v‖ = 1 ∧
      K.val v = α • rightAction n QuaternionicScalars.i v := by
  by_cases hzero : K.val = 0
  · let u := axisColumn (0 : Fin (n + 1))
    let v := quaternionCoordinates n (WithLp.toLp 2 u.val)
    refine ⟨0, v, le_rfl, ?_, ?_⟩
    · rw [(quaternionCoordinates n).norm_map]
      exact (pairing_self_eq_one_iff_norm u.val).mp u.property
    · rw [hzero, zero_apply, zero_smul]
  · obtain ⟨α, x, y, hα, hx, _, _, hKx, hKy⟩ :=
      exists_rotationPlane (toOrthogonalSkew n K) hzero
    have hx0 : x ≠ 0 := by
      intro he
      exact zero_ne_one (by simpa only [he, norm_zero] using hx)
    obtain ⟨v, hv, he⟩ := exists_unit_i_eigenvector_of_rotation K hx0 hKx hKy
    exact ⟨α, v, hα.le, hv, he⟩

theorem exists_joint_unit_eigenvector (J : Space n) (K : SkewSpace n)
    (hJK : J.val.val * K.val = -(K.val * J.val.val))
    {α : ℝ} {v : Vector (4 * n + 4)} (hv : v ≠ 0)
    (he : K.val v = α • rightAction n QuaternionicScalars.i v) :
    ∃ w : Vector (4 * n + 4), ‖w‖ = 1 ∧
      K.val w = α • rightAction n QuaternionicScalars.i w ∧
      J.val.val w = rightAction n QuaternionicScalars.j w := by
  have hKJ := ComplexStructureRotationAlgebra.reverse_anticommute J.val.val K.val hJK
  exact exists_unit_joint_quaternionic_eigenvector K.val.toLinearMap
    (rightAction n QuaternionicScalars.i).toLinearMap
    (rightAction n QuaternionicScalars.j).toLinearMap J.val.val.toLinearMap
    (fun x ↦ DFunLike.congr_fun (rightAction_i_square n) x)
    (fun x ↦ DFunLike.congr_fun (rightAction_j_square n) x)
    (square_apply J)
    (fun x ↦ DFunLike.congr_fun (rightAction_i_j_anticommute n) x)
    (fun x ↦ DFunLike.congr_fun
      ((mem_commutant_iff n J.val.val).mp J.val.property.2 QuaternionicScalars.i) x)
    (fun x ↦ DFunLike.congr_fun
      ((mem_commutant_iff n J.val.val).mp J.val.property.2 QuaternionicScalars.j) x)
    (fun x ↦ DFunLike.congr_fun
      ((mem_commutant_iff n K.val).mp K.property.2 QuaternionicScalars.i) x)
    (fun x ↦ DFunLike.congr_fun
      ((mem_commutant_iff n K.val).mp K.property.2 QuaternionicScalars.j) x)
    (fun x ↦ DFunLike.congr_fun hKJ x) hv he

theorem exists_nonnegative_joint_unit_eigenvector (J : Space n) (K : SkewSpace n)
    (hJK : J.val.val * K.val = -(K.val * J.val.val)) :
    ∃ (α : ℝ) (v : Vector (4 * n + 4)), 0 ≤ α ∧ ‖v‖ = 1 ∧
      K.val v = α • rightAction n QuaternionicScalars.i v ∧
      J.val.val v = rightAction n QuaternionicScalars.j v := by
  obtain ⟨α, v, hα, hv, he⟩ := exists_nonnegative_unit_i_eigenvector K
  have hv0 : v ≠ 0 := by
    intro hz
    exact zero_ne_one (by simpa only [hz, norm_zero] using hv)
  obtain ⟨w, hw, hKw, hJw⟩ := exists_joint_unit_eigenvector J K hJK hv0 he
  exact ⟨α, w, hα, hw, hKw, hJw⟩

theorem exists_fast_joint_unit_eigenvector (J : Space n) (K : SkewSpace n)
    (hJK : J.val.val * K.val = -(K.val * J.val.val))
    (hexp : (Exponential.exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hnot : gram (toOrthogonalSkew n K) ≠
      Real.pi ^ 2 • (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    ∃ (α : ℝ) (v : Vector (4 * n + 4)), 3 * Real.pi ≤ α ∧ ‖v‖ = 1 ∧
      K.val v = α • rightAction n QuaternionicScalars.i v ∧
      J.val.val v = rightAction n QuaternionicScalars.j v := by
  obtain ⟨α, v, hα, hv, he⟩ := exists_fast_i_eigenvector K hexp hnot
  have hv0 : v ≠ 0 := by
    intro hz
    exact zero_ne_one (by simpa only [hz, norm_zero] using hv)
  obtain ⟨w, hw, hKw, hJw⟩ := exists_joint_unit_eigenvector J K hJK hv0 he
  exact ⟨α, w, hα, hw, hKw, hJw⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
