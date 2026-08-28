import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointSeedMatrixRelations

/-!
# An actual midpoint preimage of the selected quaternionic column

The constructed unit vector has the required symmetric image. Applying
the inverse real rotation gives an input in the original five-sphere.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open QuaternionicBottMatrix

theorem matrix_conjugate : matrix vector =
    Matrix.diagonal (fun r ↦ -targetEigenvalues r) *
      QuaternionicSymmetricMatrices.conjugate (matrix vector) := by
  ext r q
  rw [Matrix.diagonal_mul]
  change matrix vector r q = -targetEigenvalues r * star (matrix vector r q)
  fin_cases r <;> fin_cases q
  · simpa [matrix, outer, crossMatrix, vector, targetEigenvalues,
      Matrix.cons_val_two, pow_two, mul_comm] using entry00
  · simpa [matrix, outer, crossMatrix, vector, targetEigenvalues,
      Matrix.cons_val_two, pow_two, mul_comm, sub_eq_add_neg] using entry01
  · simpa [matrix, outer, crossMatrix, vector, targetEigenvalues,
      Matrix.cons_val_two, pow_two, mul_comm] using entry02
  · simpa [matrix, outer, crossMatrix, vector, targetEigenvalues,
      Matrix.cons_val_two, pow_two, mul_comm] using entry10
  · simpa [matrix, outer, crossMatrix, vector, targetEigenvalues,
      Matrix.cons_val_two, pow_two, mul_comm] using entry11
  · simpa [matrix, outer, crossMatrix, vector, targetEigenvalues,
      Matrix.cons_val_two, pow_two, mul_comm, sub_eq_add_neg] using entry12
  · simpa [matrix, outer, crossMatrix, vector, targetEigenvalues,
      Matrix.cons_val_two, pow_two, mul_comm, sub_eq_add_neg] using entry20
  · simpa [matrix, outer, crossMatrix, vector, targetEigenvalues,
      Matrix.cons_val_two, pow_two, mul_comm] using entry21
  · simpa [matrix, outer, crossMatrix, vector, targetEigenvalues,
      Matrix.cons_val_two, pow_two, mul_comm] using entry22

theorem symmetricMap_rotatedInput : (symmetricMap rotatedInput).val.val =
    Matrix.diagonal (fun r ↦ -targetEigenvalues r) := by
  have hunit : matrix vector ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) := matrix_unitary rotatedInput
  have h : QuaternionicSymmetricMatrices.conjugate (matrix vector) *
      (matrix vector).transpose = 1 :=
    Unitary.coe_star_mul_self (Matrix.UnitaryGroup.transpose ⟨matrix vector, hunit⟩)
  rw [symmetricMap_val]
  change matrix vector * (matrix vector).transpose = _
  calc
    _ = (Matrix.diagonal (fun r ↦ -targetEigenvalues r) *
        QuaternionicSymmetricMatrices.conjugate (matrix vector)) * (matrix vector).transpose :=
      congrArg (fun A ↦ A * (matrix vector).transpose) matrix_conjugate
    _ = _ := by rw [mul_assoc, h, mul_one]

def input : UnitSphere := rotationSphere rotatedInput

theorem symmetricMap_input : (symmetricMap input).val.val =
    (-1 : ℂ) • targetMatrix targetAlpha targetBeta := by
  have hd : targetRotation * ((-1 : ℂ) • targetMatrix targetAlpha targetBeta) * targetRotation =
      Matrix.diagonal (fun r ↦ -targetEigenvalues r) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, targetRotation_targetMatrix]
    ext r q
    by_cases h : r = q
    · subst q
      simp [targetEigenvalues]
    · simp [h]
  rw [input, symmetricMap_rotationSphere, symmetricMap_rotatedInput, ← hd]
  simp only [mul_assoc, ← mul_assoc targetRotation targetRotation,
    targetRotation_mul_self, one_mul, mul_one]

theorem input_hits_target :
    firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap input) = targetColumn :=
  midpoint_target_of_matrix (symmetricMap input) (midpointPhases 0) symmetricMap_input

theorem rotatedInput_coordinate_ne_zero (r : Fin 3) : rotatedInput.val r ≠ 0 := by
  fin_cases r
  · exact rootA_ne_zero
  · exact rootB_ne_zero
  · exact rootC_ne_zero

theorem input_rotated_coordinate_ne_zero (r : Fin 3) : (rotationSphere input).val r ≠ 0 := by
  change (rotationSphere (rotationSphere rotatedInput)).val r ≠ 0
  rw [rotationSphere_involutive rotatedInput]
  exact rotatedInput_coordinate_ne_zero r

theorem midpointTargetPreimage_nonempty : midpointTargetPreimage.Nonempty :=
  ⟨input, input_hits_target⟩

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
