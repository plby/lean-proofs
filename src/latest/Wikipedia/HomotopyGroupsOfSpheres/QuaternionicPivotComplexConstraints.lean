import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottComplexCoordinates

/-! # Necessary complex equations for every preimage of the selected column -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices

def pivotComplex (s t : ℝ) (B : Space (Fin 3)) : ℂ := complexPart (schurPivot s t B)
def pivotCoordinate (s t : ℝ) (B : Space (Fin 3)) : ℂ := coordinate (schurPivot s t B)

theorem pivot_parts_bound (s t : ℝ) (B : Space (Fin 3)) :
    Complex.normSq (pivotComplex s t B) + Complex.normSq (pivotCoordinate s t B) ≤ 1 := by
  rw [pivotComplex, pivotCoordinate, ← normSq_complex_pair]
  exact schurPivot_normSq_le_one s t B

theorem target_pivot_complex_zero (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    angleComplex s t * pivotComplex s t B -
      (angleReal s t : ℂ) * B.val.val 0 0 * star (pivotCoordinate s t B) =
        targetAlpha * complexPart (referenceSquare s t) := by
  have he := congrArg complexPart (target_pivot_row s t B h 0)
  simpa [complexPart_add, complexPart_mul, complexPart_rotation, coordinate_rotation,
    complexPart_coeComplex, coordinate_coeComplex, pivotComplex, pivotCoordinate,
    targetColumn, remainingRow] using he

theorem target_pivot_coordinate_zero (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    (angleReal s t : ℂ) * B.val.val 0 1 + angleComplex s t * pivotCoordinate s t B +
      (angleReal s t : ℂ) * B.val.val 0 0 * star (pivotComplex s t B) =
        targetAlpha * coordinate (referenceSquare s t) := by
  have he := congrArg coordinate (target_pivot_row s t B h 0)
  simpa [coordinate_add, coordinate_mul, complexPart_rotation, coordinate_rotation,
    complexPart_coeComplex, coordinate_coeComplex, pivotComplex, pivotCoordinate,
    targetColumn, remainingRow, add_assoc] using he

theorem pivot_complex_middle (s t : ℝ) (B : Space (Fin 3)) :
    angleComplex s t - (angleReal s t : ℂ) * B.val.val 1 0 * star (pivotCoordinate s t B) =
      -pivotComplex s t B := by
  have he := congrArg complexPart (schurPivot_middle_row s t B)
  simpa [complexPart_add, complexPart_mul, complexPart_rotation, coordinate_rotation,
    complexPart_neg, pivotComplex, pivotCoordinate, sub_eq_add_neg, add_comm] using he

theorem pivot_coordinate_middle (s t : ℝ) (B : Space (Fin 3)) :
    (angleReal s t : ℂ) * B.val.val 1 0 * star (pivotComplex s t B) +
      (angleReal s t : ℂ) * B.val.val 1 1 = -pivotCoordinate s t B := by
  have he := congrArg coordinate (schurPivot_middle_row s t B)
  simpa [coordinate_add, coordinate_mul, complexPart_rotation, coordinate_rotation,
    coordinate_neg, pivotComplex, pivotCoordinate] using he

theorem target_pivot_complex_two (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    -((angleReal s t : ℂ) * B.val.val 2 0 * star (pivotCoordinate s t B)) =
      targetBeta * complexPart (referenceSquare s t) := by
  have he := congrArg complexPart (target_pivot_row s t B h 1)
  simpa [complexPart_add, complexPart_mul, complexPart_rotation, coordinate_rotation,
    complexPart_coeComplex, coordinate_coeComplex, pivotComplex, pivotCoordinate,
    targetColumn, remainingRow, Matrix.cons_val_two] using he

theorem target_pivot_coordinate_two (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    (angleReal s t : ℂ) * B.val.val 2 1 +
      (angleReal s t : ℂ) * B.val.val 2 0 * star (pivotComplex s t B) =
        targetBeta * coordinate (referenceSquare s t) := by
  have he := congrArg coordinate (target_pivot_row s t B h 1)
  simpa [coordinate_add, coordinate_mul, complexPart_rotation, coordinate_rotation,
    complexPart_coeComplex, coordinate_coeComplex, pivotComplex, pivotCoordinate,
    targetColumn, remainingRow, Matrix.cons_val_two] using he

theorem target_pivot_symmetry (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    angleComplex s t * (1 + ((Quaternion.normSq (schurPivot s t B) : ℝ) : ℂ)) +
      pivotComplex s t B =
      targetAlpha * (complexPart (referenceSquare s t) * star (pivotComplex s t B) +
        coordinate (referenceSquare s t) * star (pivotCoordinate s t B)) := by
  have h0 := target_pivot_complex_zero s t B h
  have h1 := target_pivot_coordinate_zero s t B h
  have hm := pivot_complex_middle s t B
  rw [symmetric_entry B 0 1] at h1
  rw [normSq_complex_pair, Complex.ofReal_add]
  change angleComplex s t * (1 + ((Complex.normSq (pivotComplex s t B) : ℂ) +
    (Complex.normSq (pivotCoordinate s t B) : ℂ))) + pivotComplex s t B = _
  simp only [Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def] at h0 h1 hm ⊢
  linear_combination (starRingEnd ℂ) (pivotComplex s t B) * h0 +
    (starRingEnd ℂ) (pivotCoordinate s t B) * h1 + hm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
