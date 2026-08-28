import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSchurPivotDeficit
import Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryPairing

/-!
# Two complex-vector images determined by a target preimage

These identities retain the scalar sine factor, so no division by a
possibly zero coefficient or pivot coordinate is used.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices ComplexUnitaryEntryNorm

def pivotInputR (s t : ℝ) (B : Space (Fin 3)) : Fin 3 → ℂ :=
  ![star (pivotComplex s t B), 1, 0]

def pivotInputS (s t : ℝ) (B : Space (Fin 3)) : Fin 3 → ℂ :=
  ![star (pivotCoordinate s t B), 0, 0]

def pivotImageR (s t : ℝ) (B : Space (Fin 3)) : Fin 3 → ℂ :=
  ![targetAlpha * coordinate (referenceSquare s t) - angleComplex s t * pivotCoordinate s t B,
    -pivotCoordinate s t B, targetBeta * coordinate (referenceSquare s t)]

def pivotImageS (s t : ℝ) (B : Space (Fin 3)) : Fin 3 → ℂ :=
  ![angleComplex s t * pivotComplex s t B - targetAlpha * complexPart (referenceSquare s t),
    angleComplex s t + pivotComplex s t B, -targetBeta * complexPart (referenceSquare s t)]

theorem target_pivot_imageR (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    (angleReal s t : ℂ) • (B.val.val *ᵥ pivotInputR s t B) = pivotImageR s t B := by
  funext r
  fin_cases r
  · have he := target_pivot_coordinate_zero s t B h
    simp only [Complex.star_def] at he
    simp [pivotInputR, pivotImageR, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two]
    linear_combination he
  · simpa [pivotInputR, pivotImageR, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two, mul_add, mul_assoc] using pivot_coordinate_middle s t B
  · have he := target_pivot_coordinate_two s t B h
    simp only [Complex.star_def] at he
    simp [pivotInputR, pivotImageR, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two]
    linear_combination he

theorem target_pivot_imageS (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    (angleReal s t : ℂ) • (B.val.val *ᵥ pivotInputS s t B) = pivotImageS s t B := by
  funext r
  fin_cases r
  · have he := target_pivot_complex_zero s t B h
    simp only [Complex.star_def] at he
    simp [pivotInputS, pivotImageS, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two]
    linear_combination -he
  · have he := pivot_complex_middle s t B
    simp only [Complex.star_def] at he
    simp [pivotInputS, pivotImageS, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two]
    linear_combination -he
  · have he := target_pivot_complex_two s t B h
    simp only [Complex.star_def] at he
    simp [pivotInputS, pivotImageS, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two]
    linear_combination -he

theorem target_pivot_image_pairing (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    hermitianPairing (pivotImageR s t B) (pivotImageS s t B) =
      (angleReal s t : ℂ) ^ 2 * (pivotComplex s t B * star (pivotCoordinate s t B)) := by
  rw [← target_pivot_imageR s t B h, ← target_pivot_imageS s t B h,
    pairing_smul, pairing_mulVec]
  simp [hermitianPairing, dotProduct, pivotInputR, pivotInputS,
    Fin.sum_univ_three, Matrix.cons_val_two, pow_two]

theorem target_pivot_imageR_norm (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    ∑ r, Complex.normSq (pivotImageR s t B r) =
      angleReal s t ^ 2 * (Complex.normSq (pivotComplex s t B) + 1) := by
  have he : hermitianPairing (pivotImageR s t B) (pivotImageR s t B) =
      (angleReal s t : ℂ) ^ 2 * hermitianPairing (pivotInputR s t B) (pivotInputR s t B) := by
    rw [← target_pivot_imageR s t B h, pairing_smul, pairing_mulVec]
    simp [pow_two]
  rw [pairing_self, pairing_self] at he
  have hr := congrArg Complex.re he
  simpa [pivotInputR, Fin.sum_univ_three, Matrix.cons_val_two,
    Complex.star_def, Complex.normSq_conj, ← Complex.ofReal_pow] using hr

theorem target_pivot_imageS_norm (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    ∑ r, Complex.normSq (pivotImageS s t B r) =
      angleReal s t ^ 2 * Complex.normSq (pivotCoordinate s t B) := by
  have he : hermitianPairing (pivotImageS s t B) (pivotImageS s t B) =
      (angleReal s t : ℂ) ^ 2 * hermitianPairing (pivotInputS s t B) (pivotInputS s t B) := by
    rw [← target_pivot_imageS s t B h, pairing_smul, pairing_mulVec]
    simp [pow_two]
  rw [pairing_self, pairing_self] at he
  have hr := congrArg Complex.re he
  simpa [pivotInputS, Fin.sum_univ_three, Matrix.cons_val_two,
    Complex.star_def, Complex.normSq_conj, ← Complex.ofReal_pow] using hr

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
