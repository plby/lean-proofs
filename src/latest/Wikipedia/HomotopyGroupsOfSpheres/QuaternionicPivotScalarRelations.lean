import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPivotComplexImages

/-! # Scalar compatibility equations for the unrestricted preimage problem -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices ComplexUnitaryEntryNorm

theorem angle_unit_complex (s t : ℝ) :
    star (angleComplex s t) * angleComplex s t + (angleReal s t : ℂ) ^ 2 = 1 := by
  have h : ((Complex.normSq (angleComplex s t) + angleReal s t ^ 2 : ℝ) : ℂ) = 1 := by
    exact_mod_cast angle_norm s t
  simpa [Complex.normSq_eq_conj_mul_self, Complex.star_def] using h

theorem target_coefficients_unit :
    star targetAlpha * targetAlpha + star targetBeta * targetBeta = 1 := by
  rw [targetAlpha_star, targetBeta_star]
  calc
    _ = -(targetAlpha ^ 2 - targetBeta ^ 2) := by ring
    _ = 1 := by rw [target_polynomial]; norm_num

theorem referenceSquare_coordinate_star (s t : ℝ) :
    star (coordinate (referenceSquare s t)) = coordinate (referenceSquare s t) := by
  rw [referenceSquare_coordinate_real]
  exact Complex.conj_ofReal _

theorem referenceSquare_mixed_identity (s t : ℝ) :
    complexPart (referenceSquare s t) * star (angleComplex s t) +
      (angleReal s t : ℂ) * coordinate (referenceSquare s t) = -angleComplex s t := by
  rw [referenceSquare_complexPart, referenceSquare_coordinate]
  calc
    _ = -angleComplex s t *
        (star (angleComplex s t) * angleComplex s t + (angleReal s t : ℂ) ^ 2) := by ring
    _ = _ := by rw [angle_unit_complex, mul_one]

theorem referenceSquare_second_mixed_identity (s t : ℝ) :
    angleComplex s t * coordinate (referenceSquare s t) -
      (angleReal s t : ℂ) * complexPart (referenceSquare s t) = -(angleReal s t : ℂ) := by
  rw [referenceSquare_complexPart, referenceSquare_coordinate]
  calc
    _ = -(angleReal s t : ℂ) *
        (star (angleComplex s t) * angleComplex s t + (angleReal s t : ℂ) ^ 2) := by ring
    _ = _ := by rw [angle_unit_complex, mul_one]

theorem referenceSquare_complex_unit (s t : ℝ) :
    complexPart (referenceSquare s t) * star (complexPart (referenceSquare s t)) +
      coordinate (referenceSquare s t) ^ 2 = 1 := by
  rw [referenceSquare_complexPart, referenceSquare_coordinate]
  have hc : star (angleReal s t : ℂ) = (angleReal s t : ℂ) := by simp
  simp only [star_sub, star_pow, hc]
  calc
    _ = (star (angleComplex s t) * angleComplex s t + (angleReal s t : ℂ) ^ 2) ^ 2 := by ring
    _ = 1 := by rw [angle_unit_complex, one_pow]

theorem complex_pairing_elimination (α β w p q H L c : ℂ)
    (hL : star L = L) (hw : star w * w + c ^ 2 = 1)
    (hab : star α * α + star β * β = 1)
    (he : star (α * L - w * q) * (w * p - α * H) - star q * (w + p) -
      star (β * L) * (β * H) = c ^ 2 * (p * star q)) :
    2 * p * star q = star α * L * w * p - L * H + star w * star q * α * H - w * star q := by
  simp only [star_sub, star_mul, hL] at he
  linear_combination -he - (L * H) * hab - (p * star q) * hw

theorem target_pivot_cross (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    2 * pivotComplex s t B * star (pivotCoordinate s t B) =
      star targetAlpha * coordinate (referenceSquare s t) * angleComplex s t * pivotComplex s t B -
        coordinate (referenceSquare s t) * complexPart (referenceSquare s t) +
        star (angleComplex s t) * star (pivotCoordinate s t B) * targetAlpha *
          complexPart (referenceSquare s t) - angleComplex s t * star (pivotCoordinate s t B) := by
  apply complex_pairing_elimination targetAlpha targetBeta _ _ _ _ _ (angleReal s t : ℂ)
    (referenceSquare_coordinate_star s t) (angle_unit_complex s t) target_coefficients_unit
  simpa [hermitianPairing, dotProduct, pivotImageR, pivotImageS, Fin.sum_univ_three,
    Matrix.cons_val_two, sub_eq_add_neg, mul_assoc, Complex.star_def] using
      target_pivot_image_pairing s t B h

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
