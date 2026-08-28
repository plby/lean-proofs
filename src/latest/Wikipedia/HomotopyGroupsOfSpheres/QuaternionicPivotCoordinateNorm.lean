import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPivotCofactorConstraints

/-! # Exact complex-component norms of a target preimage's Schur pivot -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices

theorem targetBeta_normSq : Complex.normSq targetBeta = 3 / 4 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [targetBeta, Complex.normSq_ofReal]
  nlinarith

theorem pivot_middle_entry_norm (s t : ℝ) (B : Space (Fin 3)) :
    Complex.normSq (angleComplex s t + pivotComplex s t B) =
      angleReal s t ^ 2 * Complex.normSq (B.val.val 1 0) *
        Complex.normSq (pivotCoordinate s t B) := by
  have he : angleComplex s t + pivotComplex s t B =
      (angleReal s t : ℂ) * B.val.val 1 0 * star (pivotCoordinate s t B) := by
    linear_combination pivot_complex_middle s t B
  rw [he, map_mul, map_mul, Complex.star_def, Complex.normSq_conj, Complex.normSq_ofReal]
  ring

theorem target_pivot_reference_entry_norm (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    angleReal s t ^ 2 * Complex.normSq (pivotCoordinate s t B) *
        Complex.normSq (B.val.val 2 1) =
      (3 / 4) * Complex.normSq (angleComplex s t) * Quaternion.normSq (schurPivot s t B) := by
  have he := congrArg Complex.normSq (target_pivot_referenceR_entry s t B h)
  simp only [map_mul, Complex.star_def, Complex.normSq_conj, Complex.normSq_ofReal,
    targetBeta_normSq, target_pivot_referenceR_norm s t B h] at he
  linear_combination he

theorem target_pivot_deficit_reduced (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    (1 - Quaternion.normSq (schurPivot s t B)) *
        (Complex.normSq (pivotCoordinate s t B) +
          Complex.normSq (angleComplex s t + pivotComplex s t B)) =
      2 * Complex.normSq (angleComplex s t + pivotComplex s t B) +
        (3 / 4) * Complex.normSq (angleComplex s t) * Quaternion.normSq (schurPivot s t B) := by
  have hd := schurPivot_normSq_deficit s t B
  have hm := pivot_middle_entry_norm s t B
  have hr := target_pivot_reference_entry_norm s t B h
  change (1 - Quaternion.normSq (schurPivot s t B)) *
    (1 + angleReal s t ^ 2 * Complex.normSq (B.val.val 1 0)) = _ at hd
  linear_combination Complex.normSq (pivotCoordinate s t B) * hd + hr -
    (1 + Quaternion.normSq (schurPivot s t B)) * hm

theorem normSq_affine_identity (w p : ℂ) (n : ℝ) :
    Complex.normSq (p + (1 + (n : ℂ)) * w) =
      (1 + n) * Complex.normSq (w + p) - n * Complex.normSq p +
        n * (1 + n) * Complex.normSq w := by
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

theorem target_pivotCoordinate_normSq (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    Complex.normSq (pivotCoordinate s t B) =
      Quaternion.normSq (schurPivot s t B) ^ 2 * angleReal s t ^ 2 := by
  have hd := target_pivot_deficit_reduced s t B h
  have hn := target_pivot_norm_constraint s t B h
  rw [normSq_affine_identity] at hn
  have hp : Complex.normSq (pivotComplex s t B) + Complex.normSq (pivotCoordinate s t B) =
      Quaternion.normSq (schurPivot s t B) := (normSq_complex_pair _).symm
  have hu := angle_norm s t
  linear_combination hd + hn / 4 + Quaternion.normSq (schurPivot s t B) * hp -
    Quaternion.normSq (schurPivot s t B) ^ 2 * hu

theorem target_pivotComplex_normSq (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    Complex.normSq (pivotComplex s t B) =
      Quaternion.normSq (schurPivot s t B) * (1 - Quaternion.normSq (schurPivot s t B)) +
        Quaternion.normSq (schurPivot s t B) ^ 2 * Complex.normSq (angleComplex s t) := by
  have hp : Complex.normSq (pivotComplex s t B) + Complex.normSq (pivotCoordinate s t B) =
      Quaternion.normSq (schurPivot s t B) := (normSq_complex_pair _).symm
  have hq := target_pivotCoordinate_normSq s t B h
  have hu := angle_norm s t
  linear_combination hp - hq - Quaternion.normSq (schurPivot s t B) ^ 2 * hu

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
