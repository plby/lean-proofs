import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSchurPivotEquality

/-! # Exact deficit in the Schur pivot norm bound -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices QuaternionicColumns

local notation "ℍ" => Quaternion ℝ

theorem normSq_rotation_diagonal (s t : ℝ) (B : Space (Fin 3)) (r : Fin 3) :
    Quaternion.normSq ((rotation s t B).val r r) =
      Complex.normSq (angleComplex s t) + angleReal s t ^ 2 * Complex.normSq (B.val.val r r) := by
  rw [normSq_complex_pair, complexPart_rotation, coordinate_rotation, if_pos rfl,
    map_mul, Complex.normSq_ofReal]
  ring

theorem schurPivot_normSq_deficit (s t : ℝ) (B : Space (Fin 3)) :
    (1 - Quaternion.normSq (schurPivot s t B)) * realDenominator s t B =
      angleReal s t ^ 2 *
        (2 * Complex.normSq (B.val.val 1 0) + Complex.normSq (B.val.val 2 1)) := by
  have hn := (eq_div_iff (ne_of_gt (realDenominator_pos s t B))).mp (schurPivot_normSq s t B)
  rw [normSq_rotation_diagonal] at hn
  have hc := ComplexUnitaryEntryNorm.sum_normSq_column B.val 1
  rw [Fin.sum_univ_three, symmetric_entry B 0 1] at hc
  have hc' := congrArg (fun x : ℝ ↦ angleReal s t ^ 2 * x) hc
  have ha := angle_norm s t
  change (1 - Quaternion.normSq (schurPivot s t B)) *
    (1 + angleReal s t ^ 2 * Complex.normSq (B.val.val 1 0)) = _
  change Quaternion.normSq (schurPivot s t B) *
    (1 + angleReal s t ^ 2 * Complex.normSq (B.val.val 1 0)) = _ at hn
  nlinarith [hc']

theorem target_angleReal_ne_zero (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) : angleReal s t ≠ 0 := by
  intro hc
  change Real.sin s * Real.sin t = 0 at hc
  have h20 : (rotation s t B).val 2 0 = 0 := by
    rw [rotation_val, matrix_apply]
    simp [hc]
  have h21 : (rotation s t B).val 2 1 = 0 := by
    rw [rotation_val, matrix_apply]
    simp [hc]
  have he := target_pivot_row s t B h 1
  change (rotation s t B).val 2 1 + (rotation s t B).val 2 0 * schurPivot s t B =
    (targetBeta : ℍ) * referenceSquare s t at he
  rw [h20, h21, zero_mul, zero_add] at he
  have hbeta : (targetBeta : ℍ) ≠ 0 := fun hz ↦ targetBeta_ne_zero (coeComplex_injective hz)
  have href : referenceSquare s t ≠ 0 := by
    intro hz
    have hu := (referenceSquare_unitary s t).1
    rw [hz, mul_zero] at hu
    exact zero_ne_one hu
  exact (mul_ne_zero hbeta href) he.symm

theorem schurPivot_unit_of_middle_entries_zero (s t : ℝ) (B : Space (Fin 3))
    (h10 : B.val.val 1 0 = 0) (h21 : B.val.val 2 1 = 0) :
    Quaternion.normSq (schurPivot s t B) = 1 := by
  have hd := schurPivot_normSq_deficit s t B
  rw [h10, h21, Complex.normSq_zero] at hd
  have hz : 1 - Quaternion.normSq (schurPivot s t B) = 0 :=
    (mul_eq_zero.mp (by simpa using hd)).resolve_right (ne_of_gt (realDenominator_pos s t B))
  linarith

theorem target_midpoint_of_middle_entries_zero (s t : ℝ) (B : Space (Fin 3))
    (hs : s ∈ Set.Icc 0 Real.pi) (ht : t ∈ Set.Icc 0 Real.pi)
    (h : firstColumnFormula s t B = targetColumn)
    (h10 : B.val.val 1 0 = 0) (h21 : B.val.val 2 1 = 0) :
    s = Real.pi / 2 ∧ t = Real.pi / 2 :=
  target_midpoint_of_pivot_unit s t B hs ht h (schurPivot_unit_of_middle_entries_zero s t B h10 h21)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
