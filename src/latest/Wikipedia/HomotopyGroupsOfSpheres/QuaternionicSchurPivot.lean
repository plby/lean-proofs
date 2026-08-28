import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointTarget
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicUnitaryEntryNorm

/-!
# The Schur pivot on the full Bott parameter space

The auxiliary quaternion rewrites the first-column equation as a matrix
equation. Its squared norm is at most one throughout the parameter space.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices QuaternionicColumns

local notation "ℍ" => Quaternion ℝ

def schurPivot (s t : ℝ) (B : Space (Fin 3)) : ℍ :=
  -((1 + (rotation s t B).val 1 0)⁻¹ * (rotation s t B).val 1 1)

theorem rotation_pivot_denominator_ne_zero (s t : ℝ) (B : Space (Fin 3)) :
    1 + (rotation s t B).val 1 0 ≠ 0 := by
  intro h
  have hr := congrArg (fun q : ℍ ↦ q.re) h
  have hzero := rotation_offDiagonal_re s t B 1 0 (by decide)
  change (1 : ℝ) + ((rotation s t B).val 1 0).re = 0 at hr
  rw [hzero] at hr
  norm_num at hr

theorem schurPivot_equation (s t : ℝ) (B : Space (Fin 3)) :
    (1 + (rotation s t B).val 1 0) * schurPivot s t B = -(rotation s t B).val 1 1 := by
  rw [schurPivot, mul_neg, ← mul_assoc,
    mul_inv_cancel₀ (rotation_pivot_denominator_ne_zero s t B), one_mul]

theorem schurPivot_middle_row (s t : ℝ) (B : Space (Fin 3)) :
    (rotation s t B).val 1 0 * schurPivot s t B + (rotation s t B).val 1 1 =
      -schurPivot s t B := by
  have h := schurPivot_equation s t B
  rw [add_mul, one_mul] at h
  apply eq_neg_iff_add_eq_zero.mpr
  calc
    _ = (schurPivot s t B + (rotation s t B).val 1 0 * schurPivot s t B) +
        (rotation s t B).val 1 1 := by abel
    _ = 0 := by rw [h]; simp

theorem schurPivot_normSq (s t : ℝ) (B : Space (Fin 3)) :
    Quaternion.normSq (schurPivot s t B) =
      Quaternion.normSq ((rotation s t B).val 1 1) / realDenominator s t B := by
  rw [schurPivot, Quaternion.normSq_neg, map_mul, Quaternion.normSq_inv,
    normSq_one_add_of_re_zero _ (rotation_offDiagonal_re s t B 1 0 (by decide)),
    rotation_one_zero, Quaternion.normSq_smul, normSq_embed]
  rw [div_eq_mul_inv, mul_comm]
  rfl

theorem schurPivot_normSq_le_one (s t : ℝ) (B : Space (Fin 3)) :
    Quaternion.normSq (schurPivot s t B) ≤ 1 := by
  rw [schurPivot_normSq, div_le_one (realDenominator_pos s t B)]
  exact (normSq_entry_le_one (rotation s t B) 1 1).trans (realDenominator_ge_one s t B)

def referenceSquare (s t : ℝ) : ℍ := -(scalarRotation s t * scalarRotation s t)

theorem referenceSquare_unitary (s t : ℝ) : referenceSquare s t ∈ unitary ℍ := by
  have h := scalarRotation_unitary s t
  have hmul := (unitary ℍ).mul_mem h h
  constructor
  · simpa only [referenceSquare, star_neg, neg_mul_neg] using hmul.1
  · simpa only [referenceSquare, star_neg, neg_mul_neg] using hmul.2

theorem firstColumnFormula_pivot (s t : ℝ) (B : Space (Fin 3)) (r : Fin 2) :
    firstColumnFormula s t B r =
      ((rotation s t B).val (remainingRow r) 1 +
        (rotation s t B).val (remainingRow r) 0 * schurPivot s t B) *
          star (referenceSquare s t) := by
  simp only [firstColumnFormula, schurPivot, referenceSquare, rotation_val]
  rw [mul_neg, ← mul_assoc, ← sub_eq_add_neg]

theorem target_pivot_row (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) (r : Fin 2) :
    (rotation s t B).val (remainingRow r) 1 +
      (rotation s t B).val (remainingRow r) 0 * schurPivot s t B =
        targetColumn r * referenceSquare s t := by
  have he := congrArg (fun f : Fin 2 → ℍ ↦ f r * referenceSquare s t) h
  rw [firstColumnFormula_pivot, mul_assoc, (referenceSquare_unitary s t).1, mul_one] at he
  exact he

theorem target_pivot_matrix_equation (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    (rotation s t B).val *ᵥ ![schurPivot s t B, 1, 0] =
      ![(targetAlpha : ℍ) * referenceSquare s t, -schurPivot s t B,
        (targetBeta : ℍ) * referenceSquare s t] := by
  funext r
  fin_cases r
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, remainingRow,
      targetColumn, Matrix.cons_val_two, add_comm] using target_pivot_row s t B h 0
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two] using
      schurPivot_middle_row s t B
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, remainingRow,
      targetColumn, Matrix.cons_val_two, add_comm] using target_pivot_row s t B h 1

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
