import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottRankReduction
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSectionSchur

/-!
# Coordinates of the explicit rank-two quaternionic map

The rank reduction is expressed by quaternionic rational formulas. The
reference family is diagonal, so its contribution to the final first column
can be computed separately.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices QuaternionicColumns QuaternionicScalars

local notation "ℍ" => Quaternion ℝ

def remainingRow (r : Fin 2) : Fin 3 := ![0, 2] r

theorem swap_mul_succ_row (A : SpGroup (Fin 3)) (r : Fin 2) (s : Fin 3) :
    (swap * A).val r.succ s = A.val (remainingRow r) s := by
  change (swapMatrix * A.val) r.succ s = _
  fin_cases r <;>
    simp [swapMatrix, Matrix.mul_apply, Fin.sum_univ_three, remainingRow, Matrix.cons_val_two]

theorem reduce_entry (A : ReductionDomain) (r s : Fin 2) :
    (reduce A).val r s = A.val.val (remainingRow r) s.succ -
      A.val.val (remainingRow r) 0 * (1 + A.val.val 1 0)⁻¹ * A.val.val 1 s.succ := by
  change ((sectionMap 0 (reductionColumn A))⁻¹ * (swap * A.val)).val r.succ s.succ = _
  have h := sectionMap_inv_mul_entry (swap * A.val) 0 (reductionColumn A).property
    r.succ s.succ (Fin.succ_ne_zero r) (Fin.succ_ne_zero s)
  simpa only [reductionColumn, swap_mul_succ_row, swap_mul_first_row] using h

theorem reduce_first_column_zero (A : ReductionDomain) :
    (reduce A).val 0 0 = A.val.val 0 1 -
      A.val.val 0 0 * (1 + A.val.val 1 0)⁻¹ * A.val.val 1 1 := by
  exact reduce_entry A 0 0

theorem reduce_first_column_one (A : ReductionDomain) :
    (reduce A).val 1 0 = A.val.val 2 1 -
      A.val.val 2 0 * (1 + A.val.val 1 0)⁻¹ * A.val.val 1 1 := by
  exact reduce_entry A 1 0

def scalarRotation (s t : ℝ) : ℍ :=
  Real.cos s • 1 + (Real.sin s * Real.cos t) • i + (Real.sin s * Real.sin t) • j

theorem rotation_identity_entry (s t : ℝ) (r q : Fin 3) :
    (rotation s t (identity : Space (Fin 3))).val r q =
      if r = q then scalarRotation s t else 0 := by
  rw [rotation_val, matrix_apply]
  by_cases h : r = q
  · subst q
    simp [identity, scalarRotation, QuaternionicComplexPlane.embed]
  · simp [identity, h, QuaternionicComplexPlane.embed]

theorem scalarRotation_unitary (s t : ℝ) : scalarRotation s t ∈ unitary ℍ := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℍ ↦ A 0 0)
    (Unitary.coe_star_mul_self (rotation s t (identity : Space (Fin 3))))
  have hleft : star (scalarRotation s t) * scalarRotation s t = 1 := by
    simpa [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three, rotation_identity_entry] using h
  exact ⟨hleft, mul_eq_one_comm.mp hleft⟩

theorem reducedRotation_identity_val (s t : ℝ) :
    (reducedRotation ((s, t), identity)).val =
      Matrix.diagonal ![-(scalarRotation s t * scalarRotation s t), scalarRotation s t] := by
  apply Matrix.ext
  intro r q
  change (reduce (rotationInDomain ((s, t), identity))).val r q = _
  rw [reduce_entry]
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  fin_cases r <;> fin_cases q <;>
    norm_num [rotationInDomain, rotation_identity_entry, remainingRow,
      Matrix.diagonal_apply, Matrix.cons_val_two, h02, h12, Ne.symm h02, Ne.symm h12]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
