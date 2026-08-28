import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification

/-! # Actual real orthogonal matrices from complex unitary matrices -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem matrix_unitary (U : unitary (Matrix N N ℂ)) :
    matrix U.val ∈ unitary (Matrix (N ⊕ N) (N ⊕ N) ℝ) := by
  constructor
  · rw [RealUnitaryMatrices.star_eq_transpose, ← matrix_star, ← matrix_mul]
    exact (congrArg matrix U.property.1).trans matrix_one
  · rw [RealUnitaryMatrices.star_eq_transpose, ← matrix_star, ← matrix_mul]
    exact (congrArg matrix U.property.2).trans matrix_one

def unitaryMap :
    unitary (Matrix N N ℂ) →* unitary (Matrix (N ⊕ N) (N ⊕ N) ℝ) where
  toFun U := ⟨matrix U.val, matrix_unitary U⟩
  map_one' := Subtype.ext matrix_one
  map_mul' U V := Subtype.ext (matrix_mul U.val V.val)

theorem unitaryMap_val (U : unitary (Matrix N N ℂ)) : (unitaryMap U).val = matrix U.val := rfl

theorem continuous_unitaryMap :
    Continuous (unitaryMap : unitary (Matrix N N ℂ) →
      unitary (Matrix (N ⊕ N) (N ⊕ N) ℝ)) :=
  (continuous_matrix.comp continuous_subtype_val).subtype_mk _

theorem matrix_conjugate (U : unitary (Matrix N N ℂ)) (A : Matrix N N ℂ) :
    matrix (U.val * A * U.valᴴ) = (unitaryMap U).val * matrix A * (unitaryMap U).val.transpose := by
  rw [matrix_mul, matrix_mul, matrix_star]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification
