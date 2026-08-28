import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductTrace

/-!
# Scalar equations for diagonal symmetric images

The diagonal entries, their phases, and the squared-coordinate sum give
linear equations for each squared coordinate. No preimage count is assumed.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

def crossVector (z : Vector) : Vector := crossMatrix (fun r ↦ star (z r)) *ᵥ z

theorem matrix_mul_vector (z : Vector) :
    matrix z *ᵥ z = squareSum z • z + crossVector z := by
  ext r
  fin_cases r <;>
    simp [matrix, outer, crossMatrix, squareSum, crossVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two] <;> ring

theorem symmetricMap_mul_conjugate (z : UnitSphere) :
    (symmetricMap z).val.val *ᵥ (fun r ↦ star (z.val r)) =
      squareSum z.val • z.val + crossVector z.val := by
  rw [symmetricMap_val, ← Matrix.mulVec_mulVec, matrix_unit_transpose_mul_conjugate,
    matrix_mul_vector]

theorem symmetric_matrix_diagonal (z : Vector) (r : Fin 3) :
    (matrix z * (matrix z).transpose) r r = star (squareSum z) +
      squareSum z * z r ^ 2 + 2 * z r * crossVector z r - star (z r) ^ 2 := by
  fin_cases r <;>
    simp [matrix, outer, crossMatrix, squareSum, crossVector, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two] <;> ring

theorem diagonal_square_norm_relation (z : UnitSphere) (d : Fin 3 → ℂ)
    (hd : (symmetricMap z).val.val = Matrix.diagonal d) (r : Fin 3) :
    d r = star (squareSum z.val) - squareSum z.val * z.val r ^ 2 +
      2 * d r * (Complex.normSq (z.val r) : ℂ) - star (z.val r) ^ 2 := by
  have hv := congrFun (symmetricMap_mul_conjugate z) r
  rw [hd, Matrix.mulVec_diagonal] at hv
  change d r * star (z.val r) = squareSum z.val * z.val r + crossVector z.val r at hv
  have hc : crossVector z.val r = d r * star (z.val r) - squareSum z.val * z.val r := by
    linear_combination -hv
  have he := symmetric_matrix_diagonal z.val r
  rw [← symmetricMap_val, hd, Matrix.diagonal_apply_eq, hc] at he
  rw [Complex.normSq_eq_conj_mul_self]
  change d r = star (squareSum z.val) - squareSum z.val * z.val r ^ 2 +
    2 * d r * (star (z.val r) * z.val r) - star (z.val r) ^ 2
  linear_combination he

theorem diagonal_entry_unitary (z : UnitSphere) (d : Fin 3 → ℂ)
    (hd : (symmetricMap z).val.val = Matrix.diagonal d) (r : Fin 3) :
    d r * star (d r) = 1 := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A r r)
    (Unitary.coe_mul_star_self (symmetricMap z).val)
  simpa [hd, Matrix.star_apply, Matrix.mul_apply, Matrix.diagonal_apply] using h

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
