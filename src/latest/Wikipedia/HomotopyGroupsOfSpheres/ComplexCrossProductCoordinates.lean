import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

/-!
# Coordinate identities for preimages of the symmetric cross-product map

The diagonal identity below turns a prescribed diagonal symmetric matrix
into explicit phase equations on the five-sphere coordinates. No assertion
about the number or local degrees of its preimages is made here.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicSymmetricMatrices

theorem matrix_diagonal (z : Vector) (r : Fin 3) : matrix z r r = z r ^ 2 := by
  fin_cases r <;> simp [matrix, outer, crossMatrix, Matrix.cons_val_two, pow_two]

theorem matrix_mul_conjugate_vector (z : Vector) :
    matrix z *ᵥ (fun r ↦ star (z r)) = normPolynomial z • z := by
  funext r
  fin_cases r <;>
    simp [matrix, outer, crossMatrix, normPolynomial, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two] <;> ring

theorem matrix_transpose_mul_conjugate_vector (z : Vector) :
    (matrix z).transpose *ᵥ (fun r ↦ star (z r)) = normPolynomial z • z := by
  funext r
  fin_cases r <;>
    simp [matrix, outer, crossMatrix, normPolynomial, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two] <;> ring

theorem matrix_unit_mul_conjugate (z : UnitSphere) :
    matrix z.val *ᵥ (fun r ↦ star (z.val r)) = z.val := by
  rw [matrix_mul_conjugate_vector, normPolynomial_unit, one_smul]

theorem matrix_unit_transpose_mul_conjugate (z : UnitSphere) :
    (matrix z.val).transpose *ᵥ (fun r ↦ star (z.val r)) = z.val := by
  rw [matrix_transpose_mul_conjugate_vector, normPolynomial_unit, one_smul]

theorem matrix_eq_symmetric_mul_conjugate (z : UnitSphere) :
    matrix z.val = (symmetricMap z).val.val * conjugate (matrix z.val) := by
  have h : (matrix z.val).transpose * conjugate (matrix z.val) = 1 := by
    exact Unitary.coe_mul_star_self
      (Matrix.UnitaryGroup.transpose ⟨matrix z.val, matrix_unitary z⟩)
  rw [symmetricMap_val, mul_assoc, h, mul_one]

theorem diagonal_phase_equation (z : UnitSphere) (d : Fin 3 → ℂ)
    (hd : (symmetricMap z).val.val = Matrix.diagonal d) (r : Fin 3) :
    z.val r ^ 2 = d r * (star (z.val r)) ^ 2 := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A r r)
    (matrix_eq_symmetric_mul_conjugate z)
  rw [hd, Matrix.diagonal_mul, matrix_diagonal] at h
  change z.val r ^ 2 = d r * star (matrix z.val r r) at h
  simpa only [matrix_diagonal, star_pow] using h

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
