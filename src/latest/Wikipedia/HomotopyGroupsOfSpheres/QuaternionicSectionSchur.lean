import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

/-!
# The quaternionic section correction is a Schur complement

Away from the distinguished row and column, correcting a unitary matrix by
the inverse of its column section has entries
`Aᵢₖ - Aᵢⱼ (1 + Aⱼⱼ)⁻¹ Aⱼₖ`. The order of quaternionic multiplication is
part of the statement.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicRankOne

local notation "ℍ" => Quaternion ℝ

variable {N : Type*} [Fintype N] [DecidableEq N]

omit [Fintype N] in
theorem axisReflectionMatrix_star (j : N) :
    star (axisReflectionMatrix j) = axisReflectionMatrix j := by
  apply Matrix.ext
  intro r s
  by_cases hrs : r = s
  · subst s
    simp only [Matrix.star_apply, axisReflectionMatrix, Matrix.diagonal_apply_eq]
    split_ifs <;> simp
  · simp only [Matrix.star_apply, axisReflectionMatrix,
      Matrix.diagonal_apply_ne _ hrs, Matrix.diagonal_apply_ne _ (Ne.symm hrs), star_zero]

theorem sectionMap_inverse_matrix (j : N) (v : columnChart j) :
    ((sectionMap j v)⁻¹).val = axisReflectionMatrix j *
      (1 - rankOne (v.val.val + axis j) (1 + v.val.val j)⁻¹) := by
  change star (columnReflectionMatrix v.val.val j * axisReflectionMatrix j) = _
  rw [star_mul, axisReflectionMatrix_star, columnReflectionMatrix,
    star_sub, star_one, star_rankOne, star_inv₀, star_add, star_one, star_star]

omit [DecidableEq N] in
theorem rankOne_mul_entry (u : N → ℍ) (c : ℍ) (A : Matrix N N ℍ) (i k : N) :
    (rankOne u c * A) i k = u i * c * (∑ l, star (u l) * A l k) := by
  simp only [Matrix.mul_apply, rankOne, Finset.mul_sum, mul_assoc]

theorem column_plus_axis_pairing (A : SpGroup N) (j k : N) (hjk : j ≠ k) :
    (∑ l, star (A.val l j + axis j l) * A.val l k) = A.val j k := by
  have ho : (∑ l, star (A.val l j) * A.val l k) = 0 := by
    have he := congrArg (fun M : Matrix N N ℍ ↦ M j k) (Unitary.coe_star_mul_self A)
    simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_ne hjk] using he
  simp only [star_add, add_mul, Finset.sum_add_distrib, ho, zero_add]
  simp [axis, Pi.single_apply, apply_ite]

theorem sectionMap_inv_mul_entry (A : SpGroup N) (j : N) (ha : A.val j j ≠ -1)
    (i k : N) (hij : i ≠ j) (hkj : k ≠ j) :
    ((sectionMap j ⟨column j A, ha⟩)⁻¹ * A).val i k =
      A.val i k - A.val i j * (1 + A.val j j)⁻¹ * A.val j k := by
  change (((sectionMap j ⟨column j A, ha⟩)⁻¹).val * A.val) i k = _
  rw [sectionMap_inverse_matrix, mul_assoc]
  rw [axisReflectionMatrix, Matrix.diagonal_mul, if_neg hij, one_mul,
    sub_mul, one_mul, Matrix.sub_apply,
    rankOne_mul_entry]
  change A.val i k - (A.val i j + axis j i) * (1 + A.val j j)⁻¹ *
      (∑ l, star (A.val l j + axis j l) * A.val l k) = _
  rw [axis_of_ne i j hij, add_zero, column_plus_axis_pairing A j k hkj.symm]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
