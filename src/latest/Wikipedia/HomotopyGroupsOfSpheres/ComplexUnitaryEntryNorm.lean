import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrixAlgebra

/-! # Entry bounds from the actual complex unitary matrix identities -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryEntryNorm

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem sum_normSq_column (U : unitary (Matrix N N ℂ)) (j : N) :
    (∑ i, Complex.normSq (U.val i j)) = 1 := by
  have h := congrArg (fun A : Matrix N N ℂ ↦ A j j) (Unitary.coe_star_mul_self U)
  have hc : (∑ i, (Complex.normSq (U.val i j) : ℂ)) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Matrix.one_apply_eq] using h
  simpa using congrArg Complex.re hc

theorem normSq_entry_le_one (U : unitary (Matrix N N ℂ)) (i j : N) :
    Complex.normSq (U.val i j) ≤ 1 := by
  have h := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset N)) ↦
    Complex.normSq_nonneg (U.val k j)) (Finset.mem_univ i)
  simpa only [sum_normSq_column] using h

theorem norm_entry_le_one (U : unitary (Matrix N N ℂ)) (i j : N) :
    ‖U.val i j‖ ≤ 1 := by
  have h := normSq_entry_le_one U i j
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (U.val i j)]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryEntryNorm
