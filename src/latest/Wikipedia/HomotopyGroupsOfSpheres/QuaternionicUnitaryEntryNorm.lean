import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

/-! # Squared-norm bounds for entries of quaternionic unitary matrices -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

local notation "ℍ" => Quaternion ℝ

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem sum_normSq_column (A : SpGroup N) (j : N) :
    ∑ r, Quaternion.normSq (A.val r j) = 1 := by
  have h := congrArg (fun M : Matrix N N ℍ ↦ M j j) (Unitary.coe_star_mul_self A)
  simp only [Matrix.mul_apply, Matrix.star_apply, Quaternion.star_mul_self,
    Matrix.one_apply_eq] at h
  have hs := map_sum (algebraMap ℝ ℍ) (fun r ↦ Quaternion.normSq (A.val r j)) Finset.univ
  have h' : (∑ r, (algebraMap ℝ ℍ) (Quaternion.normSq (A.val r j))) = 1 := h
  rw [← hs] at h'
  have hr := congrArg (fun q : ℍ ↦ q.re) h'
  exact hr

theorem normSq_entry_le_one (A : SpGroup N) (r j : N) : Quaternion.normSq (A.val r j) ≤ 1 := by
  rw [← sum_normSq_column A j]
  exact Finset.single_le_sum
    (fun i _ ↦ (show 0 ≤ Quaternion.normSq (A.val i j) from Quaternion.normSq_nonneg))
    (Finset.mem_univ r)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
