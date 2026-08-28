import Wikipedia.HomotopyGroupsOfSpheres.BalancedRealClassification

/-! # Fixed orthogonal changes of coordinates on the actual balanced orbit -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

variable {n : ℕ}

def conjugate (U : unitary (Matrix (Index n) (Index n) ℝ)) (J : Space n) : Space n :=
  ⟨U.val * J.val * U.val.transpose, by
    obtain ⟨V, hV⟩ := J.property
    exact ⟨U * V, by rw [orbitMatrix_mul, hV]⟩⟩

theorem conjugate_val (U : unitary (Matrix (Index n) (Index n) ℝ)) (J : Space n) :
    (conjugate U J).val = U.val * J.val * U.val.transpose := rfl

theorem conjugate_one (J : Space n) : conjugate 1 J = J := by
  apply Subtype.ext
  change (1 : Matrix (Index n) (Index n) ℝ) * J.val *
    (1 : Matrix (Index n) (Index n) ℝ).transpose = J.val
  simp

theorem conjugate_mul (U V : unitary (Matrix (Index n) (Index n) ℝ)) (J : Space n) :
    conjugate U (conjugate V J) = conjugate (U * V) J := by
  apply Subtype.ext
  change U.val * (V.val * J.val * V.val.transpose) * U.val.transpose =
    (U.val * V.val) * J.val * (U.val * V.val).transpose
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem conjugate_inv_cancel (U : unitary (Matrix (Index n) (Index n) ℝ)) (J : Space n) :
    conjugate U⁻¹ (conjugate U J) = J := by
  rw [conjugate_mul, inv_mul_cancel, conjugate_one]

theorem continuous_conjugate :
    Continuous (fun p : unitary (Matrix (Index n) (Index n) ℝ) × Space n ↦
      conjugate p.1 p.2) := by
  have hU : Continuous (fun p : unitary (Matrix (Index n) (Index n) ℝ) × Space n ↦ p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hJ : Continuous (fun p : unitary (Matrix (Index n) (Index n) ℝ) × Space n ↦ p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact ((hU.mul hJ).mul hU.matrix_transpose).subtype_mk _

theorem continuous_conjugate_const (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    Continuous (conjugate U) :=
  (continuous_conjugate (n := n)).comp
    ((continuous_const : Continuous (fun _ : Space n ↦ U)).prodMk continuous_id)

def conjugationHomeomorph (U : unitary (Matrix (Index n) (Index n) ℝ)) : Space n ≃ₜ Space n where
  toFun := conjugate U
  invFun := conjugate U⁻¹
  left_inv := conjugate_inv_cancel U
  right_inv J := by simpa only [inv_inv] using conjugate_inv_cancel U⁻¹ J
  continuous_toFun := continuous_conjugate_const U
  continuous_invFun := continuous_conjugate_const U⁻¹

theorem conjugate_standard (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    (conjugate U (standard n)).val = orbitMatrix n U := rfl

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
