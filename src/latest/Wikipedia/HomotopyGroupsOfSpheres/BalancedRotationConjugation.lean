import Wikipedia.HomotopyGroupsOfSpheres.BalancedRealConjugation
import Wikipedia.HomotopyGroupsOfSpheres.BalancedRotationPaths

/-! # Orthogonal normalization of the actual balanced rotation family -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open QuaternionicSymmetricMatrices RealUnitaryMatrices

variable {n : ℕ}

theorem continuous_symmetricCongruence_const
    (U : unitary (Matrix (Index n) (Index n) ℂ)) :
    Continuous (congruence U) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun B : QuaternionicSymmetricMatrices.Space (Index n) ↦
    U.val * B.val.val * U.val.transpose)
  have hB : Continuous (fun B : QuaternionicSymmetricMatrices.Space (Index n) ↦ B.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact (continuous_const.mul hB).mul continuous_const

def symmetricCongruenceHomeomorph (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    QuaternionicSymmetricMatrices.Space (Index n) ≃ₜ
      QuaternionicSymmetricMatrices.Space (Index n) where
  toFun := congruence (toComplex U)
  invFun := congruence (toComplex U)⁻¹
  left_inv := congruence_inv_cancel (toComplex U)
  right_inv B := by simpa only [inv_inv] using congruence_inv_cancel (toComplex U)⁻¹ B
  continuous_toFun := continuous_symmetricCongruence_const (toComplex U)
  continuous_invFun := continuous_symmetricCongruence_const (toComplex U)⁻¹

theorem symmetricCongruenceHomeomorph_identity
    (U : unitary (Matrix (Index n) (Index n) ℝ)) :
    symmetricCongruenceHomeomorph U identity = identity := by
  apply Subtype.ext
  apply Subtype.ext
  change (toComplex U).val * 1 * (toComplex U).val.transpose = 1
  rw [mul_one]
  exact toComplex_mul_transpose U

theorem symmetricCongruenceHomeomorph_rotation
    (U : unitary (Matrix (Index n) (Index n) ℝ)) (J : Space n) (θ : ℝ) :
    symmetricCongruenceHomeomorph U (rotation J θ).val = (rotation (conjugate U J) θ).val := by
  have hU : complexification U.val * (complexification U.val).transpose = 1 :=
    toComplex_mul_transpose U
  apply Subtype.ext
  apply Subtype.ext
  change complexification U.val * rotationMatrix n θ J.val *
    (complexification U.val).transpose = rotationMatrix n θ (U.val * J.val * U.val.transpose)
  rw [rotationMatrix, rotationMatrix, map_mul, map_mul, complexification_transpose]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one]
  rw [hU]

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
