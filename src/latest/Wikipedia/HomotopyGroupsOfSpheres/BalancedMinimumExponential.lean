import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryAntipodalMinimum
import Wikipedia.HomotopyGroupsOfSpheres.BalancedRotationPaths

/-!
# The minimum generators exponentiate to the original balanced rotations

This identifies the matrix exponential with the continuous rotation
formula already used for the based homotopy map.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open ImaginarySymmetricMatrices RealUnitaryMatrices

theorem exp_imaginary_standard (n : ℕ) (θ : ℝ) :
    NormedSpace.exp (imaginary (θ • standardMatrix n)) = diagonalPhase n θ := by
  rw [standardMatrix, ← Matrix.diagonal_smul, exp_imaginary_diagonal, diagonalPhase]
  apply congrArg Matrix.diagonal
  funext a
  cases a <;> simp [sign, phase, Circle.coe_exp, mul_comm, Complex.exp_neg]

theorem exp_imaginary_involution {n : ℕ} (J : Space n) (θ : ℝ) :
    NormedSpace.exp (imaginary (θ • J.val)) = rotationMatrix n θ J.val := by
  obtain ⟨U, hU⟩ := J.property
  rw [← hU, rotationMatrix_orbit]
  have hs : θ • orbitMatrix n U =
      RealMatrixSquareNorm.conjugate U (θ • standardMatrix n) :=
    ((RealMatrixSquareNorm.conjugate U).map_smul θ (standardMatrix n)).symm
  rw [hs, exp_imaginary_conjugate, exp_imaginary_standard]
  rfl

def direction {n : ℕ} (J : Space n) : RealSymmetricMixing.DirectionSpace (Index n) :=
  ⟨J.val, transpose_eq J, trace_eq_zero J⟩

def minimumGenerator {n : ℕ} (J : Space n) : RealSymmetricMixing.DirectionSpace (Index n) :=
  Real.pi • direction J

theorem minimumGenerator_injective (n : ℕ) :
    Function.Injective
      (minimumGenerator : Space n → RealSymmetricMixing.DirectionSpace (Index n)) := by
  intro J K h
  have he : Real.pi • J.val = Real.pi • K.val := congrArg Subtype.val h
  exact Subtype.ext ((smul_right_injective _ Real.pi_ne_zero) he)

theorem exponential_direction {n : ℕ} (J : Space n) (θ : ℝ) :
    QuaternionicSymmetricMatrices.exponential (θ • direction J) = rotation J θ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact exp_imaginary_involution J θ

theorem exponentialCurve_minimumGenerator {n : ℕ} (J : Space n) (t : ℝ) :
    QuaternionicSymmetricMatrices.exponentialCurve (minimumGenerator J) t =
      rotation J (t * Real.pi) := by
  rw [QuaternionicSymmetricMatrices.exponentialCurve, minimumGenerator, smul_smul,
    exponential_direction]

theorem minimumGenerator_antipodal {n : ℕ} (J : Space n) :
    NormedSpace.exp (imaginary (minimumGenerator J).val) = -1 := by
  change NormedSpace.exp (imaginary (Real.pi • J.val)) = -1
  rw [exp_imaginary_involution]
  have h := congrArg (fun B : QuaternionicSymmetricMatrices.SpecialSpace (Index n) ↦ B.val.val.val)
    (rotation_pi J)
  exact h.trans (antipode_matrix n)

theorem minimumGenerator_squareNorm {n : ℕ} (J : Space n) :
    RealMatrixSquareNorm.squareNorm (minimumGenerator J).val = (2 * n : ℝ) * Real.pi ^ 2 := by
  apply (antipodal_squareNorm_eq_iff_balanced n (minimumGenerator J).val
    (minimumGenerator J).property.1 (minimumGenerator J).property.2
    (minimumGenerator_antipodal J)).mpr
  exact ⟨J, rfl⟩

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
