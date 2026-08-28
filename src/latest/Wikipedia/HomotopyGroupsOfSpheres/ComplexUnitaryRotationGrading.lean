import Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryRotation

/-! # The exact involution conjugated by the unitary rotation -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryRotation

variable {N : Type*} [Fintype N] [DecidableEq N]

def grading : Matrix (N ⊕ N) (N ⊕ N) ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)

def latitudeMatrix (U : unitary (Matrix N N ℂ)) (t : ℝ) :
    Matrix (N ⊕ N) (N ⊕ N) ℂ :=
  Matrix.fromBlocks ((Real.cos t : ℂ) • 1) ((Real.sin t : ℂ) • U.val)
    ((Real.sin t : ℂ) • U.valᴴ) (-(Real.cos t : ℂ) • 1)

theorem latitudeMatrix_zero (U : unitary (Matrix N N ℂ)) : latitudeMatrix U 0 = grading := by
  simp [latitudeMatrix, grading]

theorem matrix_conjugate_grading (U : unitary (Matrix N N ℂ)) (t : ℝ) :
    matrix U t * grading * (matrix U t)ᴴ = latitudeMatrix U (2 * t) := by
  have h₁ : U.valᴴ * U.val = 1 := U.property.1
  have h₂ : U.val * U.valᴴ = 1 := U.property.2
  rw [matrix_star]
  simp only [matrix, grading, latitudeMatrix, Matrix.fromBlocks_multiply,
    Real.cos_neg, Real.sin_neg, Real.cos_two_mul', Real.sin_two_mul,
    Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, smul_mul_assoc, mul_smul_comm, smul_smul,
    one_mul, mul_one, mul_neg, neg_mul, mul_zero, zero_add, add_zero, h₁, h₂, neg_neg]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> module

theorem matrix_half_conjugate_grading (U : unitary (Matrix N N ℂ)) (t : ℝ) :
    matrix U (t / 2) * grading * (matrix U (t / 2))ᴴ = latitudeMatrix U t := by
  rw [matrix_conjugate_grading, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryRotation
