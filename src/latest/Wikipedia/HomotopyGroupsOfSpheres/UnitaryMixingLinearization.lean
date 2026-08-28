import Wikipedia.HomotopyGroupsOfSpheres.UnitaryBlockConjugation
import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealification

/-! # The explicit linear matrix at the endpoint of unitary block mixing -/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.UnitaryBlockConjugation

open QuaternionicSymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

def linearization (A : Matrix N N ℂ) : Matrix (N ⊕ N) (N ⊕ N) ℂ :=
  Matrix.fromBlocks ((1 / 2 : ℂ) • (A + A.transpose))
    ((Complex.I / 2) • (A - A.transpose))
    ((Complex.I / 2) • (A.transpose - A)) ((1 / 2 : ℂ) • (A + A.transpose))

theorem unitaryProjection_conjugate_val (P A : unitary (Matrix N N ℂ)) :
    (unitaryProjection (P⁻¹ * A * P)).val.val =
      star P.val * (A.val * (P.val * P.val.transpose) * A.val.transpose) *
        (star P.val).transpose := by
  rw [unitaryProjection_val]
  change (star P.val * A.val * P.val) * (star P.val * A.val * P.val).transpose = _
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [mul_assoc]

attribute [local irreducible] UnitaryPairMixing.blockPath

theorem projection_block_negativeSwap
    (P : unitary (Matrix (N ⊕ N) (N ⊕ N) ℂ))
    (hP : P.val * P.val.transpose = Matrix.fromBlocks (0 : Matrix N N ℂ) (-1) (-1) 0)
    (A : unitary (Matrix N N ℂ)) :
    (unitaryProjection (P⁻¹ * UnitaryBlockDiagonal.inclusion A * P)).val.val =
      star P.val * Matrix.fromBlocks 0 (-A.val) (-A.val.transpose) 0 *
        (star P.val).transpose := by
  rw [unitaryProjection_conjugate_val P (UnitaryBlockDiagonal.inclusion A), hP,
    UnitaryBlockDiagonal.inclusion_val, UnitaryBlockDiagonal.matrix_negativeSwap_product]

theorem target_val_congruence (A : unitary (Matrix N N ℂ)) :
    (target A).val.val =
      star (UnitaryPairMixing.blockPath (N := N) 1).val *
        Matrix.fromBlocks 0 (-A.val) (-A.val.transpose) 0 *
          (star (UnitaryPairMixing.blockPath (N := N) 1).val).transpose := by
  exact projection_block_negativeSwap (UnitaryPairMixing.blockPath 1)
    UnitaryPairMixing.blockPath_one_mul_transpose A

theorem quarter_congruence_linearization (A : Matrix N N ℂ) :
    star (ScalarBlockMatrices.matrix (N := N) UnitaryPairMixing.quarter.val) *
      Matrix.fromBlocks 0 (-A) (-A.transpose) 0 *
        (star (ScalarBlockMatrices.matrix (N := N) UnitaryPairMixing.quarter.val)).transpose =
      linearization A := by
  change (ScalarBlockMatrices.matrix (N := N) UnitaryPairMixing.quarter.val)ᴴ * _ *
    ((ScalarBlockMatrices.matrix (N := N) UnitaryPairMixing.quarter.val)ᴴ).transpose = _
  rw [ScalarBlockMatrices.matrix_star, UnitaryPairMixing.quarter_val]
  simp only [ScalarBlockMatrices.matrix, Matrix.conjTranspose_apply,
    Matrix.fromBlocks_transpose,
    Matrix.transpose_smul, Matrix.transpose_one, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> apply Complex.ext <;>
    norm_num [linearization, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem target_val (A : unitary (Matrix N N ℂ)) :
    (target A).val.val = linearization A.val := by
  rw [target_val_congruence, UnitaryPairMixing.blockPath_one,
    ScalarBlockMatrices.unitaryMap_val, quarter_congruence_linearization]

theorem linearization_hermitian (x : ℝ) (H : Matrix N N ℂ) (hH : Hᴴ = H) :
    linearization ((x : ℂ) • 1 + Complex.I • H) =
      (x : ℂ) • 1 + Complex.I •
        RealUnitaryMatrices.complexification (ComplexMatrixRealification.matrix H) := by
  have hr (i j : N) : (H j i).re = (H i j).re := by
    simpa using congrArg (fun A : Matrix N N ℂ ↦ (A i j).re) hH
  have hi (i j : N) : (H j i).im = -(H i j).im := by
    have h := congrArg (fun A : Matrix N N ℂ ↦ (A i j).im) hH
    simpa using congrArg Neg.neg h
  have hd (i : N) : (H i i).im = 0 := by linarith [hi i i]
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> apply Complex.ext <;>
    by_cases hij : i = j <;>
    norm_num [linearization, RealUnitaryMatrices.complexification,
      ComplexMatrixRealification.matrix, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.one_apply, hij, eq_comm, hr i j, hi i j, hd,
      Sum.inl_ne_inr, Sum.inr_ne_inl,
      Complex.mul_re, Complex.mul_im] <;> ring

end Wikipedia.HomotopyGroupsOfSpheres.UnitaryBlockConjugation
