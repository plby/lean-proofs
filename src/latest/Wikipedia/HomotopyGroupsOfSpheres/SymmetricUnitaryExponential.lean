import Wikipedia.HomotopyGroupsOfSpheres.ImaginarySymmetricMatrices
import Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricInvolutionSpectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Exponential curves in the symmetric determinant-one unitary space

For a real symmetric matrix `A`, the determinant of `exp(iA)` is
`exp(i trace(A))`. The proof uses orthogonal diagonalization, so no
general determinant-of-exponential theorem is required. Trace-zero
directions therefore give actual curves in the previously defined space.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace ImaginarySymmetricMatrices

open RealUnitaryMatrices
open scoped Matrix.Norms.Operator

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem toComplex_star (U : unitary (Matrix N N ℝ)) :
    star (toComplex U).val = (toComplex U).val.transpose := by
  change star (complexification U.val) = (complexification U.val).transpose
  rw [← complexification_star, star_eq_transpose, complexification_transpose]

theorem imaginary_conjugate (U : unitary (Matrix N N ℝ)) (A : Matrix N N ℝ) :
    imaginary (RealMatrixSquareNorm.conjugate U A) =
      (toComplex U).val * imaginary A * (toComplex U).val.transpose := by
  change Complex.I • complexification (U.val * A * U.val.transpose) =
    complexification U.val * (Complex.I • complexification A) *
      (complexification U.val).transpose
  rw [map_mul, map_mul, complexification_transpose, mul_smul_comm, smul_mul_assoc]

theorem exp_imaginary_conjugate (U : unitary (Matrix N N ℝ)) (A : Matrix N N ℝ) :
    NormedSpace.exp (imaginary (RealMatrixSquareNorm.conjugate U A)) =
      (toComplex U).val * NormedSpace.exp (imaginary A) * (toComplex U).val.transpose := by
  rw [imaginary_conjugate, ← toComplex_star]
  exact Matrix.exp_units_conj (Unitary.toUnits (toComplex U)) (imaginary A)

theorem imaginary_diagonal (μ : N → ℝ) :
    imaginary (Matrix.diagonal μ) = Matrix.diagonal (fun a ↦ Complex.I * (μ a : ℂ)) := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp only [imaginary_apply, Matrix.diagonal_apply_eq]
  · simp only [imaginary_apply, Matrix.diagonal_apply_ne _ h, Complex.ofReal_zero, mul_zero]

theorem exp_imaginary_diagonal (μ : N → ℝ) :
    NormedSpace.exp (imaginary (Matrix.diagonal μ)) =
      Matrix.diagonal (fun a ↦ Complex.exp (Complex.I * (μ a : ℂ))) := by
  rw [imaginary_diagonal, Matrix.exp_diagonal]
  congr 1
  funext a
  rw [Pi.coe_exp, Complex.exp_eq_exp_ℂ]

theorem det_exp_imaginary_diagonal (μ : N → ℝ) :
    (NormedSpace.exp (imaginary (Matrix.diagonal μ))).det =
      Complex.exp (Complex.I * ((∑ a, μ a : ℝ) : ℂ)) := by
  rw [exp_imaginary_diagonal, Matrix.det_diagonal, Complex.ofReal_sum, Finset.mul_sum,
    Complex.exp_sum]

theorem det_exp_imaginary (A : Matrix N N ℝ) (hsym : A.transpose = A) :
    (NormedSpace.exp (imaginary A)).det = Complex.exp (Complex.I * (A.trace : ℂ)) := by
  obtain ⟨U, μ, hA, htrace⟩ := symmetric_diagonalization A hsym
  have hA' : A = RealMatrixSquareNorm.conjugate U (Matrix.diagonal μ) := hA
  rw [htrace, hA', exp_imaginary_conjugate, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  calc
    (toComplex U).val.det * (NormedSpace.exp (imaginary (Matrix.diagonal μ))).det *
        (toComplex U).val.det = (toComplex U).val.det ^ 2 *
          (NormedSpace.exp (imaginary (Matrix.diagonal μ))).det := by ring
    _ = Complex.exp (Complex.I * ((∑ a, μ a : ℝ) : ℂ)) := by
      rw [toComplex_det_square, one_mul, det_exp_imaginary_diagonal]

theorem exp_imaginary_unitary (A : Matrix N N ℝ) (hsym : A.transpose = A) :
    NormedSpace.exp (imaginary A) ∈ unitary (Matrix N N ℂ) := by
  apply (Matrix.isUnit_exp (imaginary A)).mem_unitary_of_star_mul_self
  change (NormedSpace.exp (imaginary A)).conjTranspose * NormedSpace.exp (imaginary A) = 1
  rw [← Matrix.exp_conjTranspose]
  change NormedSpace.exp (star (imaginary A)) * NormedSpace.exp (imaginary A) = 1
  rw [imaginary_star, hsym,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (imaginary A)).neg_left,
    neg_add_cancel, NormedSpace.exp_zero]

theorem exp_imaginary_transpose (A : Matrix N N ℝ) (hsym : A.transpose = A) :
    (NormedSpace.exp (imaginary A)).transpose = NormedSpace.exp (imaginary A) := by
  rw [← Matrix.exp_transpose, imaginary_transpose, hsym]

end ImaginarySymmetricMatrices

namespace QuaternionicSymmetricMatrices

open ImaginarySymmetricMatrices
open scoped Matrix.Norms.Operator

variable {N : Type*} [Fintype N] [DecidableEq N]

def exponential (A : RealSymmetricMixing.DirectionSpace N) : SpecialSpace N :=
  ⟨⟨⟨NormedSpace.exp (imaginary A.val), exp_imaginary_unitary A.val A.property.1⟩,
      exp_imaginary_transpose A.val A.property.1⟩, by
    apply Circle.ext
    change (NormedSpace.exp (imaginary A.val)).det = 1
    rw [det_exp_imaginary A.val A.property.1, A.property.2,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero]⟩

theorem exponential_zero : exponential (0 : RealSymmetricMixing.DirectionSpace N) =
    specialIdentity := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.exp (imaginary 0) = 1
  rw [map_zero, NormedSpace.exp_zero]

theorem continuous_exponential :
    Continuous (exponential : RealSymmetricMixing.DirectionSpace N → SpecialSpace N) := by
  have hi : Continuous (imaginary : Matrix N N ℝ → Matrix N N ℂ) := by
    change Continuous (fun A : Matrix N N ℝ ↦ Complex.I • RealUnitaryMatrices.complexification A)
    exact (RealUnitaryMatrices.continuous_complexification (N := N)).const_smul Complex.I
  have he : Continuous (fun A : RealSymmetricMixing.DirectionSpace N ↦
      NormedSpace.exp (imaginary A.val)) :=
    NormedSpace.exp_continuous.comp (hi.comp continuous_subtype_val)
  exact ((he.subtype_mk _).subtype_mk _).subtype_mk _

def exponentialCurve (A : RealSymmetricMixing.DirectionSpace N) (t : ℝ) : SpecialSpace N :=
  exponential (t • A)

theorem exponentialCurve_zero (A : RealSymmetricMixing.DirectionSpace N) :
    exponentialCurve A 0 = specialIdentity := by
  rw [exponentialCurve, zero_smul, exponential_zero]

theorem continuous_exponentialCurve (A : RealSymmetricMixing.DirectionSpace N) :
    Continuous (exponentialCurve A) :=
  continuous_exponential.comp (continuous_id.smul continuous_const)

end QuaternionicSymmetricMatrices

end Wikipedia.HomotopyGroupsOfSpheres
