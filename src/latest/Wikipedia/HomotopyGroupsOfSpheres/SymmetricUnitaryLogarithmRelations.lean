import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixLocalLogarithm
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryMidpointRecovery
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Symmetry, skew adjointness, and trace of the small matrix logarithm -/

noncomputable section

open scoped Matrix.Norms.Frobenius

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixLocalLogarithm

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem logarithm_transpose (B : Matrix N N ℂ) (hB : B ∈ domain N)
    (hsym : B.transpose = B) : (logarithm B).transpose = logarithm B := by
  apply exp_injective_small (by simpa only [Matrix.frobenius_norm_transpose] using hB.2) hB.2
  rw [Matrix.exp_transpose, exp_logarithm B hB.1, hsym]

theorem logarithm_star (B : Matrix N N ℂ) (hB : B ∈ domain N)
    (hunit : B ∈ unitary (Matrix N N ℂ)) : star (logarithm B) = -logarithm B := by
  have hs : ‖star (logarithm B)‖ < radius N := by
    change ‖(logarithm B).conjTranspose‖ < radius N
    simpa only [Matrix.frobenius_norm_conjTranspose] using hB.2
  apply exp_injective_small hs (by simpa only [norm_neg] using hB.2)
  change NormedSpace.exp (logarithm B).conjTranspose = NormedSpace.exp (-logarithm B)
  rw [Matrix.exp_conjTranspose, Matrix.exp_neg, exp_logarithm B hB.1]
  exact (Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem hunit)).symm

def realLogarithm (B : Matrix N N ℂ) : Matrix N N ℝ := (logarithm B).map Complex.im

theorem imaginary_realLogarithm (B : Matrix N N ℂ) (hB : B ∈ domain N)
    (hsym : B.transpose = B) (hunit : B ∈ unitary (Matrix N N ℂ)) :
    ImaginarySymmetricMatrices.imaginary (realLogarithm B) = logarithm B :=
  ImaginarySymmetricMatrices.imaginary_map_im _
    (logarithm_transpose B hB hsym) (logarithm_star B hB hunit)

theorem realLogarithm_transpose (B : Matrix N N ℂ) (hB : B ∈ domain N)
    (hsym : B.transpose = B) : (realLogarithm B).transpose = realLogarithm B :=
  ImaginarySymmetricMatrices.map_im_transpose _ (logarithm_transpose B hB hsym)

theorem realLogarithm_trace (B : Matrix N N ℂ) (hB : B ∈ domain N)
    (hsym : B.transpose = B) (hunit : B ∈ unitary (Matrix N N ℂ)) (hdet : B.det = 1) :
    (realLogarithm B).trace = 0 := by
  have hi := imaginary_realLogarithm B hB hsym hunit
  have ht := logarithm_trace_lt B hB
  rw [← hi, ImaginarySymmetricMatrices.imaginary_trace, norm_mul, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs] at ht
  have he : Complex.exp (Complex.I * ((realLogarithm B).trace : ℂ)) = 1 := by
    rw [← ImaginarySymmetricMatrices.det_exp_imaginary _ (realLogarithm_transpose B hB hsym),
      hi, exp_logarithm B hB.1, hdet]
  have hc : Circle.exp (realLogarithm B).trace = Circle.exp 0 := by
    apply Circle.ext
    simpa only [Circle.coe_exp, Complex.ofReal_zero, zero_mul, mul_zero, Complex.exp_zero,
      mul_comm]
      using he
  apply Circle.exp_injOn_Ico (a := -Real.pi) (b := Real.pi) (by linarith) _ _ hc
  · exact ⟨(abs_lt.mp ht).1.le, (abs_lt.mp ht).2⟩
  · exact ⟨neg_nonpos.mpr Real.pi_pos.le, Real.pi_pos⟩

theorem realLogarithm_mem (B : QuaternionicSymmetricMatrices.SpecialSpace N)
    (hB : B.val.val.val ∈ domain N) : realLogarithm B.val.val.val ∈
      RealSymmetricMixing.symmetricTraceZero N := by
  refine ⟨realLogarithm_transpose _ hB B.val.property,
    realLogarithm_trace _ hB B.val.property B.val.val.property ?_⟩
  exact congrArg (fun z : Circle ↦ (z : ℂ)) B.property

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixLocalLogarithm
