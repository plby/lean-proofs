import ErdosProblems.Erdos1148.SpecialLinearCharacters
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-! # Translation and dilation formulas for upper half-plane frames -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma stableHorocycle_smul_eq_vadd (r : ℝ) (z : UpperHalfPlane) :
    stableHorocycle r • z = r +ᵥ z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_vadd]
  simp [stableHorocycle, add_comm]

lemma stableHorocycle_smul_re (r : ℝ) (z : UpperHalfPlane) :
    (stableHorocycle r • z).re = r + z.re := by
  rw [stableHorocycle_smul_eq_vadd]
  simp

lemma stableHorocycle_smul_im (r : ℝ) (z : UpperHalfPlane) :
    (stableHorocycle r • z).im = z.im := by
  rw [stableHorocycle_smul_eq_vadd]
  simp

lemma diagonal_frame_smul_coe (h : ℝ) (hh : h ≠ 0) (z : UpperHalfPlane) :
    ((upperTriangularFrame 0 h hh • z : UpperHalfPlane) : ℂ) = (h : ℂ) ^ 2 * (z : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [upperTriangularFrame, div_eq_mul_inv] <;> ring

lemma diagonal_frame_smul_re (h : ℝ) (hh : h ≠ 0) (z : UpperHalfPlane) :
    (upperTriangularFrame 0 h hh • z).re = h ^ 2 * z.re := by
  have heq := congrArg Complex.re (diagonal_frame_smul_coe h hh z)
  change ((upperTriangularFrame 0 h hh • z : UpperHalfPlane) : ℂ).re = h ^ 2 * (z : ℂ).re
  simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero] using heq

lemma diagonal_frame_smul_im (h : ℝ) (hh : h ≠ 0) (z : UpperHalfPlane) :
    (upperTriangularFrame 0 h hh • z).im = h ^ 2 * z.im := by
  have heq := congrArg Complex.im (diagonal_frame_smul_coe h hh z)
  change ((upperTriangularFrame 0 h hh • z : UpperHalfPlane) : ℂ).im = h ^ 2 * (z : ℂ).im
  simpa only [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero] using heq

end Erdos1148.DukeArithmetic
