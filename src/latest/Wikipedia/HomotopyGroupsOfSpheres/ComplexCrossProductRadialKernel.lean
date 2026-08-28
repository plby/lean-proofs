import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductCurveKernel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Radial directions left by the diagonal conjugation equations

The norm and complex square-sum constraints form an explicit real
three-by-three matrix. Its nonsingularity eliminates all remaining radial
directions in the kernel of the symmetric-image derivative.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

def radialMatrix (z : Vector) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun r s ↦ ![Complex.normSq (z s), (z s ^ 2).re, (z s ^ 2).im] r

theorem radial_velocity_eq_zero (z v : Vector) (a : Fin 3 → ℝ)
    (ha : ∀ r, v r = (a r : ℂ) * z r)
    (hn : ∑ r, (star (v r) * z r + star (z r) * v r) = 0)
    (ht : squareSumVariation z v = 0) (hd : (radialMatrix z).det ≠ 0) : v = 0 := by
  have hnre := congrArg Complex.re hn
  have htre := congrArg Complex.re ht
  have htim := congrArg Complex.im ht
  simp only [ha, star_mul', RCLike.star_def, Complex.conj_ofReal, Fin.sum_univ_three,
    Fin.isValue, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.conj_re,
    Complex.ofReal_im, Complex.conj_im, mul_neg, zero_mul, neg_zero, sub_zero,
    Complex.mul_im, add_zero, neg_mul, sub_neg_eq_add, Complex.zero_re,
    squareSumVariation, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im,
    Complex.zero_im] at hnre htre htim
  have hm : radialMatrix z *ᵥ a = 0 := by
    funext r
    fin_cases r <;>
      simp [radialMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_two, Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im]
    · linear_combination hnre / 2
    · linear_combination htre / 2
    · linear_combination htim / 2
  have hi : Function.Injective (radialMatrix z).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((radialMatrix z).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd))
  have ha0 : a = 0 := hi (hm.trans (Matrix.mulVec_zero _).symm)
  funext r
  rw [ha, ha0]
  simp

theorem sphere_curve_diagonal_kernel (z : ℝ → UnitSphere) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ (z t).val r) (v r) x)
    (hv : symmetricVariation (z x).val v = 0) (d : Fin 3 → ℂ)
    (hd : (symmetricMap (z x)).val.val = Matrix.diagonal d)
    (hcoord : ∀ r, (z x).val r ≠ 0)
    (htrace : Complex.normSq (squareSum (z x).val) < 1)
    (hdet : (radialMatrix (z x).val).det ≠ 0) : v = 0 := by
  choose a ha using fun r ↦ sphere_curve_diagonal_velocity_real z v x hz hv d hd r (hcoord r)
  exact radial_velocity_eq_zero _ _ a ha (sphere_curve_norm_tangent z v x hz)
    (squareSumVariation_eq_zero_of_symmetricVariation _ _ htrace hv) hdet

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
