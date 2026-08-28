import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPreimageRadialDeterminant

/-! # The angular linear system at a midpoint target

This proves the algebraic kernel elimination and the sign of its real
two-by-two determinant. Deriving these linear equations from the full
projected-map derivative is a separate step.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open ComplexCrossProductUnitary

def angularVariation (u w : ℂ) : ℂ := u * (3 * star w + targetAlpha * w) - (w + star w)

def angularMatrix (u : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![3 * u.re - u.im / 2 - 2, 3 * u.im - u.re / 2;
     3 * u.im + u.re / 2, -3 * u.re - u.im / 2]

theorem angularVariation_coordinates (u w : ℂ) :
    ![(angularVariation u w).re, (angularVariation u w).im] =
      angularMatrix u *ᵥ ![w.re, w.im] := by
  funext r
  fin_cases r <;>
    simp [angularVariation, angularMatrix, targetAlpha, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem angularMatrix_det (u : ℂ) :
    (angularMatrix u).det = -(35 / 4) * Complex.normSq u + 6 * u.re + u.im := by
  simp [angularMatrix, Matrix.det_fin_two, Complex.normSq_apply]
  ring

theorem angularMatrix_det_neg (u : unitary ℂ) : (angularMatrix u.val).det < 0 := by
  have hn := unitary_normSq u
  rw [Complex.normSq_apply] at hn
  have hr : u.val.re ≤ 1 := by
    nlinarith [sq_nonneg u.val.im, sq_nonneg (u.val.re - 1)]
  have hi : u.val.im ≤ 1 := by
    nlinarith [sq_nonneg u.val.re, sq_nonneg (u.val.im - 1)]
  rw [angularMatrix_det, unitary_normSq]
  linarith

theorem angularVariation_eq_zero (u : unitary ℂ) (w : ℂ)
    (h : angularVariation u.val w = 0) : w = 0 := by
  have hi : Function.Injective (angularMatrix u.val).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((angularMatrix u.val).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr (ne_of_lt (angularMatrix_det_neg u))))
  have he := angularVariation_coordinates u.val w
  rw [h] at he
  have hz : angularMatrix u.val *ᵥ ![w.re, w.im] = 0 := by
    rw [← he]
    funext r
    fin_cases r <;> rfl
  have hw : ![w.re, w.im] = (0 : Fin 2 → ℝ) := hi (hz.trans (Matrix.mulVec_zero _).symm)
  apply Complex.ext
  · exact congrFun hw 0
  · exact congrFun hw 1

theorem unitary_square_mul_star (u : unitary ℂ) : u.val ^ 2 * star u.val = u.val := by
  calc
    _ = u.val * (u.val * star u.val) := by ring
    _ = _ := by rw [u.property.2, mul_one]

theorem linearized_column_kernel (u : unitary ℂ) (w z v : ℂ)
    (ht : v + u.val ^ 2 * targetBeta * star z + u.val ^ 2 * targetAlpha * star v = 0)
    (h0 : z - u.val ^ 2 * targetAlpha * star z - u.val * (w + targetAlpha * star w) +
      (w + star w) * targetAlpha = 0)
    (h1 : v - u.val ^ 2 * targetBeta * star z - u.val * targetBeta * star w +
      (w + star w) * targetBeta = 0) : w = 0 ∧ z = 0 ∧ v = 0 := by
  have hc : targetBeta * z - targetAlpha * v = u.val * targetBeta * w := by
    linear_combination targetBeta * h0 - targetAlpha * h1
  have hs : targetBeta * star z + targetAlpha * star v =
      star u.val * targetBeta * star w := by
    have he := congrArg star hc
    simp only [star_sub, star_mul, targetBeta_star, targetAlpha_star] at he
    linear_combination he
  have hv : v = -u.val * targetBeta * star w := by
    calc
      v = -u.val ^ 2 * (targetBeta * star z + targetAlpha * star v) := by
        linear_combination ht
      _ = -(u.val ^ 2 * star u.val) * targetBeta * star w := by rw [hs]; ring
      _ = _ := by rw [unitary_square_mul_star]
  have hz : z = u.val * (w - targetAlpha * star w) := by
    apply mul_left_cancel₀ targetBeta_ne_zero
    linear_combination hc + targetAlpha * hv
  have hsz : star z = star u.val * (star w + targetAlpha * w) := by
    rw [hz]
    simp only [star_mul, star_sub, targetAlpha_star, star_star]
    ring
  have he : targetBeta * angularVariation u.val w = 0 := by
    rw [hv, hsz] at h1
    have hm : u.val ^ 2 * targetBeta * (star u.val * (star w + targetAlpha * w)) =
        u.val * targetBeta * (star w + targetAlpha * w) := by
      calc
        _ = (u.val ^ 2 * star u.val) * targetBeta * (star w + targetAlpha * w) := by ring
        _ = _ := by rw [unitary_square_mul_star]
    rw [hm] at h1
    unfold angularVariation
    linear_combination -h1
  have hw := angularVariation_eq_zero u w ((mul_eq_zero.mp he).resolve_left targetBeta_ne_zero)
  refine ⟨hw, ?_, ?_⟩
  · simpa [hw] using hz
  · simpa [hw] using hv

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
