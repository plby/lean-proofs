import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPivotCoordinateNorm
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPreimagePolynomial

/-! # Every selected-target preimage lies at the parameter midpoint

The exact polynomial certificate is applied to the complex components of
the actual Schur pivot. Thus the exclusion uses no extra algebraic
assumptions on the preimage and no determinant restriction on the symmetric
unitary matrix.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices
open PreimagePolynomialCertificate

theorem preimage_constraints_of_complex (w p q : ℂ) (n c : ℝ)
    (hunit : Complex.normSq w + c ^ 2 = 1)
    (hnorm : Complex.normSq p + Complex.normSq q = n)
    (hs : w * (1 + (n : ℂ)) + p = Complex.I / 2 *
      (((c : ℂ) ^ 2 - w ^ 2) * star p + (-(c : ℂ) * (w + star w)) * star q))
    (hc : 2 * p * star q =
      star (Complex.I / 2) * (-(c : ℂ) * (w + star w)) * w * p -
        (-(c : ℂ) * (w + star w)) * ((c : ℂ) ^ 2 - w ^ 2) +
        star w * star q * (Complex.I / 2) * ((c : ℂ) ^ 2 - w ^ 2) - w * star q)
    (hS : Complex.normSq (w * p - Complex.I / 2 * ((c : ℂ) ^ 2 - w ^ 2)) +
      Complex.normSq (w + p) + (3 / 4) * Complex.normSq ((c : ℂ) ^ 2 - w ^ 2) =
        c ^ 2 * Complex.normSq q)
    (hR : Complex.normSq (Complex.I / 2 * (-(c : ℂ) * (w + star w)) - w * q) +
      Complex.normSq q + (3 / 4) * Complex.normSq (-(c : ℂ) * (w + star w)) =
        c ^ 2 * (Complex.normSq p + 1))
    (hnew : 4 * Complex.normSq (p + (1 + (n : ℂ)) * w) = Complex.normSq w * n)
    (hq : Complex.normSq q = n ^ 2 * c ^ 2) :
    Constraints p.re p.im q.re q.im n c w.re w.im := by
  have hsr := congrArg Complex.re hs
  have hsi := congrArg Complex.im hs
  have hcr := congrArg Complex.re hc
  have hci := congrArg Complex.im hc
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def, pow_two]
    at hunit hnorm hsr hsi hcr hci hS hR hnew hq
  constructor
  · unfold constraint0
    linear_combination 4 * hunit
  · unfold constraint1
    linear_combination 4 * hnorm
  · unfold constraint2
    linear_combination 4 * hsr
  · unfold constraint3
    linear_combination 4 * hsi
  · unfold constraint4
    linear_combination 4 * hcr
  · unfold constraint5
    linear_combination 4 * hci
  · unfold constraint6
    linear_combination 4 * hS
  · unfold constraint7
    linear_combination 4 * hR
  · unfold constraint8
    linear_combination hnew
  · unfold constraint9
    linear_combination hq

theorem target_pivot_polynomial_constraints (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    Constraints (pivotComplex s t B).re (pivotComplex s t B).im
      (pivotCoordinate s t B).re (pivotCoordinate s t B).im
      (Quaternion.normSq (schurPivot s t B)) (angleReal s t)
      (angleComplex s t).re (angleComplex s t).im := by
  apply preimage_constraints_of_complex
  · exact angle_norm s t
  · exact (normSq_complex_pair _).symm
  · simpa only [targetAlpha, referenceSquare_complexPart, referenceSquare_coordinate] using
      target_pivot_symmetry s t B h
  · simpa only [targetAlpha, referenceSquare_complexPart, referenceSquare_coordinate] using
      target_pivot_cross s t B h
  · have he := target_pivot_imageS_norm s t B h
    simpa [pivotImageS, Fin.sum_univ_three, Matrix.cons_val_two, targetAlpha,
      referenceSquare_complexPart, map_mul, targetBeta_normSq] using he
  · have he := target_pivot_imageR_norm s t B h
    simpa [pivotImageR, Fin.sum_univ_three, Matrix.cons_val_two, targetAlpha,
      referenceSquare_coordinate, map_mul, targetBeta_normSq] using he
  · exact target_pivot_norm_constraint s t B h
  · exact target_pivotCoordinate_normSq s t B h

theorem target_angleComplex_zero (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) : angleComplex s t = 0 := by
  obtain ⟨hr, hi⟩ := coordinates_eq_zero _ _ _ _ _ _ _ _
    (show 0 ≤ Quaternion.normSq (schurPivot s t B) from Quaternion.normSq_nonneg)
    (schurPivot_normSq_le_one s t B) (target_pivot_polynomial_constraints s t B h)
  exact Complex.ext hr hi

theorem target_parameter_midpoint (s t : ℝ) (B : Space (Fin 3))
    (hs : s ∈ Set.Icc 0 Real.pi) (ht : t ∈ Set.Icc 0 Real.pi)
    (h : firstColumnFormula s t B = targetColumn) :
    s = Real.pi / 2 ∧ t = Real.pi / 2 := by
  have hw := target_angleComplex_zero s t B h
  have hc : Real.cos s = 0 := congrArg Complex.re hw
  have hi : Real.sin s * Real.cos t = 0 := congrArg Complex.im hw
  have hmid : Real.pi / 2 ∈ Set.Icc 0 Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have hs' : s = Real.pi / 2 :=
    Real.strictAntiOn_cos.injOn hs hmid (hc.trans Real.cos_pi_div_two.symm)
  rw [hs', Real.sin_pi_div_two, one_mul] at hi
  exact ⟨hs', Real.strictAntiOn_cos.injOn ht hmid (hi.trans Real.cos_pi_div_two.symm)⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
