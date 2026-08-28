import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPivotScalarRelations

/-!
# A target preimage on the first parameter equator is at the midpoint

The norm and pairing constraints exclude nonmidpoint values of the second
parameter when the first cosine vanishes. The unrestricted first-parameter
exclusion is still a separate problem.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices

local notation "ℍ" => Quaternion ℝ

theorem target_pivotCoordinate_ne_zero (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) : pivotCoordinate s t B ≠ 0 := by
  intro hz
  have h2 := target_pivot_complex_two s t B h
  rw [hz, star_zero, mul_zero, neg_zero] at h2
  have hH : complexPart (referenceSquare s t) = 0 :=
    (mul_eq_zero.mp h2.symm).resolve_left targetBeta_ne_zero
  have hm := pivot_complex_middle s t B
  rw [hz, star_zero, mul_zero, sub_zero] at hm
  have h0 := target_pivot_complex_zero s t B h
  rw [hz, star_zero, mul_zero, sub_zero, hH, mul_zero] at h0
  have hw : angleComplex s t = 0 := by
    rcases mul_eq_zero.mp h0 with hw | hp
    · exact hw
    · simpa [hp] using hm
  rw [referenceSquare_complexPart, hw, zero_pow (by decide : 2 ≠ 0), sub_zero] at hH
  rw [pow_two] at hH
  have hc' : (angleReal s t : ℂ) = 0 := (mul_eq_zero.mp hH).elim id id
  have hc : angleReal s t = 0 := Complex.ofReal_eq_zero.mp hc'
  exact target_angleReal_ne_zero s t B h hc

theorem target_schurPivot_normSq_pos (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) : 0 < Quaternion.normSq (schurPivot s t B) := by
  rw [normSq_complex_pair]
  change 0 < Complex.normSq (pivotComplex s t B) + Complex.normSq (pivotCoordinate s t B)
  exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
    (Complex.normSq_pos.mpr (target_pivotCoordinate_ne_zero s t B h))

theorem referenceSquare_eq_one_of_cos_zero (s t : ℝ) (hs : Real.cos s = 0) :
    referenceSquare s t = 1 := by
  have hr := congrArg Complex.re (scalarRotation_complexPart s t)
  change (scalarRotation s t).re = Real.cos s at hr
  rw [hs] at hr
  have hu := (scalarRotation_unitary s t).1
  rw [Quaternion.star_eq_neg.mpr hr, neg_mul] at hu
  exact hu

theorem pureImaginary_pivot_elimination (w p q : ℂ) (n : ℝ) (hw : w.re = 0) (hq : q ≠ 0)
    (hs : w * (1 + (n : ℂ)) + p = targetAlpha * star p)
    (hc : 2 * p * star q = star w * star q * targetAlpha - w * star q) : w = 0 := by
  have he : 2 * p = star w * targetAlpha - w := by
    apply mul_right_cancel₀ (star_ne_zero.mpr hq)
    linear_combination hc
  have hsr := congrArg Complex.re hs
  have her := congrArg Complex.re he
  have hei := congrArg Complex.im he
  norm_num [targetAlpha, Complex.star_def, Complex.mul_re, Complex.mul_im, hw] at hsr her hei
  apply Complex.ext
  · exact hw
  · change w.im = 0
    linarith

theorem target_angleComplex_zero_of_cos_zero (s t : ℝ) (B : Space (Fin 3))
    (hcos : Real.cos s = 0) (h : firstColumnFormula s t B = targetColumn) :
    angleComplex s t = 0 := by
  have href := referenceSquare_eq_one_of_cos_zero s t hcos
  have hcp : complexPart (1 : ℍ) = 1 := rfl
  have hcj : coordinate (1 : ℍ) = 0 := rfl
  apply pureImaginary_pivot_elimination (angleComplex s t) (pivotComplex s t B)
    (pivotCoordinate s t B) (Quaternion.normSq (schurPivot s t B)) hcos
    (target_pivotCoordinate_ne_zero s t B h)
  · have he := target_pivot_symmetry s t B h
    simpa only [href, hcp, hcj, one_mul, zero_mul, add_zero] using he
  · have he := target_pivot_cross s t B h
    simpa only [href, hcp, hcj, mul_zero, zero_mul, zero_sub, neg_zero, zero_add, mul_one] using he

theorem target_second_midpoint_of_first_midpoint (t : ℝ) (B : Space (Fin 3))
    (ht : t ∈ Set.Icc 0 Real.pi)
    (h : firstColumnFormula (Real.pi / 2) t B = targetColumn) : t = Real.pi / 2 := by
  have hw := target_angleComplex_zero_of_cos_zero (Real.pi / 2) t B Real.cos_pi_div_two h
  have hi := congrArg Complex.im hw
  change Real.sin (Real.pi / 2) * Real.cos t = 0 at hi
  rw [Real.sin_pi_div_two, one_mul] at hi
  apply Real.strictAntiOn_cos.injOn ht
  · constructor <;> linarith [Real.pi_pos]
  · exact hi.trans Real.cos_pi_div_two.symm

theorem target_referenceCoordinate_ne_zero_away (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) (hcos : Real.cos s ≠ 0) :
    coordinate (referenceSquare s t) ≠ 0 := by
  rw [referenceSquare_coordinate_real]
  apply Complex.ofReal_ne_zero.mpr
  exact mul_ne_zero (mul_ne_zero (by norm_num) hcos) (target_angleReal_ne_zero s t B h)

theorem target_pivot_coordinate_formula_away (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) (hcos : Real.cos s ≠ 0) :
    star (pivotCoordinate s t B) =
      (angleComplex s t * (1 + ((Quaternion.normSq (schurPivot s t B) : ℝ) : ℂ)) +
        pivotComplex s t B - targetAlpha * complexPart (referenceSquare s t) *
          star (pivotComplex s t B)) / (targetAlpha * coordinate (referenceSquare s t)) := by
  have hα : targetAlpha ≠ 0 := by norm_num [targetAlpha]
  apply (eq_div_iff (mul_ne_zero hα (target_referenceCoordinate_ne_zero_away s t B h hcos))).mpr
  linear_combination -(target_pivot_symmetry s t B h)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
