import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicReducedFirstColumn

/-!
# A positive real denominator for the projected coordinate formula

The only quaternion inverse in the Schur formula is replaced by conjugation
and a real denominator bounded below by one. Thus the explicit formula has
no hidden poles on its parameter space.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices QuaternionicComplexPlane

local notation "ℍ" => Quaternion ℝ

theorem normSq_one_add_of_re_zero (q : ℍ) (hq : q.re = 0) :
    Quaternion.normSq (1 + q) = 1 + Quaternion.normSq q := by
  rw [Quaternion.normSq_add]
  simp only [map_one, one_mul, Quaternion.re_star, hq, mul_zero, add_zero]

theorem inverse_one_add_of_re_zero (q : ℍ) (hq : q.re = 0) :
    (1 + q)⁻¹ = (1 + Quaternion.normSq q)⁻¹ • (1 - q) := by
  rw [Quaternion.inv_def, normSq_one_add_of_re_zero q hq, star_add, star_one,
    Quaternion.star_eq_neg.mpr hq, sub_eq_add_neg]

theorem normSq_embed (z : ℂ) : Quaternion.normSq (embed z) = Complex.normSq z := by
  rw [Quaternion.normSq_def', embed_eq_mk, Complex.normSq_apply]
  change (0 : ℝ) ^ 2 + 0 ^ 2 + z.re ^ 2 + z.im ^ 2 = z.re * z.re + z.im * z.im
  ring

def realDenominator (s t : ℝ) (B : Space (Fin 3)) : ℝ :=
  1 + (Real.sin s * Real.sin t) ^ 2 * Complex.normSq (B.val.val 1 0)

theorem realDenominator_ge_one (s t : ℝ) (B : Space (Fin 3)) :
    1 ≤ realDenominator s t B := by
  unfold realDenominator
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))

theorem realDenominator_pos (s t : ℝ) (B : Space (Fin 3)) :
    0 < realDenominator s t B := lt_of_lt_of_le zero_lt_one (realDenominator_ge_one s t B)

theorem rotation_one_zero (s t : ℝ) (B : Space (Fin 3)) :
    (rotation s t B).val 1 0 = (Real.sin s * Real.sin t) • embed (B.val.val 1 0) := by
  rw [rotation_val, matrix_apply]
  norm_num

theorem rotation_denominator_inverse (s t : ℝ) (B : Space (Fin 3)) :
    (1 + (rotation s t B).val 1 0)⁻¹ =
      (realDenominator s t B)⁻¹ • (1 - (Real.sin s * Real.sin t) • embed (B.val.val 1 0)) := by
  rw [inverse_one_add_of_re_zero _ (rotation_offDiagonal_re s t B 1 0 (by decide)),
    rotation_one_zero, Quaternion.normSq_smul, normSq_embed]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
