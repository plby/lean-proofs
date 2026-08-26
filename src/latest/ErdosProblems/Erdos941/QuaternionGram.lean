import ErdosProblems.Erdos941.IntertwinerArea

/-! # Positivity of the quaternion Gram determinant -/

namespace Erdos941

open scoped Quaternion

theorem quaternion_norm_linear_combination (x y : ℚ) (q r : ℍ[ℚ]) :
    Quaternion.normSq (x • q + y • r) =
      x ^ 2 * Quaternion.normSq q + 2 * x * y * (star q * r).re +
        y ^ 2 * Quaternion.normSq r := by
  simp only [Quaternion.normSq_def', Quaternion.re_add, Quaternion.imI_add,
    Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_smul, Quaternion.imI_smul,
    Quaternion.imJ_smul, Quaternion.imK_smul, Quaternion.re_mul, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, smul_eq_mul]
  ring

theorem hurwitzNorm_linear_combination (x y : ℤ) (q r : hurwitzOrder) :
    (hurwitzNorm (x • q + y • r) : ℚ) =
      (x : ℚ) ^ 2 * (hurwitzNorm q : ℚ) +
        2 * (x : ℚ) * (y : ℚ) * (star (q : ℍ[ℚ]) * (r : ℍ[ℚ])).re +
        (y : ℚ) ^ 2 * (hurwitzNorm r : ℚ) := by
  rw [hurwitzNorm_cast, hurwitzNorm_cast, hurwitzNorm_cast]
  change Quaternion.normSq (x • (q : ℍ[ℚ]) + y • (r : ℍ[ℚ])) = _
  simpa only [Int.cast_smul_eq_zsmul] using
    quaternion_norm_linear_combination (x : ℚ) (y : ℚ) (q : ℍ[ℚ]) (r : ℍ[ℚ])

theorem quaternion_projection_norm (q r : ℍ[ℚ]) :
    Quaternion.normSq (Quaternion.normSq q • r - (star q * r).re • q) =
      Quaternion.normSq q *
        (Quaternion.normSq q * Quaternion.normSq r - (star q * r).re ^ 2) := by
  simp only [Quaternion.normSq_def', Quaternion.re_sub, Quaternion.imI_sub,
    Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_smul, Quaternion.imI_smul,
    Quaternion.imJ_smul, Quaternion.imK_smul, Quaternion.re_mul, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, smul_eq_mul]
  ring

theorem hurwitzGram_pos_of_linearIndependent {q r : hurwitzOrder}
    (hlin : LinearIndependent ℚ ![(q : ℍ[ℚ]), (r : ℍ[ℚ])]) :
    0 < hurwitzGram q r := by
  have hq0 : (q : ℍ[ℚ]) ≠ 0 := by
    simpa only [Matrix.cons_val_zero] using hlin.ne_zero 0
  have hn : 0 < Quaternion.normSq (q : ℍ[ℚ]) :=
    lt_of_le_of_ne Quaternion.normSq_nonneg
      (Ne.symm (Quaternion.normSq_eq_zero.not.mpr hq0))
  have hid := quaternion_projection_norm (q : ℍ[ℚ]) (r : ℍ[ℚ])
  change Quaternion.normSq _ = Quaternion.normSq (q : ℍ[ℚ]) * hurwitzGram q r at hid
  by_contra h
  have hle : hurwitzGram q r ≤ 0 := le_of_not_gt h
  have hzero : Quaternion.normSq
      (Quaternion.normSq (q : ℍ[ℚ]) • (r : ℍ[ℚ]) -
        (star (q : ℍ[ℚ]) * (r : ℍ[ℚ])).re • (q : ℍ[ℚ])) = 0 := by
    have hnonneg := Quaternion.normSq_nonneg (a :=
      Quaternion.normSq (q : ℍ[ℚ]) • (r : ℍ[ℚ]) -
        (star (q : ℍ[ℚ]) * (r : ℍ[ℚ])).re • (q : ℍ[ℚ]))
    nlinarith
  have hdep := Quaternion.normSq_eq_zero.mp hzero
  have hcomb : -(star (q : ℍ[ℚ]) * (r : ℍ[ℚ])).re • (q : ℍ[ℚ]) +
      Quaternion.normSq (q : ℍ[ℚ]) • (r : ℍ[ℚ]) = 0 := by
    rw [neg_smul, add_comm, ← sub_eq_add_neg]
    exact hdep
  have hcoeff := (LinearIndependent.pair_iff.mp hlin) _ _ hcomb
  exact hn.ne' hcoeff.2

end Erdos941
