import ErdosProblems.Erdos1148.FlowVectorLengths

/-! # Two sufficiently short vectors in a unimodular lattice are dependent -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma modularVector_determinant (g : SL(2, ℝ)) (u v w z : ℤ) :
    (modularVector g u v).1 * (modularVector g w z).2 -
      (modularVector g u v).2 * (modularVector g w z).1 = ((u * z - v * w : ℤ) : ℝ) := by
  have hdet := Matrix.SpecialLinearGroup.det_coe (g⁻¹ : SL(2, ℝ))
  rw [Matrix.det_fin_two] at hdet
  dsimp only [modularVector]
  push_cast
  linear_combination ((u : ℝ) * z - (v : ℝ) * w) * hdet

theorem int_pair_determinant_eq_zero_of_short_product (g : SL(2, ℝ)) (u v w z : ℤ)
    (hshort : modularVectorLengthSq g u v * modularVectorLengthSq g w z < 1) :
    u * z - v * w = 0 := by
  have hdet : (((u * z - v * w : ℤ) : ℝ)) ^ 2 ≤
      modularVectorLengthSq g u v * modularVectorLengthSq g w z := by
    rw [← modularVector_determinant]
    dsimp only [modularVectorLengthSq]
    nlinarith [sq_nonneg ((modularVector g u v).1 * (modularVector g w z).1 +
      (modularVector g u v).2 * (modularVector g w z).2)]
  have hlt : (u * z - v * w) ^ 2 < (1 : ℤ) := by exact_mod_cast hdet.trans_lt hshort
  nlinarith [sq_nonneg (u * z - v * w)]

end Erdos1148.DukeArithmetic
