import ErdosProblems.Erdos1148.FrameVectorLengths

/-! # Exact lattice-vector lengths along a diagonal-flow trajectory -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma frameRealVector_diagonalFlow (t : ℝ) (v : Fin 2 → ℝ) :
    frameRealVector (diagonalFlow t) v =
      ![Real.exp (-(t / 2)) * v 0, Real.exp (t / 2) * v 1] := by
  rw [frameRealVector, Matrix.SpecialLinearGroup.toLin'_symm_apply]
  change (((diagonalFlow t)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).mulVec v = _
  rw [← diagonalFlow_neg]
  ext i
  fin_cases i <;> simp [diagonalFlow, Matrix.mulVec, Fin.sum_univ_two,
    Matrix.vecHead, Matrix.vecTail, neg_div]

theorem modularVectorLengthSq_flow (g : SL(2, ℝ)) (t : ℝ) (u v : ℤ) :
    modularVectorLengthSq (g * diagonalFlow t) u v =
      Real.exp (-t) * (modularVector g u v).1 ^ 2 +
        Real.exp t * (modularVector g u v).2 ^ 2 := by
  rw [modularVectorLengthSq_eq, frameRealVector_comp, frameRealVector_diagonalFlow]
  have hpair := frameRealVector_pair g u v
  have h0 := congrArg Prod.fst hpair
  have h1 := congrArg Prod.snd hpair
  dsimp only at h0 h1
  have hexp (s : ℝ) : Real.exp (s / 2) ^ 2 = Real.exp s := by
    rw [pow_two, ← Real.exp_add, add_halves]
  simp only [vectorLengthSq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_pow, h0, h1, ← neg_div, hexp]

theorem modularVectorLengthSq_flow_le (g : SL(2, ℝ)) (t : ℝ) (u v : ℤ) :
    modularVectorLengthSq (g * diagonalFlow t) u v ≤
      Real.exp |t| * modularVectorLengthSq g u v := by
  rw [modularVectorLengthSq_flow]
  change _ ≤ Real.exp |t| * ((modularVector g u v).1 ^ 2 + (modularVector g u v).2 ^ 2)
  rw [mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_abs t)) (sq_nonneg _))
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (le_abs_self t)) (sq_nonneg _))

end Erdos1148.DukeArithmetic
