import ErdosProblems.Erdos1148.FlowVectorLengths

/-! # A vector of bounded length at time S has a small expanding coordinate at time zero -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem modularVector_second_le_of_flow_lengthSq (g : SL(2, ℝ)) (S C : ℝ) (hC : 0 ≤ C)
    (u v : ℤ) (hshort : modularVectorLengthSq (g * diagonalFlow S) u v ≤ C ^ 2) :
    |(modularVector g u v).2| ≤ C * Real.exp (-(S / 2)) := by
  rw [modularVectorLengthSq_flow] at hshort
  have hle : Real.exp S * (modularVector g u v).2 ^ 2 ≤ C ^ 2 := by
    nlinarith [mul_nonneg (Real.exp_pos (-S)).le (sq_nonneg (modularVector g u v).1)]
  have hmul := mul_le_mul_of_nonneg_left hle (Real.exp_pos (-S)).le
  have hexp : Real.exp (-S) * Real.exp S = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hsquare : Real.exp (-(S / 2)) ^ 2 = Real.exp (-S) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : |(modularVector g u v).2| ^ 2 ≤ (C * Real.exp (-(S / 2))) ^ 2 := by
    rw [sq_abs, mul_pow, hsquare]
    rw [← mul_assoc, hexp, one_mul] at hmul
    simpa only [mul_comm] using hmul
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)).mp hsq

lemma unstable_parameter_difference_le {x y r s e c : ℝ}
    (hc : 0 < c) (hx : c ≤ |x|) (hr : |y - r * x| ≤ e) (hs : |y - s * x| ≤ e) :
    |r - s| ≤ 2 * e / c := by
  have hdiff : |(r - s) * x| ≤ 2 * e := by
    calc
      _ = |(y - s * x) - (y - r * x)| := by congr 1; ring
      _ ≤ |y - s * x| + |y - r * x| := abs_sub _ _
      _ ≤ 2 * e := by linarith
  rw [abs_mul] at hdiff
  apply (le_div_iff₀ hc).mpr
  exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans hdiff

end Erdos1148.DukeArithmetic
