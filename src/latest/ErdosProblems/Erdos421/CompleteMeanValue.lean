import ErdosProblems.Erdos421.MeanValueConstants

/-! # An explicit classical complete-system mean-value estimate

The count is the actual number of solutions to all the power-sum equations
of degrees `1,...,k`, with variables in `1,...,N`. No analytic or counting
estimate is assumed in this theorem.
-/

namespace Erdos421

theorem vinogradovCount_complete_meanValue {k : ℕ} (hk : 2 ≤ k) (r N : ℕ) :
    (vinogradovCount ((r + 1) * k) k N : ℝ) ≤
      (2 : ℝ) ^ (32 * (k + 1) ^ 5 * (r + 1) ^ 3) *
        (N : ℝ) ^ meanValueExponent k r := by
  by_cases hN : 0 < N
  · have hc : (meanValueConstant k r : ℝ) ≤
        (2 : ℝ) ^ (32 * (k + 1) ^ 5 * (r + 1) ^ 3) := by
      exact_mod_cast (meanValueConstant_le_two_pow k r).trans
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _
          (meanValueCoefficient_le_polynomial k)))
    exact (vinogradovCount_meanValueIteration hk r N hN).trans
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  · have hzero : N = 0 := by omega
    subst N
    have hs : 2 * ((r + 1) * k) ≠ 0 := by positivity
    have hz : vinogradovCount ((r + 1) * k) k 0 = 0 :=
      Nat.eq_zero_of_le_zero (by simpa only [zero_pow hs] using
        vinogradovCount_le_trivial ((r + 1) * k) k 0)
    rw [hz, Nat.cast_zero]
    positivity

end Erdos421
