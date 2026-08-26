import ErdosProblems.Erdos421.MeanValueRootScale
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # A degree-explicit derivative remainder for logarithmic Taylor polynomials -/

namespace Erdos421

noncomputable def logTaylorPolynomial (k : ℕ) (z w : ℝ) : ℝ :=
  ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * w ^ (i + 1) /
    (((i + 1 : ℕ) : ℝ) * z ^ (i + 1))

theorem reciprocal_sub_logTaylorDerivative (k : ℕ) {z w : ℝ}
    (hz : z ≠ 0) (hzw : z + w ≠ 0) :
    1 / (z + w) - (∑ i ∈ Finset.range k, (-w) ^ i / z ^ (i + 1)) =
      (-w) ^ k / (z ^ k * (z + w)) := by
  induction k with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, one_mul]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    calc
      _ = (1 / (z + w) - ∑ i ∈ Finset.range k, (-w) ^ i / z ^ (i + 1)) -
          (-w) ^ k / z ^ (k + 1) := by ring
      _ = (-w) ^ k / (z ^ k * (z + w)) - (-w) ^ k / z ^ (k + 1) := by rw [ih]
      _ = _ := by
        rw [pow_succ, pow_succ]
        field_simp
        ring

theorem hasDerivAt_logTaylorPolynomial (k : ℕ) {z : ℝ} (hz : z ≠ 0) (w : ℝ) :
    HasDerivAt (logTaylorPolynomial k z)
      (∑ i ∈ Finset.range k, (-w) ^ i / z ^ (i + 1)) w := by
  apply HasDerivAt.fun_sum
  intro i _
  have hi : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h := ((hasDerivAt_pow (i + 1) w).const_mul ((-1 : ℝ) ^ i)).div_const
    (((i + 1 : ℕ) : ℝ) * z ^ (i + 1))
  convert! h using 1
  simp only [Nat.add_sub_cancel]
  rw [neg_pow]
  field_simp

theorem hasDerivAt_logTaylorRemainder (k : ℕ) {z w : ℝ}
    (hz : z ≠ 0) (hzw : z + w ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ Real.log (z + x) - Real.log z - logTaylorPolynomial k z x)
      ((-w) ^ k / (z ^ k * (z + w))) w := by
  have hlog : HasDerivAt (fun x : ℝ ↦ Real.log (z + x)) (1 / (z + w)) w := by
    simpa only [one_div, one_mul, mul_one] using!
      (Real.hasDerivAt_log hzw).comp w ((hasDerivAt_id w).const_add z)
  convert! (hlog.sub_const (Real.log z)).sub (hasDerivAt_logTaylorPolynomial k hz w) using 1
  exact (reciprocal_sub_logTaylorDerivative k hz hzw).symm

theorem logTaylorRemainder_derivative_abs_le (k : ℕ) {z w M : ℝ}
    (hz : 0 < z) (hw : 0 ≤ w) (hwM : w ≤ M) :
    |(-w) ^ k / (z ^ k * (z + w))| ≤ M ^ k / z ^ (k + 1) := by
  have hzw : 0 < z + w := by positivity
  rw [abs_div, abs_pow, abs_neg, abs_of_nonneg hw,
    abs_of_pos (mul_pos (pow_pos hz k) hzw)]
  calc
    _ ≤ M ^ k / (z ^ k * (z + w)) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hw hwM k) (by positivity)
    _ ≤ M ^ k / z ^ (k + 1) := by
      apply div_le_div_of_nonneg_left (pow_nonneg (hw.trans hwM) k) (pow_pos hz _)
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hz.le k)

end Erdos421
