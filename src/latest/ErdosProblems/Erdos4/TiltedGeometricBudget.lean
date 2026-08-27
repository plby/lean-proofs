import ErdosProblems.Erdos4.TiltedMomentBudget
import ErdosProblems.Erdos4.TiltedVarianceBudget

/-! Uniform polynomial bounds for the divisor coefficients and collision exponents. -/

namespace Erdos4.Tilted

theorem gcdTiltError_nonneg (W R N : ℕ) (τ : ℝ) {D a : ℝ} (hD : 0 ≤ D) (ha : 0 ≤ a) :
    0 ≤ gcdTiltError W R N τ D a := by
  have he : 1 ≤ Real.exp (2 * a * (W : ℝ) ^ (-(1 / 2 : ℝ))) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
      (show 0 ≤ 2 * a * (W : ℝ) ^ (-(1 / 2 : ℝ)) by positivity)
  unfold gcdTiltError
  exact add_nonneg (mul_nonneg hD (sub_nonneg.mpr he)) (by positivity)

theorem divisor_coefficient_budget {L x b M U : ℝ} (hL : 324 ≤ L) (hx : 0 < x)
    (hb0 : 0 ≤ b) (hb : b ≤ L ^ 2 / x) (hM0 : 0 ≤ M) (hM : M ≤ 17 * x)
    (hU0 : 0 ≤ U) (hU : U ≤ 2 * L) :
    (b * (M + x)) ^ 2 ≤ L ^ 5 ∧ (2 * U) ^ 2 ≤ L ^ 3 := by
  have hLpos : 0 < L := by linarith
  have hbM : b * (M + x) ≤ 18 * L ^ 2 := by
    calc
      _ ≤ (L ^ 2 / x) * (18 * x) := mul_le_mul hb (by linarith) (by linarith) (by positivity)
      _ = _ := by field_simp
  constructor
  · have hh := pow_le_pow_left₀ (mul_nonneg hb0 (by linarith : 0 ≤ M + x)) hbM 2
    have hbig := mul_le_mul_of_nonneg_right hL (show 0 ≤ L ^ (4 : ℕ) by positivity)
    nlinarith
  · have hh := pow_le_pow_left₀ (show 0 ≤ 2 * U by positivity)
      (show 2 * U ≤ 4 * L by linarith) 2
    have hbig := mul_le_mul_of_nonneg_right (show 16 ≤ L by linarith) (sq_nonneg L)
    nlinarith

theorem correlation_exponent_log_budget {L w K v c : ℝ}
    (hL : 1 ≤ L) (hw : L ^ 98 ≤ w) (hK0 : 0 ≤ K) (hK : K ≤ L)
    (hv0 : 0 ≤ v) (hv : v ≤ 2 * L) (_hc0 : 0 ≤ c) (hc : c ≤ 16 * L)
    (hcoef : 128 / Real.log 2 ≤ L ^ 54) :
    c * (2 * K) ^ 2 * v / (w * Real.log 2) ≤ 1 / L ^ 40 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hwpos : 0 < w := (pow_pos hLpos 98).trans_le hw
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hKsq : (2 * K) ^ 2 ≤ (2 * L) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hnum : c * (2 * K) ^ 2 * v ≤ 128 * L ^ 4 := by
    calc
      _ ≤ (16 * L) * (2 * L) ^ 2 * (2 * L) :=
        mul_le_mul (mul_le_mul hc hKsq (sq_nonneg _) (by positivity)) hv hv0 (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (128 * L ^ 4) / (w * Real.log 2) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (128 * L ^ 4) / (L ^ 98 * Real.log 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hw hlog2.le)
    _ = (128 / Real.log 2) / L ^ 94 := by field_simp
    _ ≤ L ^ 54 / L ^ 94 := div_le_div_of_nonneg_right hcoef (by positivity)
    _ = _ := by field_simp

theorem block_correlation_log_budgets {L w K v : ℝ}
    (hL : 1 ≤ L) (hw : L ^ 98 ≤ w) (hK0 : 0 ≤ K) (hK : K ≤ L)
    (hv0 : 0 ≤ v) (hv : v ≤ 2 * L) (hcoef : 128 / Real.log 2 ≤ L ^ 54) :
    (2 + 8 * K) * (2 * K) ^ 2 * v / (w * Real.log 2) ≤ 1 / L ^ 40 ∧
      8 * (K + 1) * (2 * K) ^ 2 * v / (w * Real.log 2) ≤ 1 / L ^ 40 := by
  exact ⟨correlation_exponent_log_budget hL hw hK0 hK hv0 hv (by positivity) (by linarith) hcoef,
    correlation_exponent_log_budget hL hw hK0 hK hv0 hv (by positivity) (by linarith) hcoef⟩

end Erdos4.Tilted
