import Arxiv.Arxiv2411_18291.ExplicitReserveNumerics

/-! # A finite simultaneous probability bound for reserve sampling -/

namespace Arxiv2411_18291

theorem typical_sampling_tail_lt_one {r n K : ℕ} (hn1 : (1 : ℝ) ≤ n)
    (hlarge : (48 * (r * K) + 24 * K + 36 : ℝ) < (n : ℝ) ^ (1 / 4 : ℝ)) :
    2 * (K + 2 : ℝ) * (n : ℝ) ^ (r * K) *
      Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ) / 12)) < 1 := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  let x : ℝ := (n : ℝ) ^ (1 / 4 : ℝ)
  have hx : 0 < x := Real.rpow_pos_of_pos hn0 _
  have hx1 : 1 ≤ x := Real.one_le_rpow hn1 (by norm_num)
  have hln : Real.log (n : ℝ) ≤ 4 * x := by
    have hh := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 4)
    convert hh using 1
    dsimp only [x]
    ring
  have hlogC : Real.log (2 * (K + 2 : ℝ)) ≤ 2 * K + 3 := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * (K + 2))
    linarith only [hh]
  let A : ℝ := 2 * (K + 2 : ℝ) * (n : ℝ) ^ (r * K)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hLA : Real.log A ≤ (4 * (r * K) + 2 * K + 3 : ℝ) * x := by
    dsimp only [A]
    rw [Real.log_mul (by positivity) (pow_pos hn0 _).ne', Real.log_pow]
    have hh := mul_le_mul_of_nonneg_left hln (Nat.cast_nonneg (r * K))
    have hC := mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℝ) ≤ 2 * K + 3)
    push_cast at hh ⊢
    nlinarith only [hh, hlogC, hC]
  have hxpow : (n : ℝ) ^ (1 / 2 : ℝ) = x ^ 2 := by
    dsimp only [x]
    rw [← Real.rpow_mul_natCast hn0.le]
    norm_num
  have hprod := mul_lt_mul_of_pos_right hlarge hx
  have hexp : Real.log A - (n : ℝ) ^ (1 / 2 : ℝ) / 12 < 0 := by
    rw [hxpow]
    nlinarith only [hLA, hprod]
  calc
    _ = Real.exp (Real.log A - (n : ℝ) ^ (1 / 2 : ℝ) / 12) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hA]
    _ < Real.exp 0 := Real.exp_lt_exp.mpr hexp
    _ = 1 := Real.exp_zero


theorem paper_reserve_sampling_tail_lt_one {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let K := q.choose (r + 1)
    2 * (K + 2 : ℝ) * (n : ℝ) ^ (r * K) *
      Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ) / 12)) < 1 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  apply typical_sampling_tail_lt_one hn1
  have hρ := paperRho_le_one_div_36 hqr
  exact (paper_reserve_tail_constant_lt_rpow hqr hn).trans_le
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))

end Arxiv2411_18291
