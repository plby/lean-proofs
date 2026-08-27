import Arxiv.Arxiv2411_18291.ExplicitNibbleGrowth

/-! # The finite simultaneous nibble failure estimate -/

namespace Arxiv2411_18291

theorem paper_nibble_tail_tenth_lt_one {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) :
    5 * (n : ℝ) ^ (2 * r) * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) < 1 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  let x : ℝ := (n : ℝ) ^ (1 / 20 : ℝ)
  have hx : 0 < x := Real.rpow_pos_of_pos hn0 _
  have hx1 : 1 ≤ x := Real.one_le_rpow hn1 (by norm_num)
  have hlarge : (40 * r + 4 : ℝ) < x := by
    have hnum := paper_threshold_nibble_monomial (C := 50) (i := 1) (j := 0)
      (d := 0) hr hqr hn (by norm_num) (by norm_num) (by norm_num) (by omega)
    simp only [pow_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
      Nat.cast_ofNat, mul_one] at hnum
    have hρ := paperRho_le_one_div_36 hqr
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1
      (show paperRho q r ≤ 1 / 20 by linarith only [hρ])
    have hqR : (r : ℝ) < q := by exact_mod_cast hqr
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    exact (by linarith only [hqR, hrR] : (40 * r + 4 : ℝ) < 50 * q).trans_le
      (hnum.trans hpow)
  have hln : Real.log (n : ℝ) ≤ 20 * x := by
    have hh := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 20)
    convert hh using 1
    dsimp only [x]
    ring
  have hlog5 : Real.log 5 ≤ 4 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    norm_num at hh ⊢
    exact hh
  let A : ℝ := 5 * (n : ℝ) ^ (2 * r)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hLA : Real.log A ≤ (40 * r + 4 : ℝ) * x := by
    dsimp only [A]
    rw [Real.log_mul (by norm_num) (pow_pos hn0 _).ne', Real.log_pow]
    have hh := mul_le_mul_of_nonneg_left hln (Nat.cast_nonneg (2 * r))
    push_cast at hh ⊢
    nlinarith only [hh, hlog5, hx1]
  have hxpow : (n : ℝ) ^ (1 / 10 : ℝ) = x ^ 2 := by
    dsimp only [x]
    rw [← Real.rpow_mul_natCast hn0.le]
    norm_num
  have hprod := mul_lt_mul_of_pos_right hlarge hx
  have hexp : Real.log A - (n : ℝ) ^ (1 / 10 : ℝ) < 0 := by
    rw [hxpow]
    nlinarith only [hLA, hprod]
  calc
    _ = Real.exp (Real.log A - (n : ℝ) ^ (1 / 10 : ℝ)) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hA]
    _ < Real.exp 0 := Real.exp_lt_exp.mpr hexp
    _ = 1 := Real.exp_zero

theorem paper_nibble_tail_lt_one_of_exponent {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) {χ : ℝ} (hχ : 1 / 10 ≤ χ) :
    5 * (n : ℝ) ^ (2 * r) * Real.exp (-((n : ℝ) ^ χ)) < 1 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have he := Real.exp_le_exp.mpr
    (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hn1 hχ))
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_lt
    (paper_nibble_tail_tenth_lt_one hr hqr hn)

theorem paper_nibble_tail_lt_one {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) :
    5 * (n : ℝ) ^ (2 * r) * Real.exp (-((n : ℝ) ^ (1 / 6 : ℝ))) < 1 :=
  paper_nibble_tail_lt_one_of_exponent hr hqr hn (by norm_num)

end Arxiv2411_18291
