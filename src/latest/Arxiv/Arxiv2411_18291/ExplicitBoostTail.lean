import Arxiv.Arxiv2411_18291.ExplicitBoostSize

/-! # The finite exponential tail estimate needed for Boost sampling -/

namespace Arxiv2411_18291

theorem boost_tail_constant_lt_rpow {q n r : ℕ} (hq : 2 ≤ q) (hr : r ≤ q)
    (hn : (4 * q) ^ (90 * q) ≤ n) :
    (240 * r + 60 : ℝ) < (n : ℝ) ^ (1 / 20 : ℝ) := by
  have hq3 : 8 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hC : 240 * r + 60 ≤ (4 * q) ^ 4 := by
    calc
      _ ≤ 2048 * q := by omega
      _ ≤ (256 * q ^ 3) * q := by
        have hh := Nat.mul_le_mul_right q (Nat.mul_le_mul_left 256 hq3)
        nlinarith only [hh]
      _ = _ := by ring
  have hgap : (4 * q) ^ 4 < (4 * q) ^ (4 * q) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have hh : (240 * r + 60 : ℝ) < (4 * q : ℝ) ^ (4 * q) := by
    exact_mod_cast hC.trans_lt hgap
  have hpow := boost_threshold_rpow_lower (s := 4 * q) hq hn
    (by norm_num : (0 : ℝ) ≤ 1 / 20)
    (by push_cast; nlinarith only [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
  exact hh.trans_le hpow

theorem boost_sampling_tail_lt_one {q n r : ℕ} (hq : 2 ≤ q) (hr : r ≤ q)
    (hn : (4 * q) ^ (90 * q) ≤ n) :
    6 * (n : ℝ) ^ r * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ) / 12)) < 1 := by
  have hn1 : 1 ≤ n := by
    have hh := (boost_threshold_root_size_bounds hq hn).2.2
    omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  let x : ℝ := (n : ℝ) ^ (1 / 20 : ℝ)
  have hx : 0 < x := Real.rpow_pos_of_pos hn0 _
  have hx1 : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast hn1) (by norm_num)
  have hln : Real.log (n : ℝ) ≤ 20 * x := by
    have hh := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 20)
    convert hh using 1
    dsimp only [x]
    ring
  have hlog6 : Real.log 6 ≤ 5 := by
    calc
      _ ≤ 6 - 1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
      _ = 5 := by norm_num
  let A : ℝ := 6 * (n : ℝ) ^ r
  have hA : 0 < A := by dsimp only [A]; positivity
  have hLA : Real.log A ≤ (20 * r + 5 : ℝ) * x := by
    dsimp only [A]
    rw [Real.log_mul (by norm_num) (pow_pos hn0 r).ne', Real.log_pow]
    have hh := mul_le_mul_of_nonneg_left hln (Nat.cast_nonneg r)
    nlinarith only [hh, hlog6, hx1]
  have hxpow : (n : ℝ) ^ (1 / 10 : ℝ) = x ^ 2 := by
    dsimp only [x]
    rw [← Real.rpow_mul_natCast hn0.le]
    norm_num
  have hprod := mul_lt_mul_of_pos_right (boost_tail_constant_lt_rpow hq hr hn) hx
  change (240 * r + 60 : ℝ) * x < x * x at hprod
  have hexp : Real.log A - (n : ℝ) ^ (1 / 10 : ℝ) / 12 < 0 := by
    rw [hxpow]
    nlinarith only [hLA, hprod]
  calc
    _ = Real.exp (Real.log A - (n : ℝ) ^ (1 / 10 : ℝ) / 12) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hA]
    _ < Real.exp 0 := Real.exp_lt_exp.mpr hexp
    _ = 1 := Real.exp_zero

end Arxiv2411_18291
