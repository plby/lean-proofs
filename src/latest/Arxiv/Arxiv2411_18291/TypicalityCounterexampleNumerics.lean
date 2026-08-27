import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Numerical bounds contradicting the printed exponential probability rate -/

namespace Arxiv2411_18291

theorem isolated_vertex_probability_gt_exp (n : ℕ) (hn : 2000 ≤ n) :
    Real.exp (-(n : ℝ) / 10) < (1 / 100 : ℝ) * (99 / 100 : ℝ) ^ (n - 1) := by
  have hp : Real.exp (-100) ≤ (1 / 100 : ℝ) := by
    rw [Real.exp_neg]
    apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 100)).mpr
    have hh := Real.add_one_le_exp (100 : ℝ)
    norm_num
    linarith only [hh]
  have hc : Real.exp (-(1 / 50 : ℝ)) ≤ (99 / 100 : ℝ) := by
    rw [Real.exp_neg]
    apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 99 / 100)).mpr
    have hh := Real.add_one_le_exp (1 / 50 : ℝ)
    norm_num
    linarith only [hh]
  have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hc (n - 1)
  have hprod := mul_le_mul hp hpow (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 100)
  rw [← Real.exp_nat_mul, ← Real.exp_add] at hprod
  apply lt_of_lt_of_le (Real.exp_lt_exp.mpr _) hprod
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hn' : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  linarith only [hn']

theorem typicality_counterexample_scales (n : ℕ) (hn : 1000000 ≤ n) :
    2 ^ (9 * 2 * 1) < n ∧
      (n : ℝ) ^ (-(1 / 2 : ℝ)) < (1 / 100 : ℝ) ∧
        (n : ℝ) ^ (-(1 / 10 : ℝ)) < 1 := by
  have hn' : (1000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hn']
  have hroot : (100 : ℝ) < Real.sqrt n :=
    (Real.lt_sqrt (by norm_num)).mpr (by nlinarith only [hn'])
  refine ⟨by norm_num; omega, ?_,
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith only [hn']) (by norm_num)⟩
  rw [Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow]
  apply (inv_lt_comm₀ (Real.sqrt_pos.mpr hn0) (by norm_num : (0 : ℝ) < 1 / 100)).mpr
  norm_num
  exact hroot

end Arxiv2411_18291
