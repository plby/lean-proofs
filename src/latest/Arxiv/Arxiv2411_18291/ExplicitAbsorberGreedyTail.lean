import Arxiv.Arxiv2411_18291.ExplicitBoostTail

/-! # A uniform finite failure bound for the absorber's greedy placements -/

namespace Arxiv2411_18291

theorem absorber_greedy_failure_lt_stretched_exp {q r n M : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hM : M ≤ n) {θ : ℝ}
    (hθ : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ) :
    (M : ℝ) * n.choose r *
      Real.exp (-(2 * (r + 1).factorial * θ * n / 3)) <
        Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hMreal : (M : ℝ) ≤ n := by exact_mod_cast hM
  have hpref : (M : ℝ) * n.choose r ≤ 6 * (n : ℝ) ^ (r + 1) := by
    calc
      _ ≤ (n : ℝ) * (n : ℝ) ^ r := mul_le_mul hMreal
        (by exact_mod_cast Nat.choose_le_pow n r) (Nat.cast_nonneg _) hn0.le
      _ = (n : ℝ) ^ (r + 1) := by rw [pow_succ]; ring
      _ ≤ _ := le_mul_of_one_le_left (pow_nonneg hn0.le _) (by norm_num)
  have hscale : (n : ℝ) ^ (1 / 2 : ℝ) ≤ θ * n := by
    have hh := mul_le_mul_of_nonneg_right hθ hn0.le
    rw [← Real.rpow_add_one hn0.ne'] at hh
    norm_num at hh
    exact hh
  have hboost := (boost_threshold_le_paper_threshold hqr).trans hn
  have hq : 2 ≤ q := by omega
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have htwo : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) := by
    have hg := boost_threshold_rpow_lower (s := 1) hq hboost
      (by norm_num : (0 : ℝ) ≤ 1 / 10) (by linarith only [hqR])
    simp only [pow_one] at hg
    linarith only [hqR, hg]
  have hhalf : 2 * (n : ℝ) ^ (2 / 5 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 10 : ℝ) * (n : ℝ) ^ (2 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num
  have hpow := Real.rpow_le_rpow_of_exponent_le hn1
    (by norm_num : (1 / 10 : ℝ) ≤ 2 / 5)
  have hθn : 0 ≤ θ * n := (Real.rpow_nonneg hn0.le (1 / 2 : ℝ)).trans hscale
  have hfac : (1 : ℝ) ≤ (r + 1).factorial := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hfacmul := mul_le_mul_of_nonneg_right hfac hθn
  have hexp : Real.exp (-(2 * (r + 1).factorial * θ * n / 3)) ≤
      Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ) / 12)) *
        Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hscale, hhalf, hpow, hfacmul,
      Real.rpow_nonneg hn0.le (2 / 5 : ℝ)]
  calc
    _ ≤ (6 * (n : ℝ) ^ (r + 1)) *
        (Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ) / 12)) *
          Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ)))) :=
      mul_le_mul hpref hexp (Real.exp_pos _).le (by positivity)
    _ = (6 * (n : ℝ) ^ (r + 1) * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ) / 12))) *
        Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) := by ring
    _ < 1 * Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) :=
      mul_lt_mul_of_pos_right (boost_sampling_tail_lt_one hq hqr.le hboost) (Real.exp_pos _)
    _ = _ := one_mul _

theorem absorber_greedy_failure_lt_one {q r n M : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hM : M ≤ n) {θ : ℝ}
    (hθ : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ) :
    (M : ℝ) * n.choose r *
      Real.exp (-(2 * (r + 1).factorial * θ * n / 3)) < 1 := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  exact (absorber_greedy_failure_lt_stretched_exp hqr hn hM hθ).trans
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.rpow_pos_of_pos hn0 _)))

end Arxiv2411_18291
