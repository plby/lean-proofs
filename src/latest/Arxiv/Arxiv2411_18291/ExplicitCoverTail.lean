import Arxiv.Arxiv2411_18291.ExplicitCoverSmallness

/-! # The finite probability margin for covering a sparse leave -/

namespace Arxiv2411_18291

theorem paper_cover_failure_lt_one {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let K := q.choose (r + 1)
    let a : ℝ := K * paperRho q (r + 1)
    (K : ℝ) * n.choose r *
      Real.exp (-((2 * (r + 1).factorial * (n : ℝ) ^ (-(3 * a)) * n /
        (n : ℝ) ^ (-a)) / 3)) < 1 := by
  dsimp only
  let K := q.choose (r + 1)
  let a : ℝ := K * paperRho q (r + 1)
  have hK : 1 ≤ K := Nat.choose_pos hqr.le
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have ha : a ≤ 1 / 36 := by simpa only [a, mul_comm] using paperRho_mul_choose_le hqr
  have hscale : 2 * ((r + 1).factorial : ℝ) * (n : ℝ) ^ (-(3 * a)) * n /
      (n : ℝ) ^ (-a) = 2 * (r + 1).factorial * (n : ℝ) ^ (1 - 2 * a) := by
    calc
      _ = 2 * ((r + 1).factorial : ℝ) *
          ((n : ℝ) ^ (-(3 * a)) / (n : ℝ) ^ (-a) * n) := by ring
      _ = _ := by
        rw [rpow_density_ratio hn0 a (3 * a), ← Real.rpow_add_one hn0.ne']
        congr 2
        ring
  have hpow := Real.rpow_le_rpow_of_exponent_le hn1 (show (1 / 2 : ℝ) ≤ 1 - 2 * a by
    linarith only [ha])
  have hfac : (1 : ℝ) ≤ (r + 1).factorial := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hfacpow := mul_le_mul_of_nonneg_right hfac
    (Real.rpow_nonneg (Nat.cast_nonneg n) (1 - 2 * a))
  have hexp : Real.exp (-(2 * (r + 1).factorial * (n : ℝ) ^ (1 - 2 * a) / 3)) ≤
      Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ) / 12)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hpow, hfacpow, Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 2 : ℝ)]
  have hrK : r ≤ r * K := by simpa using Nat.mul_le_mul_left r hK
  have hcount : (K : ℝ) * n.choose r ≤
      2 * (K + 2 : ℝ) * (n : ℝ) ^ (r * K) := by
    calc
      _ ≤ (K : ℝ) * (n : ℝ) ^ r := mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.choose_le_pow n r) (Nat.cast_nonneg K)
      _ ≤ (K : ℝ) * (n : ℝ) ^ (r * K) := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hn1 hrK) (Nat.cast_nonneg K)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by nlinarith only [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])
        (pow_nonneg (Nat.cast_nonneg n) _)
  change (K : ℝ) * n.choose r *
    Real.exp (-((2 * (r + 1).factorial * (n : ℝ) ^ (-(3 * a)) * n /
      (n : ℝ) ^ (-a)) / 3)) < 1
  rw [hscale]
  exact (mul_le_mul hcount hexp (Real.exp_pos _).le (by positivity)).trans_lt
    (paper_reserve_sampling_tail_lt_one hqr hn)

end Arxiv2411_18291
