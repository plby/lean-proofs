import Arxiv.Arxiv2411_18291.FiniteModularHostNumerics
import Arxiv.Arxiv2411_18291.ShiftedChooseBounds

/-! # Finite binomial and counting errors for joint permutation probabilities -/

namespace Arxiv2411_18291

theorem paper_quadratic_size_margin {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) {β : ℝ}
    (hβ : paperAlpha q (r + 1) ≤ β) :
    2 * (q : ℝ) ^ 2 ≤ (n : ℝ) ^ β := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 2)
    (t := 1) (by norm_num) (by push_cast; linarith only [hq])
  simp only [mul_one] at hg
  have hc : 2 * (q : ℝ) ^ 2 ≤ (4 * q : ℝ) ^ 2 := by nlinarith only [sq_nonneg (q : ℝ)]
  exact (hc.trans hg).trans (Real.rpow_le_rpow_of_exponent_le hn1 hβ)

theorem uniform_shifted_choose_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) {κ : ℝ}
    (hκ : paperAlpha q (r + 1) + κ ≤ 1) :
    ∀ a ≤ q, ∀ b ≤ q,
      (1 - (n : ℝ) ^ (-κ)) * (n : ℝ) ^ b / b.factorial ≤ ((n - a).choose b : ℝ) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hα := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hnsize : 2 * q ≤ n := by
    have hh := paper_quadratic_size_margin hqr hn (by linarith only [hα] :
      paperAlpha q (r + 1) ≤ 1)
    rw [Real.rpow_one] at hh
    have hh' : (2 * q : ℝ) ≤ n := by nlinarith only [hh, hq]
    exact_mod_cast hh'
  have hmargin := paper_quadratic_size_margin hqr hn
    (by linarith only [hκ] : paperAlpha q (r + 1) ≤ 1 - κ)
  intro a ha b hb
  apply shifted_choose_relative_lower n a b (Real.rpow_nonneg hn0.le _) (by omega)
  have haR : (a : ℝ) ≤ q := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ q := by exact_mod_cast hb
  have hm := mul_le_mul hbR (add_le_add haR hbR) (by positivity) (Nat.cast_nonneg q)
  have hcoef : (b : ℝ) * (a + b) ≤ 2 * (q : ℝ) ^ 2 := by nlinarith only [hm]
  have heq : (n : ℝ) ^ (-κ) * n = (n : ℝ) ^ (1 - κ) := by
    rw [← Real.rpow_add_one hn0.ne']
    congr 1
    ring
  rw [heq]
  exact hcoef.trans hmargin

theorem paper_sixth_alpha_error_small {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (n : ℝ) ^ (-(paperAlpha q (r + 1) / 6)) ≤ 1 / 2 := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 1)
    (t := (1 / 6 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
  have hb : (2 : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 6) := by
    have hc : (2 : ℝ) ≤ (4 * q : ℝ) ^ 1 := by
      simp only [pow_one]
      linarith only [hq]
    simpa only [div_eq_mul_inv, one_mul] using hc.trans hg
  have hh := mul_le_mul_of_nonneg_right hb
    (Real.rpow_nonneg hn0.le (-(paperAlpha q (r + 1) / 6)))
  rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] at hh
  linarith only [hh]

end Arxiv2411_18291
