import Arxiv.Arxiv2411_18291.PaperParameterMargins
import Arxiv.Arxiv2411_18291.PaperAlphaGrowth
import Arxiv.Arxiv2411_18291.ExplicitReserveTail

/-! # Typicality budgets through the full exchange configuration size -/

namespace Arxiv2411_18291

theorem paper_host_configuration_growth {q r n h : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    (4 * q : ℝ) ^ (10 * (q + h)) ≤ (n : ℝ) ^ (1 / 40 : ℝ) := by
  have h12 : 12 * h ≤ paperInverseAlpha q (r + 1) :=
    twelve_mul_configuration_le_inverseAlpha q (r + 1) h hH
  have hA : 12 ≤ paperInverseAlpha q (r + 1) := by omega
  have hqA := Nat.mul_le_mul_left q hA
  have hAh : 12 * h ≤ q * paperInverseAlpha q (r + 1) :=
    h12.trans (Nat.le_mul_of_pos_left _ (by omega : 0 < q))
  have hs : 40 * (10 * (q + h)) ≤ 90 * q * paperInverseAlpha q (r + 1) := by
    nlinarith only [hqA, hAh]
  apply paper_threshold_rpow_lower hqr hn (by norm_num : (0 : ℝ) ≤ 1 / 40)
  have hsR : (40 : ℝ) * (10 * (q + h) : ℕ) ≤
      (90 * q * paperInverseAlpha q (r + 1) : ℕ) := by exact_mod_cast hs
  linarith only [hsR]

theorem paper_host_typicality_normalization {q r n h : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    (4 + 2 * h * 2 ^ h : ℝ) * (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hC4 : (4 * (4 + 2 * h * 2 ^ h) : ℝ) ≤ (4 * q : ℝ) ^ (10 * (q + h)) := by
    exact_mod_cast reserve_normalization_constant_le (K := h) (by omega : 2 ≤ q)
  have hC : (4 + 2 * h * 2 ^ h : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) := by
    have hc : (0 : ℝ) ≤ 2 * h * 2 ^ h := by positivity
    exact (show (4 + 2 * h * 2 ^ h : ℝ) ≤ 4 * (4 + 2 * h * 2 ^ h) by
      linarith only [hc]).trans (hC4.trans (paper_host_configuration_growth hqr hn hh hH))
  calc
    _ ≤ (n : ℝ) ^ (1 / 40 : ℝ) * (n : ℝ) ^ (-(1 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; norm_num

theorem paper_host_sampling_tail_lt_one {q r n h : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
      Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ) / 12)) < 1 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  apply typical_sampling_tail_lt_one hn1
  have hconst : (48 * (r * h) + 24 * h + 36 : ℝ) <
      (4 * q : ℝ) ^ (10 * (q + h)) := by
    exact_mod_cast reserve_tail_constant_lt (by omega : 2 ≤ q) hh (by omega : r ≤ q)
  exact (hconst.trans_le (paper_host_configuration_growth hqr hn hh hH)).trans_le
    (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1 / 40 : ℝ) ≤ 1 / 4))

end Arxiv2411_18291
