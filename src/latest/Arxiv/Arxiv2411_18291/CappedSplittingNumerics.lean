import Arxiv.Arxiv2411_18291.CappedDecoderCapacity
import Arxiv.Arxiv2411_18291.PaperAlphaGrowth

/-! # The linear splitting cap at the paper's finite threshold -/

noncomputable section

namespace Arxiv2411_18291

theorem decoder_splitting_cap_coefficient {q r : ℕ} (hqr : r + 1 < q) :
    2 * (2 ^ q * (r + 1).factorial * (1 + q.choose (r + 1))) + 2 ≤
      (4 * q) ^ (q + 1) := by
  have hq : 2 ≤ q := by omega
  have hk : 1 + q.choose (r + 1) ≤ 2 * 2 ^ q := by
    have h1 : 1 ≤ 2 ^ q := one_le_pow₀ (by decide)
    have hh := Nat.choose_le_two_pow q (r + 1)
    omega
  have hf : (r + 1).factorial ≤ q ^ q :=
    (Nat.factorial_le hqr.le).trans (Nat.factorial_le_pow q)
  have hprod := Nat.mul_le_mul hf hk
  have hmain : 2 * (2 ^ q * (r + 1).factorial * (1 + q.choose (r + 1))) ≤
      4 * (4 * q) ^ q := by
    calc
      _ ≤ 2 * (2 ^ q * (q ^ q) * (2 * 2 ^ q)) := by
        nlinarith only [Nat.mul_le_mul_left (2 ^ q) hprod]
      _ = _ := by rw [mul_pow, show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]; ring
  have h1 : 1 ≤ (4 * q) ^ q := one_le_pow₀ (by omega)
  calc
    _ ≤ 6 * (4 * q) ^ q := by omega
    _ ≤ (4 * q) * (4 * q) ^ q := Nat.mul_le_mul_right _ (by omega)
    _ = _ := (pow_succ' _ _).symm

theorem decoder_splitting_cap_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    2 * ((2 ^ q * (r + 1).factorial * (1 + q.choose (r + 1)) : ℕ) : ℝ) *
        (n : ℝ) ^ (paperAlpha q (r + 1) / 10) + 2 ≤
      (n : ℝ) ^ (7 * paperAlpha q (r + 1) / 60) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hα := paperAlpha_pos hqr
  have hx : 1 ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10) :=
    Real.one_le_rpow hn1 (by positivity)
  have hc : (2 * (2 ^ q * (r + 1).factorial * (1 + q.choose (r + 1))) + 2 : ℕ) ≤
      (4 * q) ^ (q + 1) := decoder_splitting_cap_coefficient hqr
  have hcR : 2 * ((2 ^ q * (r + 1).factorial * (1 + q.choose (r + 1)) : ℕ) : ℝ) + 2 ≤
      (4 * q : ℝ) ^ (q + 1) := by exact_mod_cast hc
  have hg : (4 * q : ℝ) ^ (q + 1) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 60) := by
    have hh := paper_threshold_alpha_rpow_lower hqr hn (s := q + 1)
      (t := (1 / 60 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
    convert hh using 1
    congr 1
    ring
  calc
    _ ≤ (2 * ((2 ^ q * (r + 1).factorial * (1 + q.choose (r + 1)) : ℕ) : ℝ) + 2) *
        (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by linarith only [hx]
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 60) *
        (n : ℝ) ^ (paperAlpha q (r + 1) / 10) :=
      mul_le_mul_of_nonneg_right (hcR.trans hg) (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

end Arxiv2411_18291
