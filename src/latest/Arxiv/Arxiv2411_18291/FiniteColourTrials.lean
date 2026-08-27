import Arxiv.Arxiv2411_18291.AmplificationNumerics
import Arxiv.Arxiv2411_18291.PaperAlphaGrowth

/-! # An explicit colour repetition count that handles every root at n0 -/

noncomputable section

namespace Arxiv2411_18291

def paperColourTrialCount (q r f : ℕ) : ℕ := 48 * (f + 1) * paperInverseAlpha q r

theorem paperColourTrialCount_pos {q r : ℕ} (hqr : r < q) (f : ℕ) :
    0 < paperColourTrialCount q r f := by
  have hA := paperInverseAlpha_pos hqr
  unfold paperColourTrialCount
  positivity

theorem paperColourTrialCount_exponent {q r : ℕ} (hqr : r < q) (f : ℕ) :
    (paperAlpha q r / 48) * paperColourTrialCount q r f = (f : ℝ) + 1 := by
  unfold paperColourTrialCount
  push_cast
  calc
    _ = ((f : ℝ) + 1) * (paperAlpha q r * paperInverseAlpha q r) := by ring
    _ = _ := by rw [paperAlpha_mul_inverse hqr, mul_one]

theorem colour_single_trial_failure_scale_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 48)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 1)
    (t := (1 / 48 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
  have hc : (8 : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 48) := by
    have hh : (8 : ℝ) ≤ (4 * q : ℝ) ^ 1 := by
      simp only [pow_one]
      linarith only [hq]
    simpa only [div_eq_mul_inv, one_mul] using hh.trans hg
  calc
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 48) *
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

theorem colour_single_trial_failure_thirty_second_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 32)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 1)
    (t := (1 / 96 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
  have hc : (8 : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 96) := by
    have hh : (8 : ℝ) ≤ (4 * q : ℝ) ^ 1 := by
      simp only [pow_one]
      linarith only [hq]
    simpa only [div_eq_mul_inv, one_mul] using hh.trans hg
  calc
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 96) *
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

theorem colour_trial_union_bound_le_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (f : ℕ) :
    (n : ℝ) ^ f * (8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) ^
      paperColourTrialCount q (r + 1) f ≤ (n : ℝ) ^ (-1 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hb := colour_single_trial_failure_scale_paper_threshold hqr hn
  have hexp : (f : ℝ) + (-(paperAlpha q (r + 1) / 48)) *
      paperColourTrialCount q (r + 1) f = -1 := by
    have hh := paperColourTrialCount_exponent hqr f
    linarith only [hh]
  calc
    _ ≤ (n : ℝ) ^ f * ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 48))) ^
        paperColourTrialCount q (r + 1) f :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) (pow_nonneg hn0.le _)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_natCast (n : ℝ) f,
        ← Real.rpow_add hn0, hexp]

theorem colour_trial_union_bound_square_paper_threshold {q r n f : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hf : 1 ≤ f) :
    (n : ℝ) ^ f * (8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) ^
      paperColourTrialCount q (r + 1) f ≤ (n : ℝ) ^ (-2 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hb := colour_single_trial_failure_thirty_second_paper_threshold hqr hn
  have hexp : (f : ℝ) + (-(paperAlpha q (r + 1) / 32)) *
      paperColourTrialCount q (r + 1) f ≤ -2 := by
    have hh := paperColourTrialCount_exponent hqr f
    have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
    nlinarith only [hh, hfR]
  calc
    _ ≤ (n : ℝ) ^ f * ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 32))) ^
        paperColourTrialCount q (r + 1) f :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) (pow_nonneg hn0.le _)
    _ = (n : ℝ) ^ ((f : ℝ) + (-(paperAlpha q (r + 1) / 32)) *
        paperColourTrialCount q (r + 1) f) := by
      rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_natCast (n : ℝ) f,
        ← Real.rpow_add hn0]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hexp

theorem colour_trial_union_bound_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (f : ℕ) :
    (n : ℝ) ^ f * (8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) ^
      paperColourTrialCount q (r + 1) f < 1 := by
  have hn1 : (1 : ℝ) < n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).trans_le hn
  exact (colour_trial_union_bound_le_paper_threshold hqr hn f).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg hn1 (by norm_num))

def paperCommonColourTrialCount (q r : ℕ) : ℕ := 60 * q * paperInverseAlpha q r

theorem colour_single_trial_failure_twenty_seventh_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 27)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 1)
    (t := (1 / 216 : ℝ)) (by norm_num) (by push_cast; linarith only [hqR])
  have hc : (8 : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 216) := by
    have hh : (8 : ℝ) ≤ (4 * q : ℝ) ^ 1 := by
      simp only [pow_one]
      linarith only [hqR]
    simpa only [div_eq_mul_inv, one_mul] using hh.trans hg
  calc
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 216) *
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

theorem common_colour_trial_union_bound_paper_threshold {q r n f : ℕ}
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hf : f ≤ 2 * q - 1) :
    (n : ℝ) ^ f * (8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) ^
      paperCommonColourTrialCount q (r + 1) ≤ (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hb := colour_single_trial_failure_twenty_seventh_paper_threshold hqr hq hn
  have hexact : (paperAlpha q (r + 1) / 27) * paperCommonColourTrialCount q (r + 1) =
      (20 / 9 : ℝ) * q := by
    unfold paperCommonColourTrialCount
    push_cast
    calc
      _ = (20 / 9 : ℝ) * q * (paperAlpha q (r + 1) * paperInverseAlpha q (r + 1)) := by
        ring
      _ = _ := by rw [paperAlpha_mul_inverse hqr, mul_one]
  have hexp : (f : ℝ) + (-(paperAlpha q (r + 1) / 27)) *
      paperCommonColourTrialCount q (r + 1) ≤ -(5 / 3 : ℝ) := by
    have hfR : (f : ℝ) ≤ 2 * q - 1 := by
      have hh : (f : ℝ) + 1 ≤ 2 * q := by
        exact_mod_cast (show f + 1 ≤ 2 * q by omega)
      linarith only [hh]
    have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith only [hfR, hqR, hexact]
  calc
    _ ≤ (n : ℝ) ^ f * ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 27))) ^
        paperCommonColourTrialCount q (r + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) (pow_nonneg hn0.le _)
    _ = (n : ℝ) ^ ((f : ℝ) + (-(paperAlpha q (r + 1) / 27)) *
        paperCommonColourTrialCount q (r + 1)) := by
      rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_natCast (n : ℝ) f,
        ← Real.rpow_add hn0]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hexp

end Arxiv2411_18291
