import Arxiv.Arxiv2411_18291.ExclusiveColourTrials
import Arxiv.Arxiv2411_18291.FiniteColourPaletteBudget

/-! # Joint colour amplification for all ranks with twice the printed palette -/

noncomputable section

namespace Arxiv2411_18291

def correctedCommonColourTrialCount (q r : ℕ) : ℕ := 80 * q * paperInverseAlpha q r

theorem corrected_common_colour_trials_fit_palette {q r m M : ℕ}
    (hq : 2 ≤ q) (hm : m ≤ M) :
    correctedCommonColourTrialCount q r * m ≤ correctedColourPaletteSize q r M := by
  have hc : 80 * q ≤ 40 * q ^ 2 := by nlinarith only [hq]
  exact Nat.mul_le_mul (Nat.mul_le_mul_right (paperInverseAlpha q r) hc) hm

theorem corrected_common_colour_trial_union_bound {q r n f : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hf : f ≤ 2 * q - 1) :
    (n : ℝ) ^ f * (8 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) ^
      correctedCommonColourTrialCount q (r + 1) ≤ (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hb := colour_single_trial_failure_thirty_second_paper_threshold hqr hn
  have hexact : (paperAlpha q (r + 1) / 32) *
      correctedCommonColourTrialCount q (r + 1) = (5 / 2 : ℝ) * q := by
    unfold correctedCommonColourTrialCount
    push_cast
    calc
      _ = (5 / 2 : ℝ) * q * (paperAlpha q (r + 1) * paperInverseAlpha q (r + 1)) := by
        ring
      _ = _ := by rw [paperAlpha_mul_inverse hqr, mul_one]
  have hexp : (f : ℝ) + (-(paperAlpha q (r + 1) / 32)) *
      correctedCommonColourTrialCount q (r + 1) ≤ -(5 / 3 : ℝ) := by
    have hfR : (f : ℝ) + 1 ≤ 2 * q := by
      exact_mod_cast (show f + 1 ≤ 2 * q by omega)
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    nlinarith only [hfR, hqR, hexact]
  calc
    _ ≤ (n : ℝ) ^ f * ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 32))) ^
        correctedCommonColourTrialCount q (r + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) (pow_nonneg hn0.le _)
    _ = (n : ℝ) ^ ((f : ℝ) + (-(paperAlpha q (r + 1) / 32)) *
        correctedCommonColourTrialCount q (r + 1)) := by
      rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_natCast (n : ℝ) f,
        ← Real.rpow_add hn0]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hexp

theorem exclusive_colour_single_trial_failure_thirty_sixth {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    33 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 36)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 2)
    (t := (1 / 72 : ℝ)) (by norm_num) (by push_cast; linarith only [hqR])
  have hc : (33 : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 72) := by
    have hh : (33 : ℝ) ≤ (4 * q : ℝ) ^ 2 := by nlinarith only [hqR]
    simpa only [div_eq_mul_inv, one_mul] using hh.trans hg
  calc
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 72) *
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

theorem corrected_exclusive_colour_trial_union_bound {q r n f : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hf : f ≤ q - 1) :
    (n : ℝ) ^ f * (33 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24))) ^
      correctedCommonColourTrialCount q (r + 1) ≤ (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hb := exclusive_colour_single_trial_failure_thirty_sixth hqr hn
  have hexact : (paperAlpha q (r + 1) / 36) *
      correctedCommonColourTrialCount q (r + 1) = (20 / 9 : ℝ) * q := by
    unfold correctedCommonColourTrialCount
    push_cast
    calc
      _ = (20 / 9 : ℝ) * q * (paperAlpha q (r + 1) * paperInverseAlpha q (r + 1)) := by
        ring
      _ = _ := by rw [paperAlpha_mul_inverse hqr, mul_one]
  have hexp : (f : ℝ) + (-(paperAlpha q (r + 1) / 36)) *
      correctedCommonColourTrialCount q (r + 1) ≤ -(5 / 3 : ℝ) := by
    have hfR : (f : ℝ) + 1 ≤ q := by exact_mod_cast (show f + 1 ≤ q by omega)
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    nlinarith only [hfR, hqR, hexact]
  calc
    _ ≤ (n : ℝ) ^ f * ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 36))) ^
        correctedCommonColourTrialCount q (r + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) (pow_nonneg hn0.le _)
    _ = (n : ℝ) ^ ((f : ℝ) + (-(paperAlpha q (r + 1) / 36)) *
        correctedCommonColourTrialCount q (r + 1)) := by
      rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_natCast (n : ℝ) f,
        ← Real.rpow_add hn0]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hexp

end Arxiv2411_18291
