import Arxiv.Arxiv2411_18291.PaperSizeParameters

/-! # Finite growth at multiples of the absorber exponent -/

namespace Arxiv2411_18291

theorem paper_threshold_rpow_lower {q r n s : ℕ} (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) {t : ℝ} (ht : 0 ≤ t)
    (hs : (s : ℝ) ≤ ((90 * q * paperInverseAlpha q r : ℕ) : ℝ) * t) :
    (4 * q : ℝ) ^ s ≤ (n : ℝ) ^ t := by
  have hb : (1 : ℝ) ≤ 4 * q := by exact_mod_cast (show 1 ≤ 4 * q by omega)
  have hg := Real.rpow_le_rpow (Nat.cast_nonneg (paperSizeThreshold q r))
    (by exact_mod_cast hn : (paperSizeThreshold q r : ℝ) ≤ n) ht
  rw [paperSizeThreshold, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)] at hg
  push_cast at hg
  have hs' : (s : ℝ) ≤ (90 * q * paperInverseAlpha q r : ℝ) * t := by
    exact_mod_cast hs
  exact (Real.rpow_natCast _ s).symm.trans_le
    ((Real.rpow_le_rpow_of_exponent_le hb hs').trans hg)

theorem paper_threshold_alpha_rpow_lower {q r n s : ℕ} (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) {t : ℝ} (ht : 0 ≤ t)
    (hs : (s : ℝ) ≤ (90 * q : ℝ) * t) :
    (4 * q : ℝ) ^ s ≤ (n : ℝ) ^ (paperAlpha q r * t) := by
  have hb : (1 : ℝ) ≤ 4 * q := by exact_mod_cast (show 1 ≤ 4 * q by omega)
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (paperSizeThreshold q r))
    (by exact_mod_cast hn : (paperSizeThreshold q r : ℝ) ≤ n) (paperAlpha_pos hqr).le
  rw [paperSizeThreshold_rpow_alpha hqr] at hpow
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hpow ht
  rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (Nat.cast_nonneg n)] at hh
  exact (Real.rpow_natCast _ s).symm.trans_le
    ((Real.rpow_le_rpow_of_exponent_le hb hs).trans hh)

theorem paper_threshold_alpha_third {q r n : ℕ} (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) :
    (4 * q : ℝ) ^ (30 * q) ≤ (n : ℝ) ^ (paperAlpha q r / 3) := by
  have hh := paper_threshold_alpha_rpow_lower (s := 30 * q) hqr hn
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by push_cast; linarith)
  convert hh using 1
  congr 1
  ring

end Arxiv2411_18291
