import Arxiv.Arxiv2411_18291.PaperSizeParameters

/-! # Finite density estimates above the printed size threshold -/

noncomputable section

namespace Arxiv2411_18291

theorem paper_threshold_scaled_rpow_le {q r n : ℕ} (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    (n : ℝ) ^ (-(paperAlpha q r * t)) ≤ (4 * q : ℝ) ^ (-(90 * q * t)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hb : (0 : ℝ) < 4 * q := by positivity
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (paperSizeThreshold q r))
    (by exact_mod_cast hn : (paperSizeThreshold q r : ℝ) ≤ n) (paperAlpha_pos hqr).le
  rw [paperSizeThreshold_rpow_alpha hqr] at hpow
  have hneg := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hb _) hpow
    (neg_nonpos.mpr ht)
  rw [← Real.rpow_mul (Nat.cast_nonneg n), ← Real.rpow_mul hb.le] at hneg
  simpa only [mul_neg] using hneg

theorem paper_threshold_decay_le_half_boost {q r n : ℕ} (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) :
    (n : ℝ) ^ (-(paperAlpha q r / 4)) ≤ boostComplementBound q / 2 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hb : (1 : ℝ) ≤ 4 * q := by linarith
  have hfirst := paper_threshold_scaled_rpow_le hqr hn (t := 1 / 4) (by norm_num)
  have hexp : -(90 * (q : ℝ) * (1 / 4)) ≤ -((3 * q + 1 : ℕ) : ℝ) := by
    push_cast
    linarith only [hq]
  have hbase : (2 : ℝ) ≤ 4 * q := by linarith
  calc
    _ = (n : ℝ) ^ (-(paperAlpha q r * (1 / 4))) := by congr 1; ring
    _ ≤ (4 * q : ℝ) ^ (-(90 * (q : ℝ) * (1 / 4))) := hfirst
    _ ≤ (4 * q : ℝ) ^ (-((3 * q + 1 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hb hexp
    _ ≤ (2 : ℝ) ^ (-((3 * q + 1 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hbase (neg_nonpos.mpr (Nat.cast_nonneg _))
    _ = _ := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, pow_succ]
      unfold boostComplementBound
      rw [mul_inv_rev]
      ring

theorem paper_threshold_reserve_absorber_density {q r n : ℕ} (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) :
    (n : ℝ) ^ (-paperRho q r) + (n : ℝ) ^ (-(paperAlpha q r / 4)) ≤
      boostComplementBound q := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hexp : -paperRho q r ≤ -(paperAlpha q r / 4) := by
    have hα := paperAlpha_pos hqr
    have hαρ := paperAlpha_le_rho hqr
    linarith only [hα, hαρ]
  have hrho := Real.rpow_le_rpow_of_exponent_le hn1 hexp
  have hhalf := paper_threshold_decay_le_half_boost hqr hn
  linarith only [hrho, hhalf]

theorem paper_density_above_greedy_floor {q r n : ℕ} (hqr : r < q) (hn : 1 < n)
    {γ : ℝ} (hγ : γ ≤ paperRho q r) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) < (n : ℝ) ^ (-γ) := by
  apply Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hn : (1 : ℝ) < n)
  have hρ := paperRho_le_one_div_36 hqr
  linarith only [hγ, hρ]

end Arxiv2411_18291
