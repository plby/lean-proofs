import Arxiv.Arxiv2411_18291.ReserveThresholdConstants
import Arxiv.Arxiv2411_18291.ReserveExistence

/-! # The finite numerical criteria for the reserve -/

namespace Arxiv2411_18291

theorem paper_reserve_tail_constant_lt_rpow {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (48 * (r * q.choose (r + 1)) + 24 * q.choose (r + 1) + 36 : ℝ) <
      (n : ℝ) ^ paperRho q (r + 1) := by
  have hconst := reserve_tail_constant_lt (K := q.choose (r + 1))
    (by omega : 2 ≤ q) (Nat.choose_pos hqr.le) (by omega : r ≤ q)
  calc
    _ < (4 * q : ℝ) ^ (10 * (q + q.choose (r + 1))) := by exact_mod_cast hconst
    _ ≤ _ := paper_threshold_reserve_growth hqr hn

theorem paper_reserve_normalization {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (4 + 2 * q.choose (r + 1) * 2 ^ q.choose (r + 1) : ℝ) *
      (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ 1 / 4 := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hconst := reserve_normalization_constant_le (K := q.choose (r + 1))
    (by omega : 2 ≤ q)
  have hρ := paperRho_le_one_div_36 hqr
  have hh : (4 * (4 + 2 * q.choose (r + 1) * 2 ^ q.choose (r + 1)) : ℝ) ≤
      (n : ℝ) ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ (4 * q : ℝ) ^ (10 * (q + q.choose (r + 1))) := by exact_mod_cast hconst
      _ ≤ _ := paper_threshold_reserve_growth_le_rpow hqr hn (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hh
    (Real.rpow_nonneg (Nat.cast_nonneg n) (-(1 / 8 : ℝ)))
  rw [← Real.rpow_add hnpos] at hmul
  norm_num at hmul
  linarith only [hmul]

theorem paper_reserve_size_numerics {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let K := q.choose (r + 1)
    let ρ := paperRho q (r + 1)
    let z := (n : ℝ) ^ (-ρ)
    (q : ℝ) ≤ (n : ℝ) * (z / 8) ^ K / 4 ∧
      z * 2 ^ (q - (r + 1)) * 8 ^ (K - 1) * (q - (r + 1)).factorial ≤ 1 := by
  dsimp only
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hρ := paperRho_le_one_div_36 hqr
  have hρK := paperRho_mul_choose_le hqr
  have hsize := reserve_size_constant_le (K := q.choose (r + 1)) (by omega : 2 ≤ q)
  have hcount := reserve_count_loss_constant_le (K := q.choose (r + 1))
    (by omega : 2 ≤ q) (Nat.sub_le q (r + 1))
  constructor
  · rw [reserve_size_scale hnpos]
    apply (le_div_iff₀ (by positivity)).mpr
    have hh : (4 * q * 8 ^ q.choose (r + 1) : ℝ) ≤
        (n : ℝ) ^ (1 - paperRho q (r + 1) * q.choose (r + 1)) := by
      calc
        _ ≤ (4 * q : ℝ) ^ (10 * (q + q.choose (r + 1))) := by exact_mod_cast hsize
        _ ≤ _ := paper_threshold_reserve_growth_le_rpow hqr hn (by linarith)
    nlinarith only [hh]
  · have hh : (2 ^ (q - (r + 1)) * 8 ^ (q.choose (r + 1) - 1) *
        (q - (r + 1)).factorial : ℝ) ≤ (n : ℝ) ^ paperRho q (r + 1) := by
      calc
        _ ≤ (4 * q : ℝ) ^ (10 * (q + q.choose (r + 1))) := by exact_mod_cast hcount
        _ ≤ _ := paper_threshold_reserve_growth hqr hn
    have hmul := mul_le_mul_of_nonneg_left hh
      (Real.rpow_nonneg (Nat.cast_nonneg n) (-paperRho q (r + 1)))
    rw [← Real.rpow_add hnpos, neg_add_cancel, Real.rpow_zero] at hmul
    simpa only [mul_assoc] using hmul

end Arxiv2411_18291
