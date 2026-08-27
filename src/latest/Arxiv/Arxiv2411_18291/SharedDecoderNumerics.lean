import Arxiv.Arxiv2411_18291.PaperAlphaGrowth
import Arxiv.Arxiv2411_18291.ExplicitAbsorberGreedyTail

/-! # Shared decoder sampling at the original threshold -/

namespace Arxiv2411_18291

theorem shared_decoder_sampling_size {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    q + (r + 1) ≤ n ∧ 0 < n ∧
      ((r + 1 : ℕ) : ℝ) * (q + (r + 1)) ≤ (n : ℝ) / 2 := by
  have hq : 2 ≤ q := by omega
  have hlarge : (4 * q) ^ 2 ≤ n :=
    (Nat.pow_le_pow_right (by omega : 0 < 4 * q) (by omega : 2 ≤ 90 * q)).trans
      ((boost_threshold_le_paper_threshold hqr).trans hn)
  have hsize : 2 * (r + 1) * (q + (r + 1)) ≤ n := by nlinarith only [hqr, hlarge]
  refine ⟨by nlinarith only [hqr, hlarge, hq], by nlinarith only [hlarge, hq], ?_⟩
  have hcast : (2 * (r + 1) * (q + (r + 1)) : ℝ) ≤ n := by exact_mod_cast hsize
  push_cast
  linarith only [hcast]

theorem shared_decoder_root_scale_lower {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) {C : ℝ} (hC : 1 ≤ C) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) / (q - r : ℕ) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hα := paperAlpha_pos hqr
  have hαhi := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hcost : ((q - r : ℕ) : ℝ) ≤ (n : ℝ) ^ (3 * paperAlpha q (r + 1) / 10) := by
    have h := paper_threshold_alpha_rpow_lower hqr hn (s := 1) (t := (3 / 10 : ℝ))
      (by norm_num) (by push_cast; linarith only [hq])
    have hqr' : ((q - r : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q r
    simp only [pow_one] at h
    have heq : paperAlpha q (r + 1) * (3 / 10 : ℝ) =
        3 * paperAlpha q (r + 1) / 10 := by ring
    rw [heq] at h
    exact (by linarith only [hqr', hq] : ((q - r : ℕ) : ℝ) ≤ 4 * q).trans h
  have hden : (0 : ℝ) < (q - r : ℕ) := by exact_mod_cast (show 0 < q - r by omega)
  calc
    _ ≤ (n : ℝ) ^ (-paperAlpha q (r + 1)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hαhi])
    _ ≤ (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) / (q - r : ℕ) := by
      apply (le_div_iff₀ hden).mpr
      calc
        _ ≤ (n : ℝ) ^ (-paperAlpha q (r + 1)) *
            (n : ℝ) ^ (3 * paperAlpha q (r + 1) / 10) :=
          mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg hn0.le _)
        _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (le_mul_of_one_le_left (Real.rpow_nonneg hn0.le _) hC) hden.le

theorem shared_decoder_failure_lt_one {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) {C : ℝ} (hC : 1 ≤ C) :
    (n.choose r : ℝ) * Real.exp (-(2 ^ (r + 1) * (r + 1).factorial *
      ((C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) / (q - r : ℕ)) * n / 3)) <
        1 := by
  have hn1 : 1 ≤ n := (paperSizeThreshold_one_lt hqr).le.trans hn
  have h := absorber_greedy_failure_lt_one hqr hn (M := 1) hn1
    (shared_decoder_root_scale_lower hqr hn hC)
  simp only [Nat.cast_one, one_mul] at h
  apply lt_of_le_of_lt _ h
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  have htwo : (2 : ℝ) ≤ 2 ^ (r + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 ≤ r + 1 by omega)
  gcongr

end Arxiv2411_18291
