import Arxiv.Arxiv2411_18291.FiniteGeneratorCap

/-! # Reserving three quarters of the modular-generator error budget -/

namespace Arxiv2411_18291

theorem generator_modulus_margin_paper_threshold {q r n N : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : N ≤ (r + 1).factorial * q.choose (r + 1)) :
    (256 * q.choose (r + 1) * q.choose r * N : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hc : (256 * q.choose (r + 1) * q.choose r * N : ℝ) ≤
      (4 * q : ℝ) ^ (2 * q + 4) := by
    have hbase : (16 * q.choose (r + 1) * q.choose r * N : ℝ) ≤
        (4 * q : ℝ) ^ (2 * q + 2) := by
      exact_mod_cast generator_saturation_coefficient_bound hqr hN
    calc
      _ = 16 * (16 * q.choose (r + 1) * q.choose r * N : ℝ) := by ring
      _ ≤ (4 * q : ℝ) ^ 2 * (4 * q : ℝ) ^ (2 * q + 2) :=
        mul_le_mul (by nlinarith only [hq]) hbase (by positivity) (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 2 * q + 4)
    (t := (1 / 10 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
  simpa only [div_eq_mul_inv, one_mul] using hc.trans hg

theorem generator_cap_quarter_error_of_margin {q r n N : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : (256 * q.choose (r + 1) * q.choose r * N : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 10)) :
    0 < ⌊(n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10)⌋₊ ∧
      ((q - r : ℕ) : ℝ) * ⌊(n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10)⌋₊ <
        (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) * n ∧
      ∀ d : ℝ, d ≤ 2 * (n : ℝ) ^ (-paperAlpha q (r + 1)) →
        4 * (q.choose (r + 1) : ℝ) * q.choose r * N * n * d ≤
          (⌊(n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10)⌋₊ : ℝ) *
            ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4) ^ 2 := by
  have hnNat : 0 < n :=
    Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hα := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hlarge : (2 : ℝ) ≤ (n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10) := by
    have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 1)
      (t := 1) (by norm_num) (by push_cast; linarith only [hq])
    simp only [pow_one, mul_one] at hg
    exact (show (2 : ℝ) ≤ 4 * q by linarith only [hq]).trans (hg.trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hα])))
  have hmargin : 8 * (q.choose (r + 1) : ℝ) * q.choose r * (16 * N : ℕ) * 2 ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) - 7 * paperAlpha q (r + 1) / 10 -
        2 * (paperAlpha q (r + 1) / 10)) := by
    calc
      _ = (256 * q.choose (r + 1) * q.choose r * N : ℝ) := by push_cast; ring
      _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := hN
      _ = _ := by congr 1; ring
  obtain ⟨hcap, hθ, hsmall⟩ := generator_cap_numerics_of_growth q r (16 * N) hnNat hlarge hmargin
  refine ⟨hcap, hθ, ?_⟩
  intro d hd
  have hh := hsmall d hd
  push_cast at hh
  calc
    _ = (4 * (q.choose (r + 1) : ℝ) * q.choose r * (16 * N) * n * d) / 16 := by ring
    _ ≤ ((⌊(n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10)⌋₊ : ℝ) *
        ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10))) ^ 2) / 16 :=
      div_le_div_of_nonneg_right hh (by norm_num)
    _ = _ := by ring

theorem generator_cap_quarter_error_paper_threshold {q r n N : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : N ≤ (r + 1).factorial * q.choose (r + 1)) :
    0 < ⌊(n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10)⌋₊ ∧
      ((q - r : ℕ) : ℝ) * ⌊(n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10)⌋₊ <
        (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) * n ∧
      ∀ d : ℝ, d ≤ 2 * (n : ℝ) ^ (-paperAlpha q (r + 1)) →
        4 * (q.choose (r + 1) : ℝ) * q.choose r * N * n * d ≤
          (⌊(n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10)⌋₊ : ℝ) *
            ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4) ^ 2 := by
  exact generator_cap_quarter_error_of_margin hqr hn
    (generator_modulus_margin_paper_threshold hqr hn hN)

theorem generator_count_quarter_error_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (2 * (n : ℝ) ^ (-(1 / 10 : ℝ))) * q * 2 ^ q ≤
      ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4) / 2 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hα := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hcount := typical_count_error_at_exponent_paper_threshold hqr hn
    (κ := paperAlpha q (r + 1) / 5) (by linarith only [hα])
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 1)
    (t := (1 / 10 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
  have hfour : (4 : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by
    simpa only [pow_one, mul_one, div_eq_mul_inv, one_mul] using
      (show (4 : ℝ) ≤ (4 * q : ℝ) ^ 1 by simp only [pow_one]; linarith only [hq]).trans hg
  have hm := mul_le_mul_of_nonneg_right hfour
    (Real.rpow_nonneg hn0.le (-(paperAlpha q (r + 1) / 5)))
  rw [← Real.rpow_add hn0, show paperAlpha q (r + 1) / 10 +
      -(paperAlpha q (r + 1) / 5) = -(paperAlpha q (r + 1) / 10) by ring] at hm
  linarith only [hcount, hm]

end Arxiv2411_18291
