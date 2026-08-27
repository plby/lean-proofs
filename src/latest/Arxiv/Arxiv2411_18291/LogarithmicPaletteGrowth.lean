import Arxiv.Arxiv2411_18291.LogarithmicPaletteBudget

/-! # Absorbing the full logarithmic palette without enlarging the paper threshold -/

noncomputable section

namespace Arxiv2411_18291

theorem relaxedGeneratorPaletteSize_log_bound {W : Type*} [Fintype W] [DecidableEq W]
    {q r n h : ℕ} (hqr : r + 1 < q) (hn : 1 ≤ n)
    (S : ExchangeSystem W q (r + 1)) (P : Block W q)
    (hqh : q.choose (r + 1) ≤ h) (hSh : S.graph.card ≤ h) :
    (relaxedGeneratorPaletteSize n S P : ℝ) * 2 ^ q + 1 ≤
      81 * (q + 1 : ℝ) * h * 2 ^ q * (Real.log n + 1) := by
  let b : ℝ := 2 ^ q
  let A : ℝ := (q + 1) * h * b
  have hb : 1 ≤ b := one_le_pow₀ (by norm_num)
  have hh : (1 : ℝ) ≤ h := by exact_mod_cast (Nat.choose_pos hqr.le).trans_le hqh
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hHb : b ≤ (h : ℝ) * b := le_mul_of_one_le_left (by positivity) hh
  have hAb : (h : ℝ) * b ≤ A := by
    dsimp only [A]
    nlinarith only [(Nat.cast_nonneg q : (0 : ℝ) ≤ q),
      mul_nonneg (Nat.cast_nonneg h) (by positivity : 0 ≤ b)]
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hP : (relaxedGeneratorPaletteSize n S P : ℝ) ≤
      4 * ((logarithmicColourTrialCount n (2 * q) : ℝ) * h + 1) := by
    exact_mod_cast relaxedGeneratorPaletteSize_le hqr hn S P hqh hSh
  have hL : (logarithmicColourTrialCount n (2 * q) : ℝ) ≤
      9 * (2 * q + 2 : ℝ) * Real.log n + 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (logarithmicColourTrialCount_lt hn (2 * q)).le
  calc
    _ ≤ (4 * ((logarithmicColourTrialCount n (2 * q) : ℝ) * h + 1)) * b + 1 := by
      have hh := mul_le_mul_of_nonneg_right hP (show 0 ≤ b by positivity)
      change (relaxedGeneratorPaletteSize n S P : ℝ) * b + 1 ≤ _
      linarith only [hh]
    _ ≤ (4 * ((9 * (2 * q + 2 : ℝ) * Real.log n + 1) * h + 1)) * b + 1 := by
      gcongr
    _ = 72 * A * Real.log n + 4 * ((h : ℝ) * b) + 4 * b + 1 := by
      dsimp only [A]
      ring
    _ ≤ 72 * A * Real.log n + 9 * A := by linarith only [hAb, hHb, hb]
    _ ≤ _ := by
      change _ ≤ 81 * (q + 1 : ℝ) * h * b * (Real.log n + 1)
      have hp := mul_nonneg hA0 hlog
      calc
        _ ≤ 81 * A * (Real.log n + 1) := by nlinarith only [hp, hA0]
        _ = _ := by dsimp only [A]; ring

theorem log_add_one_le_small_alpha_power {q r n : ℕ} (hqr : r + 1 < q) (hn : 1 ≤ n) :
    Real.log (n : ℝ) + 1 ≤
      181 * paperInverseAlpha q (r + 1) * (n : ℝ) ^ (paperAlpha q (r + 1) / 180) := by
  have hα := paperAlpha_pos hqr
  have hlog : Real.log (n : ℝ) ≤
      180 * paperInverseAlpha q (r + 1) * (n : ℝ) ^ (paperAlpha q (r + 1) / 180) := by
    have hh := Real.log_le_rpow_div (Nat.cast_nonneg n)
      (show (0 : ℝ) < paperAlpha q (r + 1) / 180 by positivity)
    convert hh using 1
    rw [paperAlpha_eq_inverse, div_div_eq_mul_div, div_inv_eq_mul]
    ring
  have hI : (1 : ℝ) ≤ paperInverseAlpha q (r + 1) := by
    exact_mod_cast paperInverseAlpha_pos hqr
  have hx : 1 ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 180) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  have hprod : (1 : ℝ) ≤ paperInverseAlpha q (r + 1) *
      (n : ℝ) ^ (paperAlpha q (r + 1) / 180) := by nlinarith only [hI, hx]
  linarith only [hlog, hprod]

theorem relaxed_generator_coefficient_growth_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (S : ExchangeSystem W q (r + 1)) (P : Block W q)
    (hqh : q.choose (r + 1) ≤ S.graph.card)
    (hS : S.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    (relaxedGeneratorPaletteSize n S P : ℝ) * 2 ^ q + 1 ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 20) := by
  let h := 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2
  have hnNat : 1 ≤ n := (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_one.trans_le hnNat
  have hc : (81 * 181 * (q + 1 : ℝ) * h * paperInverseAlpha q (r + 1) * 2 ^ q) ≤
      (4 * q : ℝ) ^ (4 * q) := by
    exact_mod_cast relaxed_palette_log_coefficient_bound hqr hq
  have hg : (4 * q : ℝ) ^ (4 * q) ≤
      (n : ℝ) ^ (2 * paperAlpha q (r + 1) / 45) := by
    have hh := paper_threshold_alpha_rpow_lower hqr hn (s := 4 * q)
      (t := (2 / 45 : ℝ)) (by norm_num) (by push_cast; linarith)
    convert hh using 1
    congr 1
    ring
  calc
    _ ≤ 81 * (q + 1 : ℝ) * h * 2 ^ q * (Real.log n + 1) :=
      relaxedGeneratorPaletteSize_log_bound hqr hnNat S P (hqh.trans hS) hS
    _ ≤ 81 * (q + 1 : ℝ) * h * 2 ^ q *
        (181 * paperInverseAlpha q (r + 1) *
          (n : ℝ) ^ (paperAlpha q (r + 1) / 180)) :=
      mul_le_mul_of_nonneg_left (log_add_one_le_small_alpha_power hqr hnNat) (by positivity)
    _ = (81 * 181 * (q + 1 : ℝ) * h * paperInverseAlpha q (r + 1) * 2 ^ q) *
        (n : ℝ) ^ (paperAlpha q (r + 1) / 180) := by ring
    _ ≤ (n : ℝ) ^ (2 * paperAlpha q (r + 1) / 45) *
        (n : ℝ) ^ (paperAlpha q (r + 1) / 180) :=
      mul_le_mul_of_nonneg_right (hc.trans hg) (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

end Arxiv2411_18291
