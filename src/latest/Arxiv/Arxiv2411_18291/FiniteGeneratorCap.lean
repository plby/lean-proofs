import Arxiv.Arxiv2411_18291.GeneratorCapNumerics
import Arxiv.Arxiv2411_18291.PaperAlphaGrowth

/-! # Finite face-cap and saturation budgets for the modular generators -/

namespace Arxiv2411_18291

theorem generator_saturation_coefficient_bound {q r N : ℕ} (hqr : r + 1 < q)
    (hN : N ≤ (r + 1).factorial * q.choose (r + 1)) :
    16 * q.choose (r + 1) * q.choose r * N ≤ (4 * q) ^ (2 * q + 2) := by
  have hfac : (r + 1).factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le hqr.le).trans ((Nat.factorial_le_pow q).trans
      (Nat.pow_le_pow_left (by omega) q))
  have hbin : (q.choose (r + 1)) ^ 2 * q.choose r ≤ (4 * q) ^ q := by
    calc
      _ ≤ (2 ^ q) ^ 2 * 2 ^ q := Nat.mul_le_mul
        (Nat.pow_le_pow_left (Nat.choose_le_two_pow q (r + 1)) 2) (Nat.choose_le_two_pow q r)
      _ = 8 ^ q := by
        rw [← pow_mul, ← pow_add, show q * 2 + q = 3 * q by omega, pow_mul]
        norm_num
      _ ≤ _ := Nat.pow_le_pow_left (by omega) q
  calc
    _ ≤ 16 * q.choose (r + 1) * q.choose r *
        ((r + 1).factorial * q.choose (r + 1)) := Nat.mul_le_mul_left _ hN
    _ = 16 * (r + 1).factorial * ((q.choose (r + 1)) ^ 2 * q.choose r) := by ring
    _ ≤ (4 * q) ^ 2 * (4 * q) ^ q * (4 * q) ^ q :=
      Nat.mul_le_mul (Nat.mul_le_mul (by nlinarith only [hqr] : 16 ≤ (4 * q) ^ 2) hfac) hbin
    _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega

theorem generator_cap_numerics_paper_threshold {q r n N : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : N ≤ (r + 1).factorial * q.choose (r + 1)) :
    0 < ⌊(n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10)⌋₊ ∧
      ((q - r : ℕ) : ℝ) * ⌊(n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10)⌋₊ <
        (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) * n ∧
      ∀ d : ℝ, d ≤ 2 * (n : ℝ) ^ (-paperAlpha q (r + 1)) →
        4 * (q.choose (r + 1) : ℝ) * q.choose r * N * n * d ≤
          (⌊(n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10)⌋₊ : ℝ) *
            ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10))) ^ 2 := by
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
  apply generator_cap_numerics_of_growth q r N hnNat hlarge
  have hc : (16 * q.choose (r + 1) * q.choose r * N : ℝ) ≤
      (4 * q : ℝ) ^ (2 * q + 2) := by
    exact_mod_cast generator_saturation_coefficient_bound hqr hN
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 2 * q + 2)
    (t := (1 / 10 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
  calc
    _ = (16 * q.choose (r + 1) * q.choose r * N : ℝ) := by ring
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) * (1 / 10)) := hc.trans hg
    _ = _ := by congr 1; ring

theorem typical_count_error_at_exponent_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) {κ : ℝ}
    (hκ : paperAlpha q (r + 1) + κ ≤ 1 / 10) :
    (2 * (n : ℝ) ^ (-(1 / 10 : ℝ))) * q * 2 ^ q ≤
      (n : ℝ) ^ (-(κ)) / 2 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hc : (4 * q * 2 ^ q : ℝ) ≤ (4 * q : ℝ) ^ (q + 1) := by
    calc
      _ ≤ (4 * q : ℝ) * (4 * q : ℝ) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num)
          (by linarith only [hq]) q) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := q + 1)
    (t := 1) (by norm_num) (by push_cast; linarith only [hq])
  simp only [mul_one] at hg
  have hb : (4 * q * 2 ^ q : ℝ) ≤
      (n : ℝ) ^ ((1 / 10 : ℝ) - κ) :=
    (hc.trans hg).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hκ]))
  have hh := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hn0.le (-(1 / 10 : ℝ)))
  have heq : (n : ℝ) ^ ((1 / 10 : ℝ) - κ) *
      (n : ℝ) ^ (-(1 / 10 : ℝ)) = (n : ℝ) ^ (-(κ)) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  rw [heq] at hh
  nlinarith only [hh]

theorem generator_count_error_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (2 * (n : ℝ) ^ (-(1 / 10 : ℝ))) * q * 2 ^ q ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 2 := by
  have hα := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  exact typical_count_error_at_exponent_paper_threshold hqr hn (by linarith only [hα])

end Arxiv2411_18291
