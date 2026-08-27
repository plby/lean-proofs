import Arxiv.Arxiv2411_18291.FiniteModularHostNumerics
import Arxiv.Arxiv2411_18291.FiniteTypicalHostNumerics
import Arxiv.Arxiv2411_18291.ExplicitNibbleBinomial

/-! # Reference-density binomial normalization of clique main terms -/

namespace Arxiv2411_18291

theorem reference_product_error {A B X Y ε : ℝ} (hA : 0 ≤ A) (hY : 0 ≤ Y)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hBA : B ≤ A) (hB : (1 - ε / 8) * A ≤ B)
    (hXY : |X - Y| ≤ (ε / 8) * Y) :
    |A * X - B * Y| ≤ (ε / 2) * (B * Y) := by
  have hεA := mul_le_mul_of_nonneg_right hε1 hA
  have hA2 : A ≤ 2 * B := by nlinarith only [hB, hεA, hA]
  have hfirst : |A * X - A * Y| ≤ (ε / 8) * (A * Y) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hA]
    exact (mul_le_mul_of_nonneg_left hXY hA).trans_eq (by ring)
  have hsecond : |A * Y - B * Y| ≤ (ε / 8) * (A * Y) := by
    rw [← sub_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hBA), abs_of_nonneg hY]
    have hh := mul_le_mul_of_nonneg_right
      (show A - B ≤ (ε / 8) * A by nlinarith only [hB]) hY
    nlinarith only [hh]
  calc
    _ ≤ |A * X - A * Y| + |A * Y - B * Y| := abs_sub_le _ _ _
    _ ≤ (ε / 4) * (A * Y) := by nlinarith only [hfirst, hsecond]
    _ ≤ (ε / 4) * ((2 * B) * Y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA2 hY) (by positivity)
    _ = _ := by ring

theorem reference_normalization_errors_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (n : ℝ) ^ (-(1 / 10 : ℝ)) * q.choose (r + 1) * 2 ^ q.choose (r + 1) ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 8 ∧
      (n : ℝ) ^ (-(2 / 5 : ℝ)) ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 8 := by
  let K := q.choose (r + 1)
  have hk : 1 ≤ K := Nat.choose_pos hqr.le
  have hq : 0 < q := by omega
  have hKsq : K ≤ K ^ 2 := by nlinarith only [hk]
  have hH : K ≤ 3 * (2 * q) ^ (r + 1) * K ^ 2 :=
    hKsq.trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hnormal : (4 * (4 + 2 * K * 2 ^ K) : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) :=
    (show (4 * (4 + 2 * K * 2 ^ K) : ℝ) ≤ (4 * q : ℝ) ^ (10 * (q + K)) by
      exact_mod_cast reserve_normalization_constant_le (K := K) (by omega : 2 ≤ q)).trans
        (paper_host_configuration_growth hqr hn hk hH)
  have hKnonneg : (0 : ℝ) ≤ K * 2 ^ K := by positivity
  have hcoef : (8 * K * 2 ^ K : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) := by
    nlinarith only [hnormal]
  have h8 : (8 : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) := by
    nlinarith only [hnormal, hKnonneg]
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hα := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  constructor
  · have hh := mul_le_mul_of_nonneg_right hcoef
      (Real.rpow_nonneg hn0.le (-(1 / 10 : ℝ)))
    rw [← Real.rpow_add hn0] at hh
    have hp := Real.rpow_le_rpow_of_exponent_le hn1
      (show (1 / 40 : ℝ) + -(1 / 10) ≤ -(paperAlpha q (r + 1) / 10) by
        linarith only [hα])
    change (n : ℝ) ^ (-(1 / 10 : ℝ)) * K * 2 ^ K ≤ _
    nlinarith only [hh, hp]
  · have hh := mul_le_mul_of_nonneg_right h8
      (Real.rpow_nonneg hn0.le (-(2 / 5 : ℝ)))
    rw [← Real.rpow_add hn0] at hh
    have hp := Real.rpow_le_rpow_of_exponent_le hn1
      (show (1 / 40 : ℝ) + -(2 / 5) ≤ -(paperAlpha q (r + 1) / 10) by
        linarith only [hα])
    nlinarith only [hh, hp]

theorem reference_density_factorial_error_paper_threshold {q r n m s : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hm : m ≤ q) (hs : s ≤ q.choose (r + 1)) {d : ℝ} (hd0 : 0 ≤ d)
    (hd : |d - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    |((n : ℝ) ^ m / m.factorial) * d ^ s -
        ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ s * (n.choose m : ℝ)| ≤
      ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 2) *
        (((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ s * (n.choose m : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hε0 := Real.rpow_nonneg hn0.le (-(paperAlpha q (r + 1) / 10))
  have hε1 : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1
      (by linarith only [paperAlpha_pos hqr])
  obtain ⟨hpowError, hbinError⟩ := reference_normalization_errors_paper_threshold hqr hn
  have hpow := relative_pow_error hd0 (Real.rpow_nonneg hn0.le _)
    (Real.rpow_nonneg hn0.le (-(1 / 10 : ℝ)))
    (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)) hd hs
  have hpow' := hpow.trans (mul_le_mul_of_nonneg_right hpowError
    (pow_nonneg (Real.rpow_nonneg hn0.le _) s))
  obtain ⟨_, _, hchoose⟩ := explicit_boost_binomial_numerics (by omega : 2 ≤ q)
    ((boost_threshold_le_paper_threshold hqr).trans hn)
  have hchoose' : (1 - (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 8) *
      ((n : ℝ) ^ m / m.factorial) ≤ (n.choose m : ℝ) := by
    calc
      _ ≤ (1 - (n : ℝ) ^ (-(2 / 5 : ℝ))) * ((n : ℝ) ^ m / m.factorial) :=
        mul_le_mul_of_nonneg_right (by linarith only [hbinError]) (by positivity)
      _ ≤ _ := by simpa only [mul_div_assoc] using hchoose m hm
  have hh := reference_product_error (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ m / m.factorial)
    (pow_nonneg (Real.rpow_nonneg hn0.le _) s) hε0 hε1 (Nat.choose_le_pow_div m n)
    hchoose' hpow'
  simpa only [mul_comm (n.choose m : ℝ)] using hh

theorem cliqueMainTerm_reference_error_paper_threshold {q r n a : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {d : ℝ} (hd0 : 0 ≤ d)
    (hd : |d - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    |cliqueMainTerm n d q (r + 1) a -
        ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ (q.choose (r + 1) - a.choose (r + 1)) *
          (n.choose (q - a) : ℝ)| ≤
      ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 2) *
        (((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ (q.choose (r + 1) - a.choose (r + 1)) *
          (n.choose (q - a) : ℝ)) := by
  have hh := reference_density_factorial_error_paper_threshold hqr hn
    (Nat.sub_le q a) (Nat.sub_le (q.choose (r + 1)) (a.choose (r + 1))) hd0 hd
  simpa only [cliqueMainTerm, div_mul_eq_mul_div] using hh

end Arxiv2411_18291
