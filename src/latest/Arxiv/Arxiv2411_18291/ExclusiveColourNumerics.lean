import Arxiv.Arxiv2411_18291.FiniteGoodDensity
import Arxiv.Arxiv2411_18291.FiniteColourTrials

/-! # Numerical margins for exclusive rainbow clique counts -/

noncomputable section

namespace Arxiv2411_18291

theorem paper_good_density_error_forty_eight {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    48 * (q.choose (r + 1) : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤ 1 := by
  have hq : 2 ≤ q := by omega
  have hc : 48 * q.choose (r + 1) ≤ (4 * q) ^ (q + 2) := by
    calc
      _ ≤ (4 * q) ^ 2 * (4 * q) ^ q := Nat.mul_le_mul
        (by nlinarith only [hq] : 48 ≤ (4 * q) ^ 2)
        ((Nat.choose_le_two_pow q (r + 1)).trans (Nat.pow_le_pow_left (by omega) q))
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := q + 2)
    (t := (1 / 10 : ℝ)) (by norm_num) (by push_cast; linarith only [hqR])
  have hcR : 48 * (q.choose (r + 1) : ℝ) ≤ (4 * q : ℝ) ^ (q + 2) := by
    exact_mod_cast hc
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hh := mul_le_mul_of_nonneg_right (hcR.trans hg)
    (Real.rpow_nonneg hn0.le (-(paperAlpha q (r + 1) / 10)))
  have heq : (n : ℝ) ^ (paperAlpha q (r + 1) * (1 / 10)) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) = 1 := by
    rw [← Real.rpow_add hn0, show paperAlpha q (r + 1) * (1 / 10) +
      -(paperAlpha q (r + 1) / 10) = 0 by ring, Real.rpow_zero]
  rwa [heq] at hh

theorem good_reference_density_power_fifteen_sixteenths {q r n s : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hs : s ≤ q.choose (r + 1)) (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card) :
    (15 / 16 : ℝ) * ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ s ≤ density G ^ s := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hαupper := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hδε : (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hαupper])
  have hε := Real.rpow_nonneg (Nat.cast_nonneg n) (-(paperAlpha q (r + 1) / 10))
  have hbig := paper_good_density_error_forty_eight hqr hn
  have hk : (1 : ℝ) ≤ q.choose (r + 1) := by exact_mod_cast Nat.choose_pos hqr.le
  have hsmall : 3 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hk hε
    nlinarith only [hm, hbig, hε]
  have hscaled : 48 * (s : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤ 1 :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hs) (by norm_num : (0 : ℝ) ≤ 48)) hε).trans hbig
  have hc : (15 / 16 : ℝ) ≤ 1 - 3 * (s : ℝ) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) := by linarith only [hscaled]
  exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans
    (density_pow_lower_relative_errors (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      hε hδε hsmall hd hGK hloss)

theorem exclusive_colour_collision_coefficient_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    256 * (q.choose (r + 1) : ℝ) ^ 2 * (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 24)) := by
  have hq : 2 ≤ q := by omega
  have hc : 256 * (q.choose (r + 1)) ^ 2 ≤ (4 * q) ^ (2 * q + 4) := by
    have hk := (Nat.choose_le_two_pow q (r + 1)).trans
      (Nat.pow_le_pow_left (by omega : 2 ≤ 4 * q) q)
    have h256 : 256 ≤ (4 * q) ^ 4 := by
      have hh := Nat.pow_le_pow_left (by omega : 4 ≤ 4 * q) 4
      norm_num at hh
      exact hh
    calc
      _ ≤ (4 * q) ^ 4 * ((4 * q) ^ q) ^ 2 :=
        Nat.mul_le_mul h256 (Nat.pow_le_pow_left hk 2)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have hcR : 256 * (q.choose (r + 1) : ℝ) ^ 2 ≤ (4 * q : ℝ) ^ (2 * q + 4) := by
    exact_mod_cast hc
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 2 * q + 4)
    (t := (23 / 24 : ℝ)) (by norm_num) (by push_cast; linarith only [hqR])
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  calc
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) * (23 / 24)) *
        (n : ℝ) ^ (-paperAlpha q (r + 1)) :=
      mul_le_mul_of_nonneg_right (hcR.trans hg) (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

end Arxiv2411_18291
