import Arxiv.Arxiv2411_18291.LocalTypicalityNumerics

/-! # Growth estimates at the local typicality threshold, including small ranks -/

open Finset

namespace Arxiv2411_18291

theorem local_threshold_rpow_lower {b : ℝ} {d t k n : ℕ}
    (hb : 0 ≤ b) (hd : 0 < d) (hbase : b ^ d ≤ (2 : ℝ) ^ (9 * t))
    (hn : 2 ^ (9 * k) ≤ n) : b ^ k ≤ (n : ℝ) ^ ((t : ℝ) / d) := by
  have hnR : (2 : ℝ) ^ (9 * k) ≤ n := by exact_mod_cast hn
  have hp : (b ^ k) ^ d ≤ (n : ℝ) ^ t := by
    calc
      _ = (b ^ d) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm k d]
      _ ≤ ((2 : ℝ) ^ (9 * t)) ^ k := pow_le_pow_left₀ (pow_nonneg hb d) hbase k
      _ = ((2 : ℝ) ^ (9 * k)) ^ t := by rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hnR t
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hh := Real.rpow_le_rpow (pow_nonneg (pow_nonneg hb k) d) hp
    (show (0 : ℝ) ≤ 1 / (d : ℝ) by positivity)
  rw [← Real.rpow_natCast_mul (pow_nonneg hb k),
    ← Real.rpow_natCast_mul (Nat.cast_nonneg n), mul_one_div_cancel hdR, Real.rpow_one] at hh
  simpa only [mul_one_div] using hh

theorem local_typicality_tenth_lower {k n : ℕ} (hn : 2 ^ (9 * k) ≤ n) :
    (373 / 200 : ℝ) ^ k ≤ (n : ℝ) ^ (1 / 10 : ℝ) := by
  simpa only [Nat.cast_one, Nat.cast_ofNat] using
    local_threshold_rpow_lower (d := 10) (t := 1) (by norm_num) (by norm_num)
      (by norm_num : (373 / 200 : ℝ) ^ 10 ≤ (2 : ℝ) ^ (9 * 1)) hn

theorem local_typicality_root_polynomial {k : ℕ} (hk : 1 ≤ k) :
    128 * k ≤ 256 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; nlinarith only [ih, hk]

theorem local_typicality_density_polynomial {k : ℕ} (hk : 2 ≤ k) :
    663552 * k ^ 2 ≤ 1728 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hs : 2 * k ≤ k ^ 2 := by nlinarith only [hk]
    rw [pow_succ (1728 : ℕ)]
    nlinarith only [ih, hs, hk]

theorem sharp_local_typicality_size {r h n : ℕ} (hr : 1 ≤ r) (hh : 1 ≤ h)
    (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n) :
    262144 ≤ n ∧ r + 1 ≤ n / 2 ∧
      (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 5 / 16 ∧
      (h * r : ℝ) ≤ ((n : ℝ) ^ (-(1 / 10 : ℝ)) / 128) * n := by
  let k := (r + 1) * h
  have hk : 2 ≤ k := by dsimp only [k]; nlinarith only [hr, hh]
  have hnNat : 262144 ≤ n := by
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (show 18 ≤ 9 * k by omega)
    norm_num at hp
    exact hp.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hδ1 : (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hy := local_typicality_tenth_lower hn
  have hyl : (16 / 5 : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 373 / 200) hk
    exact (show (16 / 5 : ℝ) ≤ (373 / 200 : ℝ) ^ 2 by norm_num).trans (hp.trans hy)
  have hδ : (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 5 / 16 := by
    rw [Real.rpow_neg hn0.le]
    rw [← one_div, div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)]
    linarith only [hyl]
  have hg : (256 : ℝ) ^ k ≤ (n : ℝ) ^ (9 / 10 : ℝ) := by
    simpa only [Nat.cast_ofNat] using local_threshold_rpow_lower (d := 10) (t := 9)
      (by norm_num : (0 : ℝ) ≤ 256) (by norm_num)
      (by norm_num : (256 : ℝ) ^ 10 ≤ (2 : ℝ) ^ (9 * 9)) hn
  have hrhk : h * r ≤ k := by dsimp only [k]; nlinarith
  have hpoly : (128 * k : ℝ) ≤ (256 : ℝ) ^ k := by
    exact_mod_cast local_typicality_root_polynomial (show 1 ≤ k by omega)
  have hroot : (h * r : ℝ) ≤ ((n : ℝ) ^ (-(1 / 10 : ℝ)) / 128) * n := by
    have hhr : (h * r : ℝ) ≤ k := by exact_mod_cast hrhk
    have heq : (n : ℝ) ^ (9 / 10 : ℝ) = (n : ℝ) ^ (-(1 / 10 : ℝ)) * n := by
      rw [← Real.rpow_add_one hn0.ne']
      norm_num
    have hgt := hpoly.trans hg
    rw [heq] at hgt
    nlinarith only [hgt, hhr]
  refine ⟨hnNat, ?_, hδ, hroot⟩
  have hrootN := mul_le_mul_of_nonneg_right hδ1 (show (0 : ℝ) ≤ (n : ℝ) / 128 by positivity)
  have hrh : r ≤ h * r := by simpa only [one_mul] using Nat.mul_le_mul_right r hh
  have hrhR : (r : ℝ) ≤ h * r := by exact_mod_cast hrh
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hs : (2 * (r + 1) : ℝ) ≤ n := by nlinarith only [hroot, hrootN, hrhR, hrR]
  have hsN : 2 * (r + 1) ≤ n := by exact_mod_cast hs
  omega

theorem local_typicality_log_base : Real.log (373 / 200 : ℝ) ≤ 78 / 125 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 78 / 125) 7
  have hs : (373 / 200 : ℝ) ≤ ∑ i ∈ range 7, (78 / 125 : ℝ) ^ i / i.factorial := by
    norm_num [sum_range_succ]
  exact hs.trans hh

theorem local_typicality_log_prefactor : Real.log (9 / 2 : ℝ) < 301 / 200 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 301 / 200) 9
  have hs : (9 / 2 : ℝ) < ∑ i ∈ range 9, (301 / 200 : ℝ) ^ i / i.factorial := by
    norm_num [sum_range_succ]
  exact hs.trans_le hh

theorem local_typicality_neighborhood_polynomial {k : ℕ} (hk : 2 ≤ k) :
    (373 / 200 : ℝ) ^ k + (156 / 25 : ℝ) * k * (k - 1 : ℝ) + 301 / 200 <
      (504063 / 1212416 : ℝ) * (373 / 200 : ℝ) ^ (3 * k) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hp : (k : ℝ) * (k + 1) ≤ 6 * k * (k - 1) := by nlinarith only [hkR]
    have hpos : 0 ≤ (373 / 200 : ℝ) ^ k := by positivity
    have hpoly : (373 / 200 : ℝ) ^ (k + 1) +
        (156 / 25 : ℝ) * (k + 1) * ((k + 1 : ℕ) - 1 : ℝ) + 301 / 200 ≤
          6 * ((373 / 200 : ℝ) ^ k + (156 / 25 : ℝ) * k * (k - 1 : ℝ) + 301 / 200) := by
      rw [pow_succ]
      push_cast
      nlinarith only [hp, hpos]
    have hg : 6 * ((504063 / 1212416 : ℝ) * (373 / 200 : ℝ) ^ (3 * k)) ≤
        (504063 / 1212416 : ℝ) * (373 / 200 : ℝ) ^ (3 * (k + 1)) := by
      rw [Nat.mul_add, Nat.mul_one, pow_add]
      have hm := mul_le_mul_of_nonneg_right
        (by norm_num : (6 : ℝ) ≤ (373 / 200 : ℝ) ^ 3)
        (show 0 ≤ (504063 / 1212416 : ℝ) * (373 / 200 : ℝ) ^ (3 * k) by positivity)
      nlinarith only [hm]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (hpoly.trans_lt (mul_lt_mul_of_pos_left ih (by norm_num))).trans_le hg

end Arxiv2411_18291
