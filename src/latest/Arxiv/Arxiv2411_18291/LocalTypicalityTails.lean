import Arxiv.Arxiv2411_18291.LocalTypicalityGrowth

/-! # Both typicality tails fit the source's local threshold -/

open Finset

namespace Arxiv2411_18291

theorem local_typicality_log_bound {k n : ℕ} (hk : 2 ≤ k)
    (hn : 2 ^ (9 * k) ≤ n) :
    Real.log (n : ℝ) ≤ (156 / 25 : ℝ) * k *
      ((n : ℝ) ^ (1 / 10 : ℝ) / (373 / 200 : ℝ) ^ k) := by
  have hnNat : 1 ≤ n := (Nat.one_le_pow _ _ (by norm_num)).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  let y := (n : ℝ) ^ (1 / 10 : ℝ)
  let z := y / (373 / 200 : ℝ) ^ k
  have hy0 : 0 < y := Real.rpow_pos_of_pos hn0 _
  have ha0 : 0 < (373 / 200 : ℝ) ^ k := by positivity
  have hz0 : 0 < z := div_pos hy0 ha0
  have hz1 : 1 ≤ z := (one_le_div ha0).mpr (local_typicality_tenth_lower hn)
  have hprod : (373 / 200 : ℝ) ^ k * z = y := by dsimp only [z]; field_simp
  have hlog : Real.log y = (k : ℝ) * Real.log (373 / 200 : ℝ) + Real.log z := by
    rw [← hprod, Real.log_mul ha0.ne' hz0.ne', Real.log_pow]
  have hlogy : Real.log y = (1 / 10 : ℝ) * Real.log n := Real.log_rpow hn0 _
  have hlogz := Real.log_le_sub_one_of_pos hz0
  have hloga := mul_le_mul_of_nonneg_left local_typicality_log_base (Nat.cast_nonneg k)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoeff : 0 ≤ ((78 / 125 : ℝ) * k - 1) * (z - 1) :=
    mul_nonneg (by linarith only [hkR]) (by linarith only [hz1])
  change Real.log (n : ℝ) ≤ (156 / 25 : ℝ) * k * z
  nlinarith only [hlog, hlogy, hlogz, hloga, hcoeff]

theorem local_typicality_neighborhood_tail {k m n : ℕ} (hk : 2 ≤ k)
    (hm : m + 1 ≤ k) (hn : 2 ^ (9 * k) ≤ n) :
    (9 / 4 : ℝ) * (n : ℝ) ^ m *
        Real.exp (-((504063 / 1212416 : ℝ) * (n : ℝ) ^ (3 / 10 : ℝ))) <
      (1 / 2 : ℝ) * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
  have hnNat : 1 ≤ n := (Nat.one_le_pow _ _ (by norm_num)).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  let x := (373 / 200 : ℝ) ^ k
  let y := (n : ℝ) ^ (1 / 10 : ℝ)
  let z := y / x
  have hx0 : 0 < x := by dsimp only [x]; positivity
  have hy0 : 0 < y := Real.rpow_pos_of_pos hn0 _
  have hxy : x ≤ y := local_typicality_tenth_lower hn
  have hz0 : 0 < z := div_pos hy0 hx0
  have hz1 : 1 ≤ z := (one_le_div hx0).mpr hxy
  have hxz : x * z = y := by dsimp only [z]; field_simp
  have hln := local_typicality_log_bound hk hn
  change Real.log (n : ℝ) ≤ (156 / 25 : ℝ) * k * z at hln
  have hmR : (m : ℝ) ≤ k - 1 := by exact_mod_cast (show m ≤ (k : ℤ) - 1 by omega)
  have hlog : Real.log ((9 / 2 : ℝ) * (n : ℝ) ^ m) ≤
      ((156 / 25 : ℝ) * k * (k - 1) + 301 / 200) * z := by
    rw [Real.log_mul (by norm_num) (pow_pos hn0 _).ne', Real.log_pow]
    have ha := mul_le_mul_of_nonneg_left hln (Nat.cast_nonneg m)
    have hb := mul_le_mul_of_nonneg_right hmR
      (show 0 ≤ (156 / 25 : ℝ) * k * z by positivity)
    have hc := mul_le_mul_of_nonneg_left hz1 (by norm_num : (0 : ℝ) ≤ 301 / 200)
    nlinarith only [ha, hb, hc, local_typicality_log_prefactor.le]
  have hpoly := mul_lt_mul_of_pos_right (local_typicality_neighborhood_polynomial hk) hz0
  have hpow : (373 / 200 : ℝ) ^ (3 * k) = x ^ 3 := by
    dsimp only [x]
    rw [← pow_mul, Nat.mul_comm]
  rw [hpow] at hpoly
  change (x + (156 / 25 : ℝ) * k * (k - 1) + 301 / 200) * z <
    (504063 / 1212416 : ℝ) * x ^ 3 * z at hpoly
  have hgap : y + ((156 / 25 : ℝ) * k * (k - 1) + 301 / 200) * z <
      (504063 / 1212416 : ℝ) * x ^ 2 * y := by
    have heq : x ^ 3 * z = x ^ 2 * y := by rw [← hxz]; ring
    nlinarith only [hpoly, heq, hxz]
  have hs := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0.le hxy 2) hy0.le
  have hE : y + ((156 / 25 : ℝ) * k * (k - 1) + 301 / 200) * z <
      (504063 / 1212416 : ℝ) * y ^ 3 := by
    nlinarith only [hgap, hs]
  have hy3 : y ^ 3 = (n : ℝ) ^ (3 / 10 : ℝ) := by
    dsimp only [y]
    rw [← Real.rpow_mul_natCast hn0.le]
    norm_num
  rw [hy3] at hE
  have he : (9 / 2 : ℝ) * (n : ℝ) ^ m *
      Real.exp (-((504063 / 1212416 : ℝ) * (n : ℝ) ^ (3 / 10 : ℝ))) <
        Real.exp (-y) := by
    calc
      _ = Real.exp (Real.log ((9 / 2 : ℝ) * (n : ℝ) ^ m) -
          (504063 / 1212416 : ℝ) * (n : ℝ) ^ (3 / 10 : ℝ)) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by positivity)]
      _ < _ := Real.exp_lt_exp.mpr (by linarith only [hlog, hE])
  change _ < (1 / 2 : ℝ) * Real.exp (-y)
  linarith only [he]

theorem local_typicality_density_margin {r h n : ℕ} (hr : 1 ≤ r) (hh : 1 ≤ h)
    (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n) :
    (2654208 * h ^ 2 : ℝ) ≤ (n : ℝ) ^ (6 / 5 : ℝ) := by
  let k := (r + 1) * h
  have hk : 2 ≤ k := by dsimp only [k]; nlinarith only [hr, hh]
  have hhk : 2 * h ≤ k := by dsimp only [k]; nlinarith only [hr]
  have hpoly : (663552 * k ^ 2 : ℝ) ≤ (1728 : ℝ) ^ k := by
    exact_mod_cast local_typicality_density_polynomial hk
  have hg : (1728 : ℝ) ^ k ≤ (n : ℝ) ^ (6 / 5 : ℝ) := by
    simpa only [Nat.cast_ofNat] using local_threshold_rpow_lower (d := 5) (t := 6)
      (by norm_num : (0 : ℝ) ≤ 1728) (by norm_num)
      (by norm_num : (1728 : ℝ) ^ 5 ≤ (2 : ℝ) ^ (9 * 6)) hn
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * h)
    (show (2 * h : ℝ) ≤ k by exact_mod_cast hhk) 2
  exact (show (2654208 * h ^ 2 : ℝ) ≤ 663552 * k ^ 2 by nlinarith only [hs]).trans
    (hpoly.trans hg)

theorem local_typicality_density_tail {r h n : ℕ} (hr : 1 ≤ r) (hh : 1 ≤ h)
    (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n) :
    2 * Real.exp (-((n : ℝ) ^ (13 / 10 : ℝ) / (1769472 * (h : ℝ) ^ 2))) <
      (1 / 2 : ℝ) * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
  have hnNat : 1 ≤ n := (Nat.one_le_pow _ _ (by norm_num)).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  let y := (n : ℝ) ^ (1 / 10 : ℝ)
  have hy0 : 0 < y := Real.rpow_pos_of_pos hn0 _
  have hk : 2 ≤ (r + 1) * h := by nlinarith only [hr, hh]
  have hy3 : 3 ≤ y := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 373 / 200) hk
    exact (show (3 : ℝ) ≤ (373 / 200 : ℝ) ^ 2 by norm_num).trans
      (hp.trans (local_typicality_tenth_lower hn))
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hE : (3 / 2 : ℝ) * y ≤
      (n : ℝ) ^ (13 / 10 : ℝ) / (1769472 * (h : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1769472 * (h : ℝ) ^ 2)).mpr
    have hm := mul_le_mul_of_nonneg_right (local_typicality_density_margin hr hh hn) hy0.le
    have heq : (n : ℝ) ^ (13 / 10 : ℝ) = (n : ℝ) ^ (6 / 5 : ℝ) * y := by
      dsimp only [y]
      rw [← Real.rpow_add hn0]
      norm_num
    rw [heq]
    nlinarith only [hm]
  have hfour : (4 : ℝ) < Real.exp (3 / 2) := by
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) 4
    norm_num [sum_range_succ] at he
    linarith only [he]
  have hexp : 4 * Real.exp (-(3 / 2 : ℝ) * y) < Real.exp (-y) := by
    calc
      _ < Real.exp (y / 2) * Real.exp (-(3 / 2 : ℝ) * y) :=
        mul_lt_mul_of_pos_right (hfour.trans_le
          (Real.exp_le_exp.mpr (by linarith only [hy3]))) (Real.exp_pos _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have ht := Real.exp_le_exp.mpr (neg_le_neg hE)
  rw [neg_mul] at hexp
  change _ < (1 / 2 : ℝ) * Real.exp (-y)
  nlinarith only [ht, hexp]

end Arxiv2411_18291
