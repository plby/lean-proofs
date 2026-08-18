import Mathlib.Analysis.SpecialFunctions.Pochhammer
import Mathlib.Data.Nat.Factorial.BigOperators

open scoped BigOperators

open Finset

noncomputable section

namespace Erdos570

theorem telescoping_product (d : ℕ) (hd : 3 ≤ d) :
    (∏ r ∈ Finset.Ico d (2 * d), (((r - 2 : ℕ) : ℝ) / r)) =
      ((d - 2 : ℕ) : ℝ) / (2 * (2 * d - 1)) := by
  have hd2 : d - 2 + 2 = d := by omega
  have h2d : 2 * d - 2 + 2 = 2 * d := by omega
  have hsplitNum :
      (∏ r ∈ Finset.Ico (d - 2) (2 * d - 2), (r : ℝ)) =
        ((d - 2 : ℕ) : ℝ) * (d - 1) *
          ∏ r ∈ Finset.Ico d (2 * d - 2), (r : ℝ) := by
    calc
      _ = (∏ r ∈ Finset.Ico (d - 2) d, (r : ℝ)) *
          ∏ r ∈ Finset.Ico d (2 * d - 2), (r : ℝ) :=
        (Finset.prod_Ico_consecutive (fun r : ℕ ↦ (r : ℝ))
          (by omega : d - 2 ≤ d) (by omega : d ≤ 2 * d - 2)).symm
      _ = _ := by
        have hn1 : d - 1 + 1 = d := by omega
        have hc1 : (((d - 1 : ℕ) : ℝ)) = (d : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        rw [show Finset.Ico (d - 2) d = {d - 2, d - 1} by ext x; simp; omega]
        have hne : d - 2 ≠ d - 1 := by omega
        simp [hne, hc1, mul_assoc]
  have hsplitDen :
      (∏ r ∈ Finset.Ico d (2 * d), (r : ℝ)) =
        (∏ r ∈ Finset.Ico d (2 * d - 2), (r : ℝ)) *
          (2 * d - 2) * (2 * d - 1) := by
    calc
      _ = (∏ r ∈ Finset.Ico d (2 * d - 2), (r : ℝ)) *
          ∏ r ∈ Finset.Ico (2 * d - 2) (2 * d), (r : ℝ) :=
        (Finset.prod_Ico_consecutive (fun r : ℕ ↦ (r : ℝ))
          (by omega : d ≤ 2 * d - 2) (by omega : 2 * d - 2 ≤ 2 * d)).symm
      _ = _ := by
        have hc1 : (((2 * d - 2 : ℕ) : ℝ)) = 2 * (d : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
        have hc2 : (((2 * d - 1 : ℕ) : ℝ)) = 2 * (d : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
          norm_num
        rw [show Finset.Ico (2 * d - 2) (2 * d) =
          {2 * d - 2, 2 * d - 1} by ext x; simp; omega]
        have hne : 2 * d - 2 ≠ 2 * d - 1 := by omega
        simp [hne, hc1, hc2, mul_assoc]
  rw [Finset.prod_div_distrib]
  have hshift :
      (∏ r ∈ Finset.Ico d (2 * d), (((r - 2 : ℕ) : ℝ))) =
        ∏ r ∈ Finset.Ico (d - 2) (2 * d - 2), (r : ℝ) := by
    simpa [hd2, h2d] using
      (Finset.prod_Ico_add_right_sub_eq (f := fun r : ℕ ↦ (r : ℝ))
        (d - 2) (2 * d - 2) 2)
  rw [hshift, hsplitNum, hsplitDen]
  have hcommon : 0 < ∏ r ∈ Finset.Ico d (2 * d - 2), (r : ℝ) := by
    apply Finset.prod_pos
    intro r hr
    rw [Finset.mem_Ico] at hr
    exact_mod_cast (show 0 < r by omega)
  have hdpos : (0 : ℝ) < d := by positivity
  have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hlast : (0 : ℝ) < 2 * d - 1 := by nlinarith
  have hd1 : (((d - 1 : ℕ) : ℝ)) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hd2c : (((d - 2 : ℕ) : ℝ)) = (d : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [show 2 * (d : ℝ) - 2 = 2 * ((d : ℝ) - 1) by ring]
  have hdm1 : (d : ℝ) - 1 ≠ 0 := by nlinarith
  have h2dm1 : 2 * (d : ℝ) - 1 ≠ 0 := by nlinarith
  have hpoly : 1 - (d : ℝ) * 3 + (d : ℝ) ^ 2 * 2 ≠ 0 := by
    nlinarith [mul_pos (show 0 < (d : ℝ) - 1 by nlinarith) hlast]
  field_simp [ne_of_gt hcommon, hdm1, h2dm1, hpoly]

theorem telescoping_product_reindexed (d : ℕ) (hd : 3 ≤ d) :
    (∏ j ∈ Finset.Icc 1 d,
        (((2 * d - j - 2 : ℕ) : ℝ) / ((2 * d - j : ℕ) : ℝ))) =
      ((d - 2 : ℕ) : ℝ) / (2 * (2 * d - 1)) := by
  rw [← telescoping_product d hd]
  refine Finset.prod_bij'
      (s := Finset.Icc 1 d) (t := Finset.Ico d (2 * d))
      (f := fun j : ℕ ↦ (((2 * d - j - 2 : ℕ) : ℝ) /
        ((2 * d - j : ℕ) : ℝ)))
      (g := fun r : ℕ ↦ (((r - 2 : ℕ) : ℝ) / r))
      (fun j _ ↦ (2 * d - j : ℕ)) (fun r _ ↦ (2 * d - r : ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_Ico]
    omega
  · intro r hr
    rw [Finset.mem_Ico] at hr
    rw [Finset.mem_Icc]
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    omega
  · intro r hr
    simp only [Finset.mem_Ico] at hr
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    rfl

theorem product_lower_large_degree (d t y : ℕ) (hd : 5 ≤ d)
    (ht : 2 * d ≤ t) (hy : d * t ≤ y) :
    (1 : ℝ) / (d + 1) ≤
      ∏ j ∈ Finset.Icc 1 d,
        (1 - (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ))) := by
  have hd3 : 3 ≤ d := by omega
  have hbase := telescoping_product_reindexed d hd3
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have htR : 2 * (d : ℝ) ≤ t := by exact_mod_cast ht
  have hyR : (d : ℝ) * t ≤ y := by exact_mod_cast hy
  have hprod :
      (∏ j ∈ Finset.Icc 1 d,
        (((2 * d - j - 2 : ℕ) : ℝ) /
          ((2 * d - j : ℕ) : ℝ))) ≤
      ∏ j ∈ Finset.Icc 1 d,
        (1 - (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ))) := by
    apply Finset.prod_le_prod
    · intro j hj
      rw [Finset.mem_Icc] at hj
      have hden : 0 < (2 * d - j : ℕ) := by omega
      have hnum : 0 ≤ (2 * d - j - 2 : ℕ) := Nat.zero_le _
      positivity
    · intro j hj
      rw [Finset.mem_Icc] at hj
      have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
      have hjdR : (j : ℝ) ≤ d := by exact_mod_cast hj.2
      have htj : j < t := by omega
      have hdtj : 0 < (t - j : ℕ) := Nat.sub_pos_iff_lt.mpr htj
      have hdenBase : 0 < (2 * d - j : ℕ) := by omega
      have hdenActual : 0 < (y : ℝ) * ((t - j : ℕ) : ℝ) := by
        have hdtpos : 0 < d * t := Nat.mul_pos (by omega) (by omega)
        have hypos : 0 < y := hdtpos.trans_le hy
        positivity
      have hdenTwo : 0 < ((2 * d - j : ℕ) : ℝ) := by positivity
      have htjCast : (((t - j : ℕ) : ℝ)) = (t : ℝ) - j := by
        rw [Nat.cast_sub htj.le]
      have h2djCast : (((2 * d - j : ℕ) : ℝ)) =
          2 * (d : ℝ) - j := by
        rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
      have h2djm2Cast : (((2 * d - j - 2 : ℕ) : ℝ)) =
          2 * (d : ℝ) - j - 2 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_mul,
          Nat.cast_ofNat]
      rw [h2djCast, h2djm2Cast, htjCast]
      have hpos1 : 0 < 2 * (d : ℝ) - j := by nlinarith
      have hpos2 : 0 < (y : ℝ) * ((t : ℝ) - j) := by
        rw [← htjCast]
        exact hdenActual
      have hfirst : (t : ℝ) * (2 * (d : ℝ) - j) ≤
          2 * (d : ℝ) * ((t : ℝ) - j) := by
        nlinarith [mul_nonneg (show 0 ≤ (j : ℝ) by positivity)
          (show 0 ≤ (t : ℝ) - 2 * d by nlinarith)]
      have hsecond :
          2 * (d : ℝ) * (t : ℝ) * ((t : ℝ) - j) ≤
            2 * (y : ℝ) * ((t : ℝ) - j) := by
        have hcoef : 2 * (d : ℝ) * (t : ℝ) ≤ 2 * (y : ℝ) := by
          nlinarith
        exact mul_le_mul_of_nonneg_right hcoef (by nlinarith)
      have hcross :
        (t : ℝ) ^ 2 * (2 * (d : ℝ) - j) =
            (t : ℝ) * ((t : ℝ) * (2 * (d : ℝ) - j)) := by ring
      have hcross' : (t : ℝ) ^ 2 * (2 * (d : ℝ) - j) ≤
          2 * ((y : ℝ) * ((t : ℝ) - j)) := by
        calc
          _ = (t : ℝ) * ((t : ℝ) * (2 * (d : ℝ) - j)) := hcross
          _ ≤ (t : ℝ) * (2 * (d : ℝ) * ((t : ℝ) - j)) := by gcongr
          _ = 2 * (d : ℝ) * (t : ℝ) * ((t : ℝ) - j) := by ring
          _ ≤ 2 * (y : ℝ) * ((t : ℝ) - j) := hsecond
          _ = _ := by ring
      have hfrac : (t : ℝ) ^ 2 / ((y : ℝ) * ((t : ℝ) - j)) ≤
          2 / (2 * (d : ℝ) - j) := by
        rw [div_le_div_iff₀ hpos2 hpos1]
        exact hcross'
      rw [show (2 * (d : ℝ) - j - 2) / (2 * (d : ℝ) - j) =
          1 - 2 / (2 * (d : ℝ) - j) by field_simp]
      linarith
  calc
    (1 : ℝ) / (d + 1) ≤
        ((d - 2 : ℕ) : ℝ) / (2 * (2 * d - 1)) := by
      have hd2c : (((d - 2 : ℕ) : ℝ)) = (d : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hdm : (0 : ℝ) < d + 1 := by positivity
      have hden : (0 : ℝ) < 2 * (2 * d - 1) := by nlinarith
      rw [hd2c, div_le_div_iff₀ hdm hden]
      nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) by positivity)
        (show 0 ≤ (d : ℝ) - 5 by nlinarith)]
    _ ≤ _ := hbase.symm.trans_le hprod

theorem product_lower_degree_four (t y : ℕ) (ht : 7 ≤ t)
    (hy : 31 * (t + 1) ≤ 9 * y) :
    (1 : ℝ) / 4 ≤
      ∏ j ∈ Finset.Icc 1 3,
        (1 - (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ))) := by
  let L : ℕ → ℝ := fun j ↦
    1 - 9 * (t : ℝ) ^ 2 /
      (31 * ((t : ℝ) + 1) * ((t - j : ℕ) : ℝ))
  have htR : (7 : ℝ) ≤ t := by exact_mod_cast ht
  have hyR : 31 * ((t : ℝ) + 1) ≤ 9 * (y : ℝ) := by
    exact_mod_cast hy
  have hprod : (∏ j ∈ Finset.Icc 1 3, L j) ≤
      ∏ j ∈ Finset.Icc 1 3,
        (1 - (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ))) := by
    apply Finset.prod_le_prod
    · intro j hj
      rw [Finset.mem_Icc] at hj
      dsimp only [L]
      have htj : j < t := by omega
      have htjR : (0 : ℝ) < ((t - j : ℕ) : ℝ) := by
        exact_mod_cast (Nat.sub_pos_iff_lt.mpr htj)
      have hden : 9 * (t : ℝ) ^ 2 ≤
          31 * ((t : ℝ) + 1) * ((t - j : ℕ) : ℝ) := by
        have hjR : (j : ℝ) ≤ 3 := by exact_mod_cast hj.2
        have htjCast : (((t - j : ℕ) : ℝ)) = (t : ℝ) - j := by
          rw [Nat.cast_sub htj.le]
        rw [htjCast]
        nlinarith [mul_nonneg (show 0 ≤ (t : ℝ) - 7 by nlinarith)
          (show 0 ≤ 22 * (t : ℝ) - 31 by nlinarith)]
      have hdenpos : 0 < 31 * ((t : ℝ) + 1) *
          ((t - j : ℕ) : ℝ) := by positivity
      exact sub_nonneg.mpr (div_le_one hdenpos |>.mpr hden)
    · intro j hj
      rw [Finset.mem_Icc] at hj
      dsimp only [L]
      have htj : j < t := by omega
      have hty : 0 < y := by omega
      have hposj : 0 < ((t - j : ℕ) : ℝ) := by
        exact_mod_cast (Nat.sub_pos_iff_lt.mpr htj)
      have hden1 : 0 < (y : ℝ) * ((t - j : ℕ) : ℝ) := by positivity
      have hden2 : 0 < 31 * ((t : ℝ) + 1) *
          ((t - j : ℕ) : ℝ) := by positivity
      have hfrac : (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ)) ≤
          9 * (t : ℝ) ^ 2 /
            (31 * ((t : ℝ) + 1) * ((t - j : ℕ) : ℝ)) := by
        rw [div_le_div_iff₀ hden1 hden2]
        have ht2 : 0 ≤ (t : ℝ) ^ 2 := sq_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hyR ht2
        have hmul' := mul_le_mul_of_nonneg_right hmul hposj.le
        nlinarith [hmul']
      linarith
  have hL : (1 : ℝ) / 4 ≤ ∏ j ∈ Finset.Icc 1 3, L j := by
    have hI : Finset.Icc 1 3 = {1, 2, 3} := by decide
    rw [hI]
    norm_num [Finset.prod_insert]
    dsimp only [L]
    have h1 : (0 : ℝ) < (t : ℝ) - 1 := by nlinarith
    have h2 : (0 : ℝ) < (t : ℝ) - 2 := by nlinarith
    have h3 : (0 : ℝ) < (t : ℝ) - 3 := by nlinarith
    rw [show (((t - 1 : ℕ) : ℝ)) = (t : ℝ) - 1 by
      rw [Nat.cast_sub (by omega)]; norm_num]
    rw [show (((t - 2 : ℕ) : ℝ)) = (t : ℝ) - 2 by
      rw [Nat.cast_sub (by omega)]; norm_num]
    rw [show (((t - 3 : ℕ) : ℝ)) = (t : ℝ) - 3 by
      rw [Nat.cast_sub (by omega)]; norm_num]
    field_simp
    let x : ℝ := (t : ℝ) - 7
    have hx : 0 ≤ x := by dsimp [x]; nlinarith
    have hpoly : 0 ≤
        4267 * x ^ 6 + 148989 * x ^ 5 + 2054438 * x ^ 4 +
          13973864 * x ^ 3 + 46943904 * x ^ 2 + 63216916 * x + 4467924 := by
      positivity
    dsimp [x] at hpoly
    nlinarith [hpoly]
  exact hL.trans hprod

theorem product_lower_degree_five (t y : ℕ) (ht : 9 ≤ t)
    (hy : 49 * (t + 1) ≤ 11 * y) :
    (1 : ℝ) / 5 ≤
      ∏ j ∈ Finset.Icc 1 4,
        (1 - (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ))) := by
  let L : ℕ → ℝ := fun j ↦
    1 - 11 * (t : ℝ) ^ 2 /
      (49 * ((t : ℝ) + 1) * ((t - j : ℕ) : ℝ))
  have htR : (9 : ℝ) ≤ t := by exact_mod_cast ht
  have hyR : 49 * ((t : ℝ) + 1) ≤ 11 * (y : ℝ) := by
    exact_mod_cast hy
  have hprod : (∏ j ∈ Finset.Icc 1 4, L j) ≤
      ∏ j ∈ Finset.Icc 1 4,
        (1 - (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ))) := by
    apply Finset.prod_le_prod
    · intro j hj
      rw [Finset.mem_Icc] at hj
      dsimp only [L]
      have htj : j < t := by omega
      have htjR : (0 : ℝ) < ((t - j : ℕ) : ℝ) := by
        exact_mod_cast (Nat.sub_pos_iff_lt.mpr htj)
      have hden : 11 * (t : ℝ) ^ 2 ≤
          49 * ((t : ℝ) + 1) * ((t - j : ℕ) : ℝ) := by
        have hjR : (j : ℝ) ≤ 4 := by exact_mod_cast hj.2
        have htjCast : (((t - j : ℕ) : ℝ)) = (t : ℝ) - j := by
          rw [Nat.cast_sub htj.le]
        rw [htjCast]
        nlinarith [mul_nonneg (show 0 ≤ (t : ℝ) - 9 by nlinarith)
          (show 0 ≤ 38 * (t : ℝ) + 195 by positivity)]
      have hdenpos : 0 < 49 * ((t : ℝ) + 1) *
          ((t - j : ℕ) : ℝ) := by positivity
      exact sub_nonneg.mpr (div_le_one hdenpos |>.mpr hden)
    · intro j hj
      rw [Finset.mem_Icc] at hj
      dsimp only [L]
      have htj : j < t := by omega
      have hty : 0 < y := by omega
      have hposj : 0 < ((t - j : ℕ) : ℝ) := by
        exact_mod_cast (Nat.sub_pos_iff_lt.mpr htj)
      have hden1 : 0 < (y : ℝ) * ((t - j : ℕ) : ℝ) := by positivity
      have hden2 : 0 < 49 * ((t : ℝ) + 1) *
          ((t - j : ℕ) : ℝ) := by positivity
      have hfrac : (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ)) ≤
          11 * (t : ℝ) ^ 2 /
            (49 * ((t : ℝ) + 1) * ((t - j : ℕ) : ℝ)) := by
        rw [div_le_div_iff₀ hden1 hden2]
        have ht2 : 0 ≤ (t : ℝ) ^ 2 := sq_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hyR ht2
        have hmul' := mul_le_mul_of_nonneg_right hmul hposj.le
        nlinarith [hmul']
      linarith
  have hL : (1 : ℝ) / 5 ≤ ∏ j ∈ Finset.Icc 1 4, L j := by
    have hI : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
    rw [hI]
    norm_num [Finset.prod_insert]
    dsimp only [L]
    have h1 : (0 : ℝ) < (t : ℝ) - 1 := by nlinarith
    have h2 : (0 : ℝ) < (t : ℝ) - 2 := by nlinarith
    have h3 : (0 : ℝ) < (t : ℝ) - 3 := by nlinarith
    have h4 : (0 : ℝ) < (t : ℝ) - 4 := by nlinarith
    rw [show (((t - 1 : ℕ) : ℝ)) = (t : ℝ) - 1 by
      rw [Nat.cast_sub (by omega)]; norm_num]
    rw [show (((t - 2 : ℕ) : ℝ)) = (t : ℝ) - 2 by
      rw [Nat.cast_sub (by omega)]; norm_num]
    rw [show (((t - 3 : ℕ) : ℝ)) = (t : ℝ) - 3 by
      rw [Nat.cast_sub (by omega)]; norm_num]
    rw [show (((t - 4 : ℕ) : ℝ)) = (t : ℝ) - 4 by
      rw [Nat.cast_sub (by omega)]; norm_num]
    field_simp
    let x : ℝ := (t : ℝ) - 9
    have hx : 0 ≤ x := by dsimp [x]; nlinarith
    have hpoly : 0 ≤
        4660879 * x ^ 8 + 289510254 * x ^ 7 + 7718758649 * x ^ 6 +
          114995034994 * x ^ 5 + 1042478472980 * x ^ 4 +
          5852205549750 * x ^ 3 + 19682633182835 * x ^ 2 +
          35706876331390 * x + 25985755453605 := by
      positivity
    dsimp [x] at hpoly
    nlinarith [hpoly]
  exact hL.trans hprod

/-- The explicit degree-three estimate in Goddard--Kleitman's candidate
average.  The integer form of the lower bound for `y` avoids all rounding. -/
theorem product_lower_degree_three (t y : ℕ) (ht : 7 ≤ t)
    (hy : 17 * t + 31 ≤ 7 * y) :
    (1 : ℝ) / 3 ≤
      ∏ j ∈ Finset.Icc 1 2,
        (1 - (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ))) := by
  let L : ℕ → ℝ := fun j ↦
    1 - 7 * (t : ℝ) ^ 2 /
      ((17 * (t : ℝ) + 31) * ((t - j : ℕ) : ℝ))
  have htR : (7 : ℝ) ≤ t := by exact_mod_cast ht
  have hyR : 17 * (t : ℝ) + 31 ≤ 7 * (y : ℝ) := by
    exact_mod_cast hy
  have hprod : (∏ j ∈ Finset.Icc 1 2, L j) ≤
      ∏ j ∈ Finset.Icc 1 2,
        (1 - (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ))) := by
    apply Finset.prod_le_prod
    · intro j hj
      rw [Finset.mem_Icc] at hj
      dsimp only [L]
      have htj : j < t := by omega
      have htjR : (0 : ℝ) < ((t - j : ℕ) : ℝ) := by
        exact_mod_cast (Nat.sub_pos_iff_lt.mpr htj)
      have hden : 7 * (t : ℝ) ^ 2 ≤
          (17 * (t : ℝ) + 31) * ((t - j : ℕ) : ℝ) := by
        have hjR : (j : ℝ) ≤ 2 := by exact_mod_cast hj.2
        have htjCast : (((t - j : ℕ) : ℝ)) = (t : ℝ) - j := by
          rw [Nat.cast_sub htj.le]
        rw [htjCast]
        nlinarith [mul_nonneg (show 0 ≤ (t : ℝ) - 7 by nlinarith)
          (show 0 ≤ 10 * (t : ℝ) - 31 by nlinarith)]
      have hdenpos : 0 < (17 * (t : ℝ) + 31) *
          ((t - j : ℕ) : ℝ) := by positivity
      exact sub_nonneg.mpr (div_le_one hdenpos |>.mpr hden)
    · intro j hj
      rw [Finset.mem_Icc] at hj
      dsimp only [L]
      have htj : j < t := by omega
      have hty : 0 < y := by omega
      have hposj : 0 < ((t - j : ℕ) : ℝ) := by
        exact_mod_cast (Nat.sub_pos_iff_lt.mpr htj)
      have hden1 : 0 < (y : ℝ) * ((t - j : ℕ) : ℝ) := by positivity
      have hden2 : 0 < (17 * (t : ℝ) + 31) *
          ((t - j : ℕ) : ℝ) := by positivity
      have hfrac : (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ)) ≤
          7 * (t : ℝ) ^ 2 /
            ((17 * (t : ℝ) + 31) * ((t - j : ℕ) : ℝ)) := by
        rw [div_le_div_iff₀ hden1 hden2]
        have ht2 : 0 ≤ (t : ℝ) ^ 2 := sq_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hyR ht2
        have hmul' := mul_le_mul_of_nonneg_right hmul hposj.le
        nlinarith [hmul']
      linarith
  have hL : (1 : ℝ) / 3 ≤ ∏ j ∈ Finset.Icc 1 2, L j := by
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hI]
    norm_num [Finset.prod_insert]
    dsimp only [L]
    rw [show (((t - 1 : ℕ) : ℝ)) = (t : ℝ) - 1 by
      rw [Nat.cast_sub (by omega)]; norm_num]
    rw [show (((t - 2 : ℕ) : ℝ)) = (t : ℝ) - 2 by
      rw [Nat.cast_sub (by omega)]; norm_num]
    have h1 : (0 : ℝ) < (t : ℝ) - 1 := by nlinarith
    have h2 : (0 : ℝ) < (t : ℝ) - 2 := by nlinarith
    have hden : (0 : ℝ) < 17 * (t : ℝ) + 31 := by positivity
    field_simp
    let x : ℝ := (t : ℝ) - 7
    have hx : 0 ≤ x := by dsimp [x]; nlinarith
    have hpoly : 0 ≤
        480 * x ^ 4 + 13704 * x ^ 3 + 143769 * x ^ 2 +
          654255 * x + 1080450 := by positivity
    dsimp [x] at hpoly
    nlinarith [hpoly]
  exact hL.trans hprod

theorem pochhammer_candidate_ratio (δ t y : ℕ) (hδ : 1 ≤ δ)
    (hδt : δ ≤ t) (hty : t < y) :
    (descPochhammer ℝ δ).eval
        ((t : ℝ) * ((y - t : ℕ) : ℝ) / y) =
      (((y - t : ℕ) : ℝ) / y) *
        (descPochhammer ℝ δ).eval (t : ℝ) *
          (∏ j ∈ Finset.Icc 1 (δ - 1),
            (1 - (t : ℝ) ^ 2 /
              ((y : ℝ) * ((t - j : ℕ) : ℝ)))) := by
  have hypos : (0 : ℝ) < y := by exact_mod_cast (Nat.zero_lt_of_lt hty)
  rw [descPochhammer_eval_eq_prod_range,
    descPochhammer_eval_eq_prod_range]
  have hrange : Finset.range δ = insert 0 (Finset.Icc 1 (δ - 1)) := by
    ext j
    simp
    omega
  rw [hrange]
  have hz : 0 ∉ Finset.Icc 1 (δ - 1) := by simp
  rw [Finset.prod_insert hz, Finset.prod_insert hz]
  simp only [Nat.cast_zero, sub_zero]
  have hprod :
      (∏ j ∈ Finset.Icc 1 (δ - 1),
          ((t : ℝ) * ((y - t : ℕ) : ℝ) / y - j)) =
        (∏ j ∈ Finset.Icc 1 (δ - 1), ((t - j : ℕ) : ℝ)) *
          ∏ j ∈ Finset.Icc 1 (δ - 1),
            (1 - (t : ℝ) ^ 2 /
              ((y : ℝ) * ((t - j : ℕ) : ℝ))) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hjt : j < t := by omega
    have htjpos : (0 : ℝ) < ((t - j : ℕ) : ℝ) := by
      exact_mod_cast (Nat.sub_pos_iff_lt.mpr hjt)
    have htjCast : (((t - j : ℕ) : ℝ)) = (t : ℝ) - j := by
      rw [Nat.cast_sub hjt.le]
    have hytCast : (((y - t : ℕ) : ℝ)) = (y : ℝ) - t := by
      rw [Nat.cast_sub hty.le]
    rw [htjCast, hytCast]
    have htjNe : (t : ℝ) - j ≠ 0 := by
      rw [← htjCast]
      positivity
    field_simp [ne_of_gt htjpos, ne_of_gt hypos, htjNe]
    <;> ring
  rw [hprod]
  have hfallCast :
      (∏ j ∈ Finset.Icc 1 (δ - 1), ((t - j : ℕ) : ℝ)) =
        ∏ j ∈ Finset.Icc 1 (δ - 1), ((t : ℝ) - j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Nat.cast_sub (by omega)]
  rw [← hfallCast]
  ring

theorem binomial_candidate_average
    {Y : Type*} [Fintype Y] (deg : Y → ℕ) (δ t y : ℕ)
    (hcard : Fintype.card Y = y) (hδ : 1 ≤ δ) (hδt : δ ≤ t)
    (hty : t < y)
    (hsum : ∑ z : Y, deg z = t * (y - t))
    (havg : (δ - 1 : ℕ) ≤ t * (y - t) / y)
    (hprod : (1 : ℝ) / δ ≤
      ∏ j ∈ Finset.Icc 1 (δ - 1),
        (1 - (t : ℝ) ^ 2 /
          ((y : ℝ) * ((t - j : ℕ) : ℝ)))) :
    (y - t) * t.choose δ ≤ δ * ∑ z : Y, (deg z).choose δ := by
  classical
  have hyposN : 0 < y := Nat.zero_lt_of_lt hty
  have hypos : (0 : ℝ) < y := by exact_mod_cast hyposN
  have hδpos : (0 : ℝ) < δ := by positivity
  let w : Y → ℝ := fun _ ↦ 1 / y
  have hw0 : ∀ z ∈ (Finset.univ : Finset Y), 0 ≤ w z := by
    intro z hz
    dsimp [w]
    positivity
  have hw1 : ∑ z ∈ (Finset.univ : Finset Y), w z = 1 := by
    simp [w, hcard]
    field_simp
  have havgEq : ∑ z ∈ (Finset.univ : Finset Y), w z * deg z =
      (t : ℝ) * ((y - t : ℕ) : ℝ) / y := by
    change (∑ z : Y, (1 / (y : ℝ)) * (deg z : ℝ)) = _
    calc
      _ = (1 / (y : ℝ)) * ∑ z : Y, (deg z : ℝ) := by
        simpa using (Finset.mul_sum (Finset.univ : Finset Y)
          (fun z ↦ (deg z : ℝ)) (1 / (y : ℝ))).symm
      _ = (1 / (y : ℝ)) * (t * (y - t) : ℕ) := by
        rw [← Nat.cast_sum, hsum]
      _ = _ := by push_cast; ring
  have havgR : (δ - 1 : ℕ) ≤ ∑ z ∈ (Finset.univ : Finset Y), w z * deg z := by
    rw [havgEq]
    have havgCast : (((t * (y - t) / y : ℕ) : ℝ)) ≤
        (t : ℝ) * ((y - t : ℕ) : ℝ) / y := by
      simpa only [Nat.cast_mul] using
        (Nat.cast_div_le (α := ℝ) (n := y) (m := t * (y - t)))
    have havgReal : (((δ - 1 : ℕ) : ℝ)) ≤
        (((t * (y - t) / y : ℕ) : ℝ)) := by exact_mod_cast havg
    exact havgReal.trans havgCast
  have hJ := descPochhammer_eval_div_factorial_le_sum_choose
    (n := δ) (t := (Finset.univ : Finset Y)) (by omega : δ ≠ 0) deg w
    hw0 hw1 (by
      have hcastPred : (((δ - 1 : ℕ) : ℝ)) = (δ : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rwa [← hcastPred])
  rw [havgEq] at hJ
  simp only [Finset.mem_univ, w] at hJ
  have hratio := pochhammer_candidate_ratio δ t y hδ hδt hty
  have hchoose : ((t.choose δ : ℕ) : ℝ) =
      (descPochhammer ℝ δ).eval (t : ℝ) / δ.factorial :=
    Nat.cast_choose_eq_descPochhammer_div (K := ℝ) t δ
  have hnonneg : 0 ≤ (((y - t : ℕ) : ℝ) / y) * (t.choose δ : ℝ) := by
    positivity
  have hlow :
      (((y - t : ℕ) : ℝ) / y) * (t.choose δ : ℝ) *
          ((1 : ℝ) / δ) ≤
        (descPochhammer ℝ δ).eval
          ((t : ℝ) * ((y - t : ℕ) : ℝ) / y) / δ.factorial := by
    rw [hratio]
    have hfact : (0 : ℝ) < δ.factorial := by positivity
    calc
      _ ≤ (((y - t : ℕ) : ℝ) / y) *
          (t.choose δ : ℝ) *
            (∏ j ∈ Finset.Icc 1 (δ - 1),
              (1 - (t : ℝ) ^ 2 /
                ((y : ℝ) * ((t - j : ℕ) : ℝ)))) := by
          exact mul_le_mul_of_nonneg_left hprod hnonneg
      _ = ((((y - t : ℕ) : ℝ) / y) *
          ((descPochhammer ℝ δ).eval (t : ℝ) / δ.factorial) *
            (∏ j ∈ Finset.Icc 1 (δ - 1),
              (1 - (t : ℝ) ^ 2 /
                ((y : ℝ) * ((t - j : ℕ) : ℝ))))) := by rw [← hchoose]
      _ = _ := by ring
  have hJ' :
      (descPochhammer ℝ δ).eval
          ((t : ℝ) * ((y - t : ℕ) : ℝ) / y) / δ.factorial ≤
        ∑ z : Y, ((deg z).choose δ : ℝ) / y := by
    simpa [div_eq_mul_inv, mul_comm] using hJ
  have hsumR : (((y - t : ℕ) : ℝ) / y) * (t.choose δ : ℝ) *
      ((1 : ℝ) / δ) ≤
        ∑ z : Y, ((deg z).choose δ : ℝ) / y := hlow.trans hJ'
  have hcast : (((y - t) * t.choose δ : ℕ) : ℝ) ≤
      ((δ * ∑ z : Y, (deg z).choose δ : ℕ) : ℝ) := by
    have hδne : (δ : ℝ) ≠ 0 := ne_of_gt hδpos
    have hyne : (y : ℝ) ≠ 0 := ne_of_gt hypos
    rw [← Finset.sum_div] at hsumR
    simp only [Nat.cast_mul, Nat.cast_sum]
    field_simp [hδne, hyne] at hsumR ⊢
    nlinarith
  exact_mod_cast hcast

end Erdos570
