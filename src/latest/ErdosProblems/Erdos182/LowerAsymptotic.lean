/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Analytic estimates for the layered PRS construction

This file contains the real-analytic and rounding estimates used in the
layered Pyber--Rődl--Szemerédi lower-bound construction.  Layers are
numbered from zero: layer `0` has real size `n / 2`, while layer `i` has
the scale called `a_(i+1)` in the mathematical write-up.
-/

open Filter Finset
open scoped Nat

namespace Erdos182

private theorem prs_natCast_choose_le_three_mul_div_pow (n k : ℕ) :
    (n.choose k : ℝ) ≤ (3 * (n : ℝ) / (k : ℝ)) ^ k := by
  by_cases hk : k = 0
  · subst k
    simp
  by_cases hkn : n < k
  · rw [Nat.choose_eq_zero_of_lt hkn]
    simpa only [Nat.cast_zero] using
      (pow_nonneg (by positivity : 0 ≤ 3 * (n : ℝ) / (k : ℝ)) k)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hfacpos : (0 : ℝ) < k ! := by positivity
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * k) := by
    rw [Real.one_le_sqrt]
    have hpi : (3 : ℝ) ≤ Real.pi := (Real.pi_gt_three : (3 : ℝ) < Real.pi).le
    nlinarith [show (1 : ℝ) ≤ k by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk]
  have hstirling : ((k : ℝ) / Real.exp 1) ^ k ≤ (k ! : ℝ) := by
    calc
      ((k : ℝ) / Real.exp 1) ^ k ≤
          Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k := by
        exact le_mul_of_one_le_left (by positivity) hsqrt
      _ ≤ (k ! : ℝ) := Stirling.le_factorial_stirling k
  have hchoose : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (k ! : ℝ) :=
    Nat.choose_le_pow_div k n
  calc
    (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (k ! : ℝ) := hchoose
    _ ≤ (n : ℝ) ^ k / (((k : ℝ) / Real.exp 1) ^ k) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hstirling
    _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
      simp only [div_pow]
      field_simp
      <;> ring
    _ ≤ (3 * (n : ℝ) / (k : ℝ)) ^ k := by
      gcongr
      exact Real.exp_one_lt_three.le

/-- The two binomial estimates, collected in the exact form needed by the
bad-event union bound. -/
lemma prs_choose_bridge_core
    (n x B r : ℕ) (E : ℝ)
    (hx : 0 < x) (hB : 0 < B)
    (hr : 11 * x ≤ 10 * r)
    (hbase : 3 * (x : ℝ) / (2 * (B : ℝ)) ≤ 1)
    (hE : 3 * (n : ℝ) / (x : ℝ) *
      (3 * (x : ℝ) / (2 * (B : ℝ))) ^ (11 / 10 : ℝ) ≤ E) :
    (n.choose x : ℝ) * ((x.choose 2).choose r : ℝ) / (B : ℝ) ^ r ≤ E ^ x := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hrR : (11 / 10 : ℝ) * x ≤ r := by
    have hr' : (11 : ℝ) * x ≤ 10 * r := by exact_mod_cast hr
    nlinarith
  have hxr : x ≤ r := by omega
  have hrpos : (0 : ℝ) < r := by exact_mod_cast lt_of_lt_of_le hx hxr
  have hchoose2 : (x.choose 2 : ℝ) ≤ (x : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith
  have hsecondbase :
      3 * (x.choose 2 : ℝ) / (r : ℝ) / (B : ℝ) ≤
        3 * (x : ℝ) / (2 * (B : ℝ)) := by
    calc
      3 * (x.choose 2 : ℝ) / (r : ℝ) / (B : ℝ)
          ≤ 3 * ((x : ℝ) ^ 2 / 2) / (r : ℝ) / (B : ℝ) := by gcongr
      _ ≤ 3 * (x : ℝ) / (2 * (B : ℝ)) := by
        have hxrR : (x : ℝ) ≤ r := by exact_mod_cast hxr
        rw [div_le_iff₀ hBR, div_le_iff₀ hrpos]
        field_simp
        nlinarith
  have hbasepos : 0 < 3 * (x : ℝ) / (2 * (B : ℝ)) := by positivity
  have hchoose1 := prs_natCast_choose_le_three_mul_div_pow n x
  have hchoose2r := prs_natCast_choose_le_three_mul_div_pow (x.choose 2) r
  have hdecay :
      (3 * (x : ℝ) / (2 * (B : ℝ))) ^ r ≤
        (3 * (x : ℝ) / (2 * (B : ℝ))) ^ ((11 / 10 : ℝ) * x) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hbasepos hbase hrR
  have hfactor :
      (3 * (n : ℝ) / (x : ℝ)) ^ x *
          (3 * (x : ℝ) / (2 * (B : ℝ))) ^ ((11 / 10 : ℝ) * x) =
        (3 * (n : ℝ) / (x : ℝ) *
          (3 * (x : ℝ) / (2 * (B : ℝ))) ^ (11 / 10 : ℝ)) ^ x := by
    rw [mul_pow]
    congr 1
    exact Real.rpow_mul_natCast hbasepos.le (11 / 10 : ℝ) x
  calc
    (n.choose x : ℝ) * ((x.choose 2).choose r : ℝ) / (B : ℝ) ^ r
        = (n.choose x : ℝ) *
            (((x.choose 2).choose r : ℝ) / (B : ℝ) ^ r) := by ring
    _ ≤ (3 * (n : ℝ) / (x : ℝ)) ^ x *
          ((3 * (x.choose 2 : ℝ) / (r : ℝ)) ^ r / (B : ℝ) ^ r) := by
      gcongr
    _ = (3 * (n : ℝ) / (x : ℝ)) ^ x *
          (3 * (x.choose 2 : ℝ) / (r : ℝ) / (B : ℝ)) ^ r := by
      congr 1
      exact (div_pow (3 * (x.choose 2 : ℝ) / (r : ℝ)) (B : ℝ) r).symm
    _ ≤ (3 * (n : ℝ) / (x : ℝ)) ^ x *
          (3 * (x : ℝ) / (2 * (B : ℝ))) ^ r := by gcongr
    _ ≤ (3 * (n : ℝ) / (x : ℝ)) ^ x *
          (3 * (x : ℝ) / (2 * (B : ℝ))) ^ ((11 / 10 : ℝ) * x) := by gcongr
    _ = (3 * (n : ℝ) / (x : ℝ) *
          (3 * (x : ℝ) / (2 * (B : ℝ))) ^ (11 / 10 : ℝ)) ^ x := hfactor
    _ ≤ E ^ x := by gcongr

/-- The elementary base appearing in `prs_choose_bridge_core` is bounded
by the cleaner layer-size bracket. -/
lemma prs_choose_base_le_badEvent_bracket
    {n x b B : ℕ} (hx : 0 < x) (hb : 0 < b) (hB : 0 < B)
    (hxb : x ≤ 1000 * b) :
    3 * (n : ℝ) / (x : ℝ) *
        (3 * (x : ℝ) / (2 * (B : ℝ))) ^ (11 / 10 : ℝ) ≤
      20 * (n : ℝ) * (b : ℝ) ^ (1 / 10 : ℝ) /
        (B : ℝ) ^ (11 / 10 : ℝ) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hxle : (x : ℝ) ≤ 1000 * (b : ℝ) := by exact_mod_cast hxb
  have hroot1000 : (1000 : ℝ) ^ (1 / 10 : ℝ) ≤ 2 := by
    calc
      (1000 : ℝ) ^ (1 / 10 : ℝ) ≤
          ((2 : ℝ) ^ 10) ^ (1 / 10 : ℝ) := by
        exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  have hxroot : (x : ℝ) ^ (1 / 10 : ℝ) ≤
      2 * (b : ℝ) ^ (1 / 10 : ℝ) := by
    calc
      (x : ℝ) ^ (1 / 10 : ℝ) ≤
          (1000 * (b : ℝ)) ^ (1 / 10 : ℝ) :=
        Real.rpow_le_rpow hxR.le hxle (by norm_num)
      _ = (1000 : ℝ) ^ (1 / 10 : ℝ) *
          (b : ℝ) ^ (1 / 10 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) hbR.le]
      _ ≤ 2 * (b : ℝ) ^ (1 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_right hroot1000 (Real.rpow_nonneg hbR.le _)
  have hc : ((3 : ℝ) / 2) ^ (11 / 10 : ℝ) ≤ 3 := by
    calc
      ((3 : ℝ) / 2) ^ (11 / 10 : ℝ) ≤ ((3 : ℝ) / 2) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 9 / 4 := by norm_num [Real.rpow_two]
      _ ≤ 3 := by norm_num
  have hq :
      (3 * (x : ℝ) / (2 * (B : ℝ))) ^ (11 / 10 : ℝ) =
        ((3 : ℝ) / 2) ^ (11 / 10 : ℝ) *
          (x : ℝ) ^ (11 / 10 : ℝ) /
            (B : ℝ) ^ (11 / 10 : ℝ) := by
    rw [show 3 * (x : ℝ) / (2 * (B : ℝ)) =
      ((3 : ℝ) / 2 * (x : ℝ)) / (B : ℝ) by field_simp]
    rw [Real.div_rpow (by positivity) hBR.le, Real.mul_rpow (by positivity) hxR.le]
  have hxsplit : (x : ℝ) ^ (11 / 10 : ℝ) =
      (x : ℝ) * (x : ℝ) ^ (1 / 10 : ℝ) := by
    rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num,
      Real.rpow_add hxR, Real.rpow_one]
  rw [hq, hxsplit]
  have hden : 0 < (B : ℝ) ^ (11 / 10 : ℝ) := Real.rpow_pos_of_pos hBR _
  have hc' : 3 * (((3 : ℝ) / 2) ^ (11 / 10 : ℝ)) ≤ 9 := by nlinarith
  have hroot' : 9 * (x : ℝ) ^ (1 / 10 : ℝ) ≤
      18 * (b : ℝ) ^ (1 / 10 : ℝ) := by
    nlinarith [hxroot]
  field_simp [hxR.ne', hden.ne']
  have hcombine :
      3 * (((3 : ℝ) / 2) ^ (11 / 10 : ℝ)) *
          (x : ℝ) ^ (1 / 10 : ℝ) ≤
        20 * (b : ℝ) ^ (1 / 10 : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hc'
      (Real.rpow_nonneg hxR.le (1 / 10 : ℝ))
    have hbpow : 0 ≤ (b : ℝ) ^ (1 / 10 : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg b) _
    nlinarith [h1, hroot']
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left hcombine (Nat.cast_nonneg n)

/-- The logarithmic number of layers in the PRS construction. -/
noncomputable def prsLayerCount (n : ℕ) : ℕ :=
  ⌊Real.log (Real.log (n : ℝ)) / 10⌋₊

/-- The square-root logarithmic scale in the PRS construction. -/
noncomputable def prsY (n : ℕ) : ℝ :=
  Real.sqrt (Real.log (n : ℝ))

/-- The unrounded size of the layer numbered `i`. -/
noncomputable def prsRealLayerSize (n i : ℕ) : ℝ :=
  (n : ℝ) / 2 * Real.exp (-(((20 ^ (i + 1) - 20 : ℕ) : ℝ) * prsY n))

/-- The integer size of the layer numbered `i`. -/
noncomputable def prsLayerSize (n i : ℕ) : ℕ :=
  ⌊prsRealLayerSize n i⌋₊

/-- `ceil (11x/10)`, written without a real-valued ceiling. -/
def prsBadEdgeCount (x : ℕ) : ℕ :=
  (11 * x + 9) / 10

lemma eleven_mul_le_ten_mul_prsBadEdgeCount (x : ℕ) :
    11 * x ≤ 10 * prsBadEdgeCount x := by
  simp only [prsBadEdgeCount]
  omega

@[simp] lemma prsRealLayerSize_zero (n : ℕ) :
    prsRealLayerSize n 0 = (n : ℝ) / 2 := by
  simp [prsRealLayerSize]

@[simp] lemma prsLayerSize_zero (n : ℕ) :
    prsLayerSize n 0 = n / 2 := by
  simp only [prsLayerSize, prsRealLayerSize_zero]
  simpa using (Nat.floor_div_natCast (n : ℝ) 2)

/-- Logarithm of an unrounded layer size. -/
lemma log_prsRealLayerSize {n i : ℕ} (hn : 0 < n) :
    Real.log (prsRealLayerSize n i) =
      Real.log (n : ℝ) - Real.log 2 -
        ((20 ^ (i + 1) - 20 : ℕ) : ℝ) * prsY n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [prsRealLayerSize, Real.log_mul (div_ne_zero hnr.ne' (by norm_num))
      (Real.exp_ne_zero _), Real.log_div hnr.ne' (by norm_num), Real.log_exp]
  ring

/-- The layer count tends to infinity. -/
lemma tendsto_prsLayerCount_atTop : Tendsto prsLayerCount atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop |>.const_mul_atTop
      (show 0 < (10 : ℝ)⁻¹ by positivity)) |>.comp tendsto_natCast_atTop_atTop |>.congr'
        (by filter_upwards [] with n; simp [div_eq_mul_inv, mul_comm]))

lemma eventually_two_le_prsLayerCount : ∀ᶠ n : ℕ in atTop, 2 ≤ prsLayerCount n :=
  tendsto_prsLayerCount_atTop.eventually_ge_atTop 2

/-- The square-root logarithmic scale tends to infinity. -/
lemma tendsto_prsY_atTop : Tendsto prsY atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma eventually_prsY_pos : ∀ᶠ n : ℕ in atTop, 0 < prsY n :=
  tendsto_prsY_atTop.eventually_gt_atTop 0

private lemma log_twenty_lt_four : Real.log 20 < 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 20)]
  calc
    (20 : ℝ) < (2.7 : ℝ) ^ 4 := by norm_num
    _ < (2.7182818283 : ℝ) ^ 4 := by
      exact pow_lt_pow_left₀ (by norm_num) (by norm_num)
        (by norm_num : (4 : ℕ) ≠ 0)
    _ < (Real.exp 1) ^ 4 := by
      exact pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num)
        (by norm_num : (4 : ℕ) ≠ 0)
    _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num

/-- The largest power of twenty occurring among the active layers is at
most a two-fifths power of `log n`.  The deliberately loose exponent leaves
room for the square-root factor in the definition of the layer sizes. -/
lemma prs_twenty_pow_le {n i : ℕ}
    (hL : 1 ≤ Real.log (n : ℝ)) (hi : i < prsLayerCount n) :
    ((20 ^ (i + 1) : ℕ) : ℝ) ≤ (Real.log (n : ℝ)) ^ (2 / 5 : ℝ) := by
  have hiC : i + 1 ≤ prsLayerCount n := Nat.succ_le_iff.mpr hi
  have hpow : (20 : ℝ) ^ (i + 1) ≤ (20 : ℝ) ^ prsLayerCount n := by
    exact pow_le_pow_right₀ (by norm_num) hiC
  have hlogL : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg hL
  have hC : (prsLayerCount n : ℝ) ≤ Real.log (Real.log (n : ℝ)) / 10 := by
    exact_mod_cast Nat.floor_le (div_nonneg hlogL (by norm_num))
  have hexponent :
      Real.log 20 * (prsLayerCount n : ℝ) ≤
        Real.log (Real.log (n : ℝ)) * (2 / 5 : ℝ) := by
    calc
      Real.log 20 * (prsLayerCount n : ℝ) ≤
          4 * (prsLayerCount n : ℝ) :=
        mul_le_mul_of_nonneg_right log_twenty_lt_four.le (by positivity)
      _ ≤ 4 * (Real.log (Real.log (n : ℝ)) / 10) :=
        mul_le_mul_of_nonneg_left hC (by norm_num)
      _ = Real.log (Real.log (n : ℝ)) * (2 / 5 : ℝ) := by ring
  calc
    ((20 ^ (i + 1) : ℕ) : ℝ) = (20 : ℝ) ^ (i + 1) := by norm_num
    _ ≤ (20 : ℝ) ^ prsLayerCount n := hpow
    _ = Real.exp (Real.log 20 * (prsLayerCount n : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    _ ≤ Real.exp (Real.log (Real.log (n : ℝ)) * (2 / 5 : ℝ)) :=
      Real.exp_le_exp.mpr hexponent
    _ = (Real.log (n : ℝ)) ^ (2 / 5 : ℝ) := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hL)]

/-- The exponential loss in any active layer is at most half of `log n`,
once the very slowly growing residual power of `log n` exceeds two. -/
lemma prs_layer_exponent_le {n i : ℕ}
    (hL : 1 ≤ Real.log (n : ℝ))
    (hres : 2 ≤ (Real.log (n : ℝ)) ^ (1 / 10 : ℝ))
    (hi : i < prsLayerCount n) :
    (((20 ^ (i + 1) - 20 : ℕ) : ℝ) * prsY n) ≤
      Real.log (n : ℝ) / 2 := by
  let L : ℝ := Real.log (n : ℝ)
  have hpow := prs_twenty_pow_le hL hi
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hsub : (((20 ^ (i + 1) - 20 : ℕ) : ℝ)) ≤
      ((20 ^ (i + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le (20 ^ (i + 1)) 20
  have hsqrt : prsY n = L ^ (1 / 2 : ℝ) := by
    simp [prsY, L, Real.sqrt_eq_rpow]
  have hpnonneg : 0 ≤ L ^ (2 / 5 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hhalfnonneg : 0 ≤ L ^ (1 / 2 : ℝ) := Real.rpow_nonneg hLpos.le _
  calc
    (((20 ^ (i + 1) - 20 : ℕ) : ℝ) * prsY n)
        ≤ ((20 ^ (i + 1) : ℕ) : ℝ) * prsY n :=
      mul_le_mul_of_nonneg_right hsub (by simp [prsY])
    _ ≤ L ^ (2 / 5 : ℝ) * L ^ (1 / 2 : ℝ) := by
      rw [hsqrt]
      exact mul_le_mul hpow le_rfl hhalfnonneg (by positivity)
    _ = L ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_add hLpos]
      norm_num
    _ ≤ L / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc
        L ^ (9 / 10 : ℝ) * 2
            ≤ L ^ (9 / 10 : ℝ) * L ^ (1 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_left hres (Real.rpow_nonneg hLpos.le _)
        _ = L := by
          rw [← Real.rpow_add hLpos]
          norm_num

/-- A floor of a real number at least two loses at most a factor two. -/
lemma natFloor_bounds_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    0 < ⌊x⌋₊ ∧ x / 2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  have hx0 : 0 ≤ x := by positivity
  have hlo : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
  have hhi : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hpos : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  exact ⟨hpos, by constructor <;> nlinarith⟩

/-- Uniformly over every active layer, the real size is eventually at least
two.  This is the only analytic input needed to control all floors at once. -/
lemma eventually_two_le_prsRealLayerSize :
    ∀ᶠ n : ℕ in atTop, ∀ i < prsLayerCount n, 2 ≤ prsRealLayerSize n i := by
  have hLtop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hresTop : Tendsto
      (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hLtop
  have hexpTop : Tendsto
      (fun n : ℕ ↦ Real.exp (Real.log (n : ℝ) / 2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp <|
      (hLtop.const_mul_atTop (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)).congr'
        (by filter_upwards [] with n; simp [div_eq_mul_inv, mul_comm])
  filter_upwards [hLtop.eventually_ge_atTop 1, hresTop.eventually_ge_atTop 2,
      hexpTop.eventually_ge_atTop 4] with n hL hres hexp i hi
  have hnpos : (0 : ℝ) < n := by
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      norm_num at hL
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hexponent := prs_layer_exponent_le hL hres hi
  have hprod : Real.exp (Real.log (n : ℝ) / 2) =
      (n : ℝ) * Real.exp (-(Real.log (n : ℝ) / 2)) := by
    calc
      Real.exp (Real.log (n : ℝ) / 2) =
          Real.exp (Real.log (n : ℝ) + -(Real.log (n : ℝ) / 2)) := by
        congr 1
        ring
      _ = Real.exp (Real.log (n : ℝ)) *
          Real.exp (-(Real.log (n : ℝ) / 2)) := Real.exp_add _ _
      _ = (n : ℝ) * Real.exp (-(Real.log (n : ℝ) / 2)) := by
        rw [Real.exp_log hnpos]
  calc
    2 ≤ Real.exp (Real.log (n : ℝ) / 2) / 2 := by linarith
    _ = (n : ℝ) / 2 * Real.exp (-(Real.log (n : ℝ) / 2)) := by
      rw [hprod]
      ring
    _ ≤ prsRealLayerSize n i := by
      simp only [prsRealLayerSize]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (neg_le_neg hexponent)

/-- Eventual positivity and the two floor inequalities, simultaneously for
all active layers. -/
lemma eventually_prsLayerSize_bounds :
    ∀ᶠ n : ℕ in atTop, ∀ i < prsLayerCount n,
      0 < prsLayerSize n i ∧
      prsRealLayerSize n i / 2 ≤ (prsLayerSize n i : ℝ) ∧
      (prsLayerSize n i : ℝ) ≤ prsRealLayerSize n i := by
  filter_upwards [eventually_two_le_prsRealLayerSize] with n hn i hi
  simpa only [prsLayerSize] using natFloor_bounds_of_two_le (hn i hi)

private lemma four_mul_exp_neg_two_le_one :
    4 * Real.exp (-2) ≤ (1 : ℝ) := by
  have he : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      (4 : ℝ) ≤ (2.7 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := by
        exact (pow_lt_pow_left₀ (lt_of_lt_of_le (by norm_num) Real.exp_one_gt_d9.le)
          (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)).le
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [Real.exp_neg]
  rw [← div_eq_mul_inv, div_le_one (Real.exp_pos 2)]
  exact he

private lemma eight_thousand_mul_exp_neg_ten_le_one :
    8000 * Real.exp (-10) ≤ (1 : ℝ) := by
  have he : (8000 : ℝ) ≤ Real.exp 10 := by
    calc
      (8000 : ℝ) ≤ (2.7 : ℝ) ^ 10 := by norm_num
      _ ≤ (Real.exp 1) ^ 10 := by
        exact (pow_lt_pow_left₀ (lt_of_lt_of_le (by norm_num) Real.exp_one_gt_d9.le)
          (by norm_num) (by norm_num : (10 : ℕ) ≠ 0)).le
      _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
  rw [Real.exp_neg]
  rw [← div_eq_mul_inv, div_le_one (Real.exp_pos 10)]
  exact he

private lemma prs_coefficient_succ (i : ℕ) :
    20 ^ (i + 2) - 20 = (20 ^ (i + 1) - 20) + 19 * 20 ^ (i + 1) := by
  have hp : 20 ≤ 20 ^ (i + 1) := by
    simpa [pow_succ] using
      (Nat.mul_le_mul_left 20 (Nat.one_le_pow i 20 (by norm_num)))
  rw [show i + 2 = (i + 1) + 1 by omega, pow_succ]
  omega

/-- Consecutive unrounded layers decay by at least a factor four as soon
as `sqrt (log n) ≥ 1`. -/
lemma four_mul_prsRealLayerSize_succ_le {n i : ℕ} (hy : 1 ≤ prsY n) :
    4 * prsRealLayerSize n (i + 1) ≤ prsRealLayerSize n i := by
  let d : ℝ := ((20 ^ (i + 1) - 20 : ℕ) : ℝ)
  let d' : ℝ := ((20 ^ (i + 2) - 20 : ℕ) : ℝ)
  have hd : d + 380 ≤ d' := by
    have hpow : 20 ≤ 20 ^ (i + 1) := by
      simpa [pow_succ] using
        (Nat.mul_le_mul_left 20 (Nat.one_le_pow i 20 (by norm_num)))
    have hnat : (20 ^ (i + 1) - 20) + 380 ≤ 20 ^ (i + 2) - 20 := by
      rw [prs_coefficient_succ]
      omega
    change (((20 ^ (i + 1) - 20 : ℕ) : ℝ) + 380 ≤
      ((20 ^ (i + 2) - 20 : ℕ) : ℝ))
    exact_mod_cast hnat
  have hgap : d * prsY n + 2 ≤ d' * prsY n := by
    have hy0 : 0 ≤ prsY n := by positivity
    have := mul_le_mul_of_nonneg_right hd hy0
    nlinarith
  have hexp : 4 * Real.exp (-(d' * prsY n)) ≤ Real.exp (-(d * prsY n)) := by
    calc
      4 * Real.exp (-(d' * prsY n))
          ≤ 4 * Real.exp (-(d * prsY n) - 2) := by
        gcongr
        linarith
      _ = Real.exp (-(d * prsY n)) * (4 * Real.exp (-2)) := by
        rw [Real.exp_sub]
        have hneg : (Real.exp 2)⁻¹ = Real.exp (-2) := (Real.exp_neg 2).symm
        rw [div_eq_mul_inv, hneg]
        ring
      _ ≤ Real.exp (-(d * prsY n)) * 1 :=
        mul_le_mul_of_nonneg_left four_mul_exp_neg_two_le_one (Real.exp_pos _).le
      _ = Real.exp (-(d * prsY n)) := by ring
  simp only [prsRealLayerSize]
  change 4 * ((n : ℝ) / 2 * Real.exp (-(d' * prsY n))) ≤
    (n : ℝ) / 2 * Real.exp (-(d * prsY n))
  have hm := mul_le_mul_of_nonneg_left hexp
    (show (0 : ℝ) ≤ (n : ℝ) / 2 by positivity)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hm

/-- The actual separation of consecutive PRS layers is far stronger than
dyadic; this form supplies the base-at-most-one condition in the binomial
union bound. -/
lemma eight_thousand_mul_prsRealLayerSize_succ_le {n i : ℕ}
    (hy : 1 ≤ prsY n) :
    8000 * prsRealLayerSize n (i + 1) ≤ prsRealLayerSize n i := by
  let d : ℝ := ((20 ^ (i + 1) - 20 : ℕ) : ℝ)
  let d' : ℝ := ((20 ^ (i + 2) - 20 : ℕ) : ℝ)
  have hd : d + 380 ≤ d' := by
    have hpow : 20 ≤ 20 ^ (i + 1) := by
      simpa [pow_succ] using
        (Nat.mul_le_mul_left 20 (Nat.one_le_pow i 20 (by norm_num)))
    have hnat : (20 ^ (i + 1) - 20) + 380 ≤ 20 ^ (i + 2) - 20 := by
      rw [prs_coefficient_succ]
      omega
    change (((20 ^ (i + 1) - 20 : ℕ) : ℝ) + 380 ≤
      ((20 ^ (i + 2) - 20 : ℕ) : ℝ))
    exact_mod_cast hnat
  have hgap : d * prsY n + 10 ≤ d' * prsY n := by
    have hy0 : 0 ≤ prsY n := by positivity
    have := mul_le_mul_of_nonneg_right hd hy0
    nlinarith
  have hexp : 8000 * Real.exp (-(d' * prsY n)) ≤
      Real.exp (-(d * prsY n)) := by
    calc
      8000 * Real.exp (-(d' * prsY n))
          ≤ 8000 * Real.exp (-(d * prsY n) - 10) := by
        gcongr
        linarith
      _ = Real.exp (-(d * prsY n)) * (8000 * Real.exp (-10)) := by
        rw [Real.exp_sub]
        have hneg : (Real.exp 10)⁻¹ = Real.exp (-10) := (Real.exp_neg 10).symm
        rw [div_eq_mul_inv, hneg]
        ring
      _ ≤ Real.exp (-(d * prsY n)) * 1 :=
        mul_le_mul_of_nonneg_left eight_thousand_mul_exp_neg_ten_le_one
          (Real.exp_pos _).le
      _ = Real.exp (-(d * prsY n)) := by ring
  simp only [prsRealLayerSize]
  change 8000 * ((n : ℝ) / 2 * Real.exp (-(d' * prsY n))) ≤
    (n : ℝ) / 2 * Real.exp (-(d * prsY n))
  have hm := mul_le_mul_of_nonneg_left hexp
    (show (0 : ℝ) ≤ (n : ℝ) / 2 by positivity)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hm

/-- The rounded layer sizes satisfy the convenient dyadic decay used by
the tail estimates. -/
lemma eventually_two_mul_prsLayerSize_succ_le :
    ∀ᶠ n : ℕ in atTop, ∀ i, i + 1 < prsLayerCount n →
      2 * prsLayerSize n (i + 1) ≤ prsLayerSize n i := by
  filter_upwards [eventually_prsLayerSize_bounds,
      tendsto_prsY_atTop.eventually_ge_atTop 1] with n hb hy i hi
  have hi' : i < prsLayerCount n := lt_trans (Nat.lt_succ_self i) hi
  have hdecay := four_mul_prsRealLayerSize_succ_le (n := n) (i := i) hy
  have hcast : (2 * prsLayerSize n (i + 1) : ℝ) ≤ prsLayerSize n i := by
    calc
      (2 * prsLayerSize n (i + 1) : ℝ)
          ≤ 2 * prsRealLayerSize n (i + 1) := by
        exact mul_le_mul_of_nonneg_left (hb (i + 1) hi).2.2 (by norm_num)
      _ ≤ prsRealLayerSize n i / 2 := by linarith
      _ ≤ (prsLayerSize n i : ℝ) := (hb i hi').2.1
  exact_mod_cast hcast

/-- Rounded consecutive layers retain a factor `4000` of separation. -/
lemma eventually_four_thousand_mul_prsLayerSize_succ_le :
    ∀ᶠ n : ℕ in atTop, ∀ i, i + 1 < prsLayerCount n →
      4000 * prsLayerSize n (i + 1) ≤ prsLayerSize n i := by
  filter_upwards [eventually_prsLayerSize_bounds,
      tendsto_prsY_atTop.eventually_ge_atTop 1] with n hb hy i hi
  have hi' : i < prsLayerCount n := lt_trans (Nat.lt_succ_self i) hi
  have hdecay := eight_thousand_mul_prsRealLayerSize_succ_le
    (n := n) (i := i) hy
  have hcast : (4000 * prsLayerSize n (i + 1) : ℝ) ≤ prsLayerSize n i := by
    calc
      (4000 * prsLayerSize n (i + 1) : ℝ)
          ≤ 4000 * prsRealLayerSize n (i + 1) := by
        exact mul_le_mul_of_nonneg_left (hb (i + 1) hi).2.2 (by norm_num)
      _ ≤ prsRealLayerSize n i / 2 := by nlinarith
      _ ≤ (prsLayerSize n i : ℝ) := (hb i hi').2.1
  exact_mod_cast hcast

/-- A finite dyadically decreasing sequence has total mass at most twice
its first term. -/
lemma sum_range_le_two_mul_of_two_mul_succ_le (b : ℕ → ℕ) (m : ℕ)
    (hstep : ∀ j, j + 1 < m → 2 * b (j + 1) ≤ b j) :
    ∑ j ∈ Finset.range m, b j ≤ 2 * b 0 := by
  induction m generalizing b with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ']
      by_cases hm : m = 0
      · subst m
        simp
        omega
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have htail : ∑ j ∈ Finset.range m, b (j + 1) ≤ 2 * b 1 := by
          apply ih (fun j ↦ b (j + 1))
          intro j hj
          simpa only [Nat.add_assoc, Nat.one_add] using
            hstep (j + 1) (by omega)
        have hfirst : 2 * b 1 ≤ b 0 := by
          simpa using hstep 0 (by omega)
        omega

/-- Every tail of the active rounded layers is at most twice its first
term.  The sum is empty when `i + 1 ≥ prsLayerCount n`. -/
lemma eventually_prsLayer_tail_le :
    ∀ᶠ n : ℕ in atTop, ∀ i,
      ∑ j ∈ Finset.Ico (i + 1) (prsLayerCount n), prsLayerSize n j ≤
        2 * prsLayerSize n (i + 1) := by
  filter_upwards [eventually_two_mul_prsLayerSize_succ_le] with n hstep i
  by_cases hi : i + 1 < prsLayerCount n
  · rw [Finset.sum_Ico_eq_sum_range]
    let m := prsLayerCount n - (i + 1)
    have hgeom := sum_range_le_two_mul_of_two_mul_succ_le
      (fun j ↦ prsLayerSize n (i + 1 + j)) m (by
        intro j hj
        apply hstep (i + 1 + j)
        omega)
    simpa [m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hgeom
  · have : Finset.Ico (i + 1) (prsLayerCount n) = ∅ := by
      exact Finset.Ico_eq_empty hi
    simp [this]

/-- The active layers occupy at most `n` vertices; the remaining vertices
can therefore be padded by isolates. -/
lemma eventually_prsLayer_sum_le :
    ∀ᶠ n : ℕ in atTop,
      ∑ i ∈ Finset.range (prsLayerCount n), prsLayerSize n i ≤ n := by
  filter_upwards [eventually_prsLayer_tail_le, eventually_prsLayerSize_bounds,
      eventually_two_le_prsLayerCount,
      tendsto_prsY_atTop.eventually_ge_atTop 1] with n htail hb hC hy
  have h0 : 0 < prsLayerCount n := by omega
  have h1 : 1 < prsLayerCount n := by omega
  have hsplit :
      ∑ i ∈ Finset.range (prsLayerCount n), prsLayerSize n i =
        prsLayerSize n 0 +
          ∑ i ∈ Finset.Ico 1 (prsLayerCount n), prsLayerSize n i := by
    rw [← Finset.sum_range_add_sum_Ico (f := fun i ↦ prsLayerSize n i)
      (show 1 ≤ prsLayerCount n by omega)]
    simp
  have hdecay := four_mul_prsRealLayerSize_succ_le (n := n) (i := 0) hy
  have hreal0 : prsRealLayerSize n 0 = (n : ℝ) / 2 := prsRealLayerSize_zero n
  have hcast :
      ((prsLayerSize n 0 + 2 * prsLayerSize n 1 : ℕ) : ℝ) ≤ n := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hb0 := (hb 0 h0).2.2
    have hb1 := (hb 1 h1).2.2
    rw [hreal0] at hb0 hdecay
    nlinarith
  have hnat : prsLayerSize n 0 + 2 * prsLayerSize n 1 ≤ n := by
    exact_mod_cast hcast
  rw [hsplit]
  exact Nat.add_le_add_left (htail 0) _ |>.trans hnat

/-- The first layer times the number of later layers gives the required
`n log log n` edge count, with the explicit slack constant `1/60`. -/
lemma eventually_prs_edge_count_lower :
    ∀ᶠ n : ℕ in atTop,
      (1 / 60 : ℝ) * (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        (prsLayerSize n 0 * (prsLayerCount n - 1) : ℕ) := by
  have hLLtop : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hLLtop.eventually_ge_atTop 60,
      eventually_prsLayerSize_bounds, eventually_two_le_prsLayerCount]
      with n hLL hb hC
  let T : ℝ := Real.log (Real.log (n : ℝ))
  have hzero : 0 < prsLayerCount n := by omega
  have hb0 : (n : ℝ) / 4 ≤ prsLayerSize n 0 := by
    have := (hb 0 hzero).2.1
    convert this using 1 <;> simp [prsRealLayerSize_zero] <;> ring
  have hfloor : T / 10 - 1 < (prsLayerCount n : ℝ) := by
    simpa only [prsLayerCount, T] using
      (Nat.sub_one_lt_floor (Real.log (Real.log (n : ℝ)) / 10))
  have hcount : T / 15 ≤ ((prsLayerCount n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    norm_num only [Nat.cast_one]
    nlinarith
  have hmul := mul_le_mul hb0 hcount
    (show (0 : ℝ) ≤ T / 15 by positivity)
    (show (0 : ℝ) ≤ (prsLayerSize n 0 : ℝ) by positivity)
  norm_num only [Nat.cast_mul]
  change (1 / 60 : ℝ) * (n : ℝ) * T ≤
    (prsLayerSize n 0 : ℝ) * ((prsLayerCount n - 1 : ℕ) : ℝ)
  calc
    (1 / 60 : ℝ) * (n : ℝ) * T =
        ((n : ℝ) / 4) * (T / 15) := by ring
    _ ≤ (prsLayerSize n 0 : ℝ) * ((prsLayerCount n - 1 : ℕ) : ℝ) := hmul

/-- A convenient comparison between the layer count and the square-root
logarithmic scale. -/
lemma prsLayerCount_le_prsY {n : ℕ} (hL : 1 ≤ Real.log (n : ℝ)) :
    (prsLayerCount n : ℝ) ≤ prsY n := by
  let L : ℝ := Real.log (n : ℝ)
  let y : ℝ := Real.sqrt L
  have hL0 : 0 ≤ L := hL.trans' zero_le_one
  have hy : 1 ≤ y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_le_sqrt hL
  have hypos : 0 < y := zero_lt_one.trans_le hy
  have hsq : y * y = L := by
    simpa [y, pow_two] using Real.sq_sqrt hL0
  have hlogeq : Real.log L = 2 * Real.log y := by
    rw [← hsq, Real.log_mul hypos.ne' hypos.ne']
    ring
  have hlogy : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hypos
  have hC : (prsLayerCount n : ℝ) ≤ Real.log L / 10 := by
    exact_mod_cast Nat.floor_le
      (div_nonneg (Real.log_nonneg hL) (by norm_num : (0 : ℝ) ≤ 10))
  rw [show prsY n = y by rfl]
  rw [hlogeq] at hC
  nlinarith

/-- The geometric union-bound error is eventually strictly below one. -/
lemma eventually_prs_error_lt_one :
    ∀ᶠ n : ℕ in atTop,
      2 * (prsLayerCount n : ℝ) * Real.exp (-(prsY n / 2)) < 1 := by
  have hdecay : Tendsto
      (fun x : ℝ ↦ 2 * (x ^ (1 : ℝ) * Real.exp (-(1 / 2 : ℝ) * x)))
      atTop (nhds 0) :=
    by
      have htwo : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
      simpa using htwo.mul
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2) (by norm_num))
  have hcomp : Tendsto
      (fun n : ℕ ↦ 2 * prsY n * Real.exp (-(prsY n / 2))) atTop (nhds 0) := by
    convert hdecay.comp tendsto_prsY_atTop using 1 <;>
      ext n <;> simp [div_eq_mul_inv] <;> ring_nf
  have hevent : ∀ᶠ n : ℕ in atTop,
      2 * prsY n * Real.exp (-(prsY n / 2)) < 1 :=
    hcomp.eventually (Iio_mem_nhds zero_lt_one)
  have hLtop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hevent, hLtop.eventually_ge_atTop 1] with n hsmall hL
  have hC := prsLayerCount_le_prsY hL
  have hnonneg : 0 ≤ Real.exp (-(prsY n / 2)) := (Real.exp_pos _).le
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 2)) hnonneg)
    hsmall

private lemma prs_log_coefficient_le {i : ℕ} (hi : 1 ≤ i) :
    -(1 / 10 : ℝ) * ((20 ^ (i + 1) - 20 : ℕ) : ℝ) +
        (11 / 10 : ℝ) * ((20 ^ i - 20 : ℕ) : ℝ) ≤ -38 := by
  have hp : 20 ≤ 20 ^ i := by
    calc
      20 = 20 ^ 1 := by norm_num
      _ ≤ 20 ^ i := pow_le_pow_right₀ (by norm_num) hi
  have hp' : 20 ≤ 20 ^ (i + 1) := hp.trans
    (pow_le_pow_right₀ (by norm_num) (Nat.le_succ i))
  rw [Nat.cast_sub hp', Nat.cast_sub hp]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  have hpr : (20 : ℝ) ≤ (20 : ℝ) ^ i := by exact_mod_cast hp
  norm_num [div_eq_mul_inv]
  nlinarith

/-- The bracket in the PRS bad-event estimate decays exponentially in
`sqrt (log n)`, uniformly over all noninitial active layers. -/
lemma eventually_prs_badEvent_bracket_le :
    ∀ᶠ n : ℕ in atTop, ∀ i, 1 ≤ i → i < prsLayerCount n →
      20 * (n : ℝ) * (prsLayerSize n i : ℝ) ^ (1 / 10 : ℝ) /
          (prsLayerSize n (i - 1) : ℝ) ^ (11 / 10 : ℝ) ≤
        Real.exp (-(prsY n / 2)) := by
  have hLtop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_prsLayerSize_bounds,
      tendsto_prsY_atTop.eventually_ge_atTop 1,
      hLtop.eventually_ge_atTop 1] with n hb hy hL i hi hiC
  have hn : 0 < n := by
    by_contra hn
    have : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num at hL
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have him1 : i - 1 < prsLayerCount n := lt_of_le_of_lt (Nat.sub_le i 1) hiC
  have hbi : 0 < prsLayerSize n i := (hb i hiC).1
  have hbim1 : 0 < prsLayerSize n (i - 1) := (hb (i - 1) him1).1
  have hbiR : (0 : ℝ) < prsLayerSize n i := by exact_mod_cast hbi
  have hbim1R : (0 : ℝ) < prsLayerSize n (i - 1) := by exact_mod_cast hbim1
  have hai : 0 < prsRealLayerSize n i := by
    simp [prsRealLayerSize]
    positivity
  have haim1 : 0 < prsRealLayerSize n (i - 1) := by
    simp [prsRealLayerSize]
    positivity
  have hlogbi : Real.log (prsLayerSize n i : ℝ) ≤
      Real.log (prsRealLayerSize n i) :=
    Real.log_le_log (by exact_mod_cast hbi) (hb i hiC).2.2
  have hlogbim1 : Real.log (prsRealLayerSize n (i - 1) / 2) ≤
      Real.log (prsLayerSize n (i - 1) : ℝ) :=
    Real.log_le_log (by positivity) (hb (i - 1) him1).2.1
  have hlogai := log_prsRealLayerSize (i := i) hn
  have hlogaim1 : Real.log (prsRealLayerSize n (i - 1) / 2) =
      Real.log (n : ℝ) - 2 * Real.log 2 -
        ((20 ^ i - 20 : ℕ) : ℝ) * prsY n := by
    rw [Real.log_div haim1.ne' (by norm_num), log_prsRealLayerSize hn]
    rw [show i - 1 + 1 = i by omega]
    ring
  have hcoeff := prs_log_coefficient_le hi
  have hcoeffY := mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ prsY n)
  have hlog20 : Real.log 20 ≤ 4 := log_twenty_lt_four.le
  have hlog2 : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  let Q : ℝ := 20 * (n : ℝ) * (prsLayerSize n i : ℝ) ^ (1 / 10 : ℝ) /
    (prsLayerSize n (i - 1) : ℝ) ^ (11 / 10 : ℝ)
  have hQ : 0 < Q := by
    dsimp [Q]
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hnr) (Real.rpow_pos_of_pos hbiR _))
      (Real.rpow_pos_of_pos hbim1R _)
  rw [← Real.log_le_iff_le_exp hQ]
  have hlogQ : Real.log Q =
      Real.log 20 + Real.log (n : ℝ) +
        (1 / 10 : ℝ) * Real.log (prsLayerSize n i : ℝ) -
        (11 / 10 : ℝ) * Real.log (prsLayerSize n (i - 1) : ℝ) := by
    dsimp [Q]
    rw [Real.log_div
        (mul_ne_zero (mul_ne_zero (by norm_num) hnr.ne')
          (Real.rpow_pos_of_pos hbiR _).ne')
        (Real.rpow_pos_of_pos hbim1R _).ne',
      Real.log_mul (mul_ne_zero (by norm_num) hnr.ne')
        (Real.rpow_pos_of_pos hbiR _).ne',
      Real.log_mul (by norm_num) hnr.ne',
      Real.log_rpow hbiR, Real.log_rpow hbim1R]
  rw [hlogQ]
  rw [hlogai] at hlogbi
  rw [hlogaim1] at hlogbim1
  nlinarith

/-- Complete numerical estimate for one PRS bad event.  This is the form
used after the union bound over the vertex set and its demanded edges. -/
lemma eventually_prs_badEvent_choose_bound :
    ∀ᶠ n : ℕ in atTop, ∀ i, 1 ≤ i → i < prsLayerCount n →
      ∀ x, 1 ≤ x → x ≤ 1000 * prsLayerSize n i →
        (n.choose x : ℝ) *
            ((x.choose 2).choose (prsBadEdgeCount x) : ℝ) /
              (prsLayerSize n (i - 1) : ℝ) ^ prsBadEdgeCount x ≤
          Real.exp (-(x : ℝ) * prsY n / 2) := by
  filter_upwards [eventually_prsLayerSize_bounds,
      eventually_four_thousand_mul_prsLayerSize_succ_le,
      eventually_prs_badEvent_bracket_le] with n hb hsep hbracket i hi hiC x hx hxb
  have hxpos : 0 < x := by omega
  have him1 : i - 1 < prsLayerCount n := lt_of_le_of_lt (Nat.sub_le i 1) hiC
  have him1succ : (i - 1) + 1 = i := by omega
  have hbi : 0 < prsLayerSize n i := (hb i hiC).1
  have hB : 0 < prsLayerSize n (i - 1) := (hb (i - 1) him1).1
  have hsep' : 4000 * prsLayerSize n i ≤ prsLayerSize n (i - 1) := by
    simpa only [him1succ] using hsep (i - 1) (by omega)
  have hbase :
      3 * (x : ℝ) / (2 * (prsLayerSize n (i - 1) : ℝ)) ≤ 1 := by
    have hxR : (x : ℝ) ≤ 1000 * prsLayerSize n i := by exact_mod_cast hxb
    have hsepR : (4000 : ℝ) * prsLayerSize n i ≤
        prsLayerSize n (i - 1) := by exact_mod_cast hsep'
    rw [div_le_one (by positivity : (0 : ℝ) <
      2 * (prsLayerSize n (i - 1) : ℝ))]
    nlinarith
  have hE : 3 * (n : ℝ) / (x : ℝ) *
      (3 * (x : ℝ) / (2 * (prsLayerSize n (i - 1) : ℝ))) ^
          (11 / 10 : ℝ) ≤ Real.exp (-(prsY n / 2)) :=
    (prs_choose_base_le_badEvent_bracket hxpos hbi hB hxb).trans
      (hbracket i hi hiC)
  have hcore := prs_choose_bridge_core n x (prsLayerSize n (i - 1))
    (prsBadEdgeCount x) (Real.exp (-(prsY n / 2))) hxpos hB
    (eleven_mul_le_ten_mul_prsBadEdgeCount x) hbase hE
  calc
    (n.choose x : ℝ) *
          ((x.choose 2).choose (prsBadEdgeCount x) : ℝ) /
            (prsLayerSize n (i - 1) : ℝ) ^ prsBadEdgeCount x
        ≤ Real.exp (-(prsY n / 2)) ^ x := hcore
    _ = Real.exp (-(x : ℝ) * prsY n / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

end Erdos182
