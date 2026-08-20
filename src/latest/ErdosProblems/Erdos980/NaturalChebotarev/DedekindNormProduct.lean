/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import CebotarevDensity.NumberFieldEulerProduct
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The de la Vallée Poussin norm product for Dedekind zeta functions

This file proves the `3-4-1` norm-product inequality for a Dedekind zeta function directly
from the AINTLIB prime-ideal Euler product.  It is the number-field analogue of
`DirichletCharacter.norm_LSeries_product_ge_one`.
-/

namespace Erdos980.NaturalChebotarev

open Complex NumberField

noncomputable section

private abbrev PrimeIdeal (K : Type*) [Field K] [NumberField K] :=
  { 𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ }

private lemma two_le_absNorm_of_primeIdeal
    (K : Type*) [Field K] [NumberField K] (𝔭 : PrimeIdeal K) :
    2 ≤ Ideal.absNorm 𝔭.1 := by
  have h₀ : Ideal.absNorm 𝔭.1 ≠ 0 :=
    fun h ↦ 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have h₁ : Ideal.absNorm 𝔭.1 ≠ 1 :=
    fun h ↦ 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

private lemma re_log_comb_nonneg' {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ}
    (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re
      + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

private lemma re_log_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 1 < x)
    (y : ℝ) :
    0 ≤ 3 * (-log (1 - (n : ℂ) ^ (-(x : ℂ)))).re
      + 4 * (-log (1 - (n : ℂ) ^ (-(x + I * y)))).re
      + (-log (1 - (n : ℂ) ^ (-(x + 2 * I * y)))).re := by
  have ha₁ : (n : ℝ) ^ (-x) < 1 := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), inv_lt_one_iff₀]
    exact .inr <| Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) <| zero_lt_one.trans hx
  have hz : ‖(n : ℂ) ^ (-(I * y))‖ = 1 := by
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (mod_cast by omega)]
    simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
      sub_self, neg_zero, Real.rpow_zero]
  convert! re_log_comb_nonneg' (by positivity) ha₁ hz using 6
  · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
  · congr 2
    rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast]
  · rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast,
      show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul]

private lemma one_lt_re_one_add {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 < (1 + x : ℂ).re ∧ 1 < (1 + x + I * y).re ∧
      1 < (1 + x + 2 * I * y).re := by
  simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx, mul_re, I_re, zero_mul,
    I_im, ofReal_im, mul_zero, sub_self, add_zero, re_ofNat, im_ofNat, mul_one, mul_im,
    and_self]

/-- The logarithms of the prime-ideal Euler factors are summable on `Re s > 1`. -/
private lemma summable_neg_log_one_sub_primeIdeal_cpow
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    Summable fun 𝔭 : PrimeIdeal K ↦
      -log (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) := by
  have hsumIdeal : Summable fun 𝔞 : Chebotarev.NonzeroIdeal K ↦
      ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)‖ :=
    (Chebotarev.hasSum_nonzeroIdeal_absNorm_cpow K hs).summable.norm
  have hsumPrime : Summable fun 𝔭 : PrimeIdeal K ↦
      ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ := by
    exact hsumIdeal.comp_injective
      (i := fun 𝔭 : PrimeIdeal K ↦ (⟨𝔭.1, 𝔭.2.2⟩ : Chebotarev.NonzeroIdeal K))
      (fun 𝔭 𝔮 h ↦ Subtype.ext (by simpa using h))
  exact (Summable.of_norm hsumPrime).clog_one_sub.neg

/-- The prime-ideal logarithmic Euler product for the Dedekind zeta function. -/
private lemma dedekindZeta_eq_exp_tsum
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s =
      exp (∑' 𝔭 : PrimeIdeal K,
        -log (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))) := by
  have hsum := summable_neg_log_one_sub_primeIdeal_cpow K hs
  have hne : ∀ 𝔭 : PrimeIdeal K,
      (1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s) ≠ 0 := by
    intro 𝔭
    apply sub_ne_zero.mpr
    intro h
    have hlt := Chebotarev.norm_absNorm_cpow_neg_lt_one K hs 𝔭
    rw [← h, norm_one] at hlt
    exact (lt_irrefl 1 hlt)
  have H := hsum.hasSum.cexp.tprod_eq
  simp only [Function.comp_apply, exp_neg, exp_log (hne _)] at H
  rw [Chebotarev.dedekindZeta_eq_tprod_primeIdeal K hs]
  exact H

/-- The de la Vallée Poussin `3-4-1` norm-product inequality for a Dedekind zeta function. -/
theorem norm_dedekindZeta_product_ge_one
    (K : Type*) [Field K] [NumberField K] {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖dedekindZeta K (1 + x) ^ 3 * dedekindZeta K (1 + x + I * y) ^ 4
      * dedekindZeta K (1 + x + 2 * I * y)‖ ≥ 1 := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  have H₀ := summable_neg_log_one_sub_primeIdeal_cpow K h₀
  have H₁ := summable_neg_log_one_sub_primeIdeal_cpow K h₁
  have H₂ := summable_neg_log_one_sub_primeIdeal_cpow K h₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [dedekindZeta_eq_exp_tsum K h₀, dedekindZeta_eq_exp_tsum K h₁,
    dedekindZeta_eq_exp_tsum K h₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← hsum₀.tsum_add hsum₁, ← (hsum₀.add hsum₁).tsum_add hsum₂]
  simpa only [neg_add_rev, neg_re, mul_neg, ge_iff_le, add_re, one_re, ofReal_re,
    ofReal_add, ofReal_one] using
      tsum_nonneg fun 𝔭 : PrimeIdeal K ↦
        re_log_comb_nonneg (two_le_absNorm_of_primeIdeal K 𝔭) h₀ y

end

end Erdos980.NaturalChebotarev
