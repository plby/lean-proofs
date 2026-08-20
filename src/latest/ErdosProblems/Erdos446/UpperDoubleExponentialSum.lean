/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperFiniteLayerSum

/-!
# Erdős Problem 446: Ford's double-exponential layer sum

This file isolates the numerical estimate labelled (33a) in the accompanying
write-up.  After putting `j = b - m - 1`, its first (finite) sum is

`sum_{5 <= j < b} b / (2^(b-j-1) * 2^(2^j))`.

For `b >= 6`, putting `w = m - (b-5)` changes the second sum into

`sum_{w >= 0} (w+1)^2 (b+w-3) / 2^(b-5+w)`.

When `b <= 5` there is no first sum, and the second sum starts at `m=0`.
All sums below have an arbitrary finite cutoff.  Thus the theorem is a
fully finite, uniform version of Ford's `O((1+b^2)/(2^b+1))` estimate; no
infinite-series convergence statement is hidden in the argument.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The double-exponential head in (33a), reindexed by `j = b-m-1`. -/
noncomputable def ford33aDoubleExponentialHead (b : ℕ) : ℝ :=
  ∑ j ∈ (Finset.range b).filter (5 ≤ ·),
    (b : ℝ) /
      ((2 : ℝ) ^ (b - j - 1) * (2 : ℝ) ^ (2 ^ j))

/-- The finite-cutoff polynomially weighted tail in (33a).  The two
branches are precisely the two cases in Ford's calculation. -/
noncomputable def ford33aPolynomialTail (b R : ℕ) : ℝ :=
  if 6 ≤ b then
    ∑ w ∈ Finset.range R,
      ((w + 1 : ℕ) : ℝ) ^ 2 * ((b + w - 3 : ℕ) : ℝ) /
        (2 : ℝ) ^ (b - 5 + w)
  else
    ∑ m ∈ Finset.range R,
      ((m + 6 - b : ℕ) : ℝ) ^ 2 * ((m + 2 : ℕ) : ℝ) /
        (2 : ℝ) ^ m

/-- A finite version of the complete numerical expression (33a), with the
irrelevant common factorial factor removed. -/
noncomputable def ford33aNumericalSum (b R : ℕ) : ℝ :=
  ford33aDoubleExponentialHead b + ford33aPolynomialTail b R

private theorem succ_le_two_pow (j : ℕ) : j + 1 ≤ 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      calc
        j + 1 + 1 ≤ 2 * (j + 1) := by omega
        _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (j + 1) := by rw [pow_succ]; ring

private theorem head_denominator_ge
    {b j : ℕ} (hj : j < b) :
    (2 : ℝ) ^ b ≤
      (2 : ℝ) ^ (b - j - 1) * (2 : ℝ) ^ (2 ^ j) := by
  have hexp : b ≤ b - j - 1 + 2 ^ j := by
    have hsplit : b = (b - j - 1) + (j + 1) := by omega
    calc
      b = (b - j - 1) + (j + 1) := hsplit
      _ ≤ (b - j - 1) + 2 ^ j :=
        Nat.add_le_add_left (succ_le_two_pow j) _
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num) hexp

private theorem ford33aDoubleExponentialHead_le_raw (b : ℕ) :
    ford33aDoubleExponentialHead b ≤
      (b : ℝ) ^ 2 / (2 : ℝ) ^ b := by
  let I := (Finset.range b).filter (5 ≤ ·)
  have hterm : ∀ j ∈ I,
      (b : ℝ) /
          ((2 : ℝ) ^ (b - j - 1) * (2 : ℝ) ^ (2 ^ j)) ≤
        (b : ℝ) / (2 : ℝ) ^ b := by
    intro j hj
    have hjb : j < b := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (head_denominator_ge hjb)
  have hcard : I.card ≤ b := by
    dsimp [I]
    simpa using Finset.card_filter_le (Finset.range b) (5 ≤ ·)
  calc
    ford33aDoubleExponentialHead b =
        ∑ j ∈ I,
          (b : ℝ) /
            ((2 : ℝ) ^ (b - j - 1) * (2 : ℝ) ^ (2 ^ j)) := by
      rfl
    _ ≤ I.card • ((b : ℝ) / (2 : ℝ) ^ b) :=
      Finset.sum_le_card_nsmul I _ _ hterm
    _ = (I.card : ℝ) * ((b : ℝ) / (2 : ℝ) ^ b) := by
      rw [nsmul_eq_mul]
    _ ≤ (b : ℝ) * ((b : ℝ) / (2 : ℝ) ^ b) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = (b : ℝ) ^ 2 / (2 : ℝ) ^ b := by ring

private theorem quadratic_model_conversion (b : ℕ) :
    (1 + (b : ℝ) ^ 2) / (2 : ℝ) ^ b ≤
      2 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have hden : (0 : ℝ) < (2 : ℝ) ^ b + 1 := by positivity
  have hratio : (2 : ℝ) ^ b + 1 ≤ 2 * (2 : ℝ) ^ b := by
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
    linarith
  apply (div_le_div_iff₀ hpow hden).2
  calc
    (1 + (b : ℝ) ^ 2) * ((2 : ℝ) ^ b + 1) ≤
        (1 + (b : ℝ) ^ 2) * (2 * (2 : ℝ) ^ b) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (2 * (1 + (b : ℝ) ^ 2)) * (2 : ℝ) ^ b := by ring

theorem ford33aDoubleExponentialHead_le (b : ℕ) :
    ford33aDoubleExponentialHead b ≤
      2 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) := by
  calc
    ford33aDoubleExponentialHead b ≤
        (b : ℝ) ^ 2 / (2 : ℝ) ^ b :=
      ford33aDoubleExponentialHead_le_raw b
    _ ≤ (1 + (b : ℝ) ^ 2) / (2 : ℝ) ^ b := by
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ 2 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) :=
      quadratic_model_conversion b

private theorem large_tail_polynomial_le (b w : ℕ) :
    ((w + 1 : ℕ) : ℝ) ^ 2 * ((b + w - 3 : ℕ) : ℝ) ≤
      ((b + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 3 := by
  have hnat : b + w - 3 ≤ (b + 1) * (w + 1) := by
    calc
      b + w - 3 ≤ b + w + 1 := by omega
      _ ≤ (b + 1) * (w + 1) := by
        nlinarith [Nat.zero_le (b * w)]
  have hcast : ((b + w - 3 : ℕ) : ℝ) ≤
      (((b + 1) * (w + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    ((w + 1 : ℕ) : ℝ) ^ 2 * ((b + w - 3 : ℕ) : ℝ) ≤
        ((w + 1 : ℕ) : ℝ) ^ 2 *
          (((b + 1) * (w + 1) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hcast (by positivity)
    _ = ((b + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 3 := by
      push_cast
      ring

private theorem large_tail_polynomial_sum_le (b R : ℕ) :
    (∑ w ∈ Finset.range R,
        ((w + 1 : ℕ) : ℝ) ^ 2 * ((b + w - 3 : ℕ) : ℝ) /
          (2 : ℝ) ^ w) ≤
      ((b + 1 : ℕ) : ℝ) * cubicGeometricPartial R := by
  rw [cubicGeometricPartial, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  simpa only [mul_div_assoc] using
    div_le_div_of_nonneg_right (large_tail_polynomial_le b w)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) w)

private theorem add_one_le_quadratic (b : ℕ) :
    ((b + 1 : ℕ) : ℝ) ≤ 1 + (b : ℝ) ^ 2 := by
  have hnat : b + 1 ≤ 1 + b ^ 2 := by
    cases b with
    | zero => simp
    | succ b => nlinarith
  exact_mod_cast hnat

private theorem ford33aLargePolynomialTail_le
    {b : ℕ} (hb : 6 ≤ b) (R : ℕ) :
    (∑ w ∈ Finset.range R,
        ((w + 1 : ℕ) : ℝ) ^ 2 * ((b + w - 3 : ℕ) : ℝ) /
          (2 : ℝ) ^ (b - 5 + w)) ≤
      3328 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (b - 5) := by positivity
  have hpoly := large_tail_polynomial_sum_le b R
  have hcubic := cubicGeometricPartial_le R
  calc
    (∑ w ∈ Finset.range R,
        ((w + 1 : ℕ) : ℝ) ^ 2 * ((b + w - 3 : ℕ) : ℝ) /
          (2 : ℝ) ^ (b - 5 + w)) =
        (1 / (2 : ℝ) ^ (b - 5)) *
          (∑ w ∈ Finset.range R,
            ((w + 1 : ℕ) : ℝ) ^ 2 * ((b + w - 3 : ℕ) : ℝ) /
              (2 : ℝ) ^ w) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [pow_add]
      field_simp
    _ ≤ (1 / (2 : ℝ) ^ (b - 5)) *
          (((b + 1 : ℕ) : ℝ) * cubicGeometricPartial R) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ ≤ (1 / (2 : ℝ) ^ (b - 5)) *
          (((b + 1 : ℕ) : ℝ) * 52) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcubic (by positivity)
    _ = 1664 * (((b + 1 : ℕ) : ℝ) / (2 : ℝ) ^ b) := by
      have hsplit : b = (b - 5) + 5 := by omega
      rw [hsplit, pow_add]
      norm_num
      ring
    _ ≤ 1664 * ((1 + (b : ℝ) ^ 2) / (2 : ℝ) ^ b) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_right (add_one_le_quadratic b) (by positivity)
    _ ≤ 1664 *
        (2 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1)) :=
      mul_le_mul_of_nonneg_left (quadratic_model_conversion b) (by norm_num)
    _ = 3328 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) := by ring

private theorem small_tail_polynomial_le
    {b : ℕ} (hb : b < 6) (m : ℕ) :
    ((m + 6 - b : ℕ) : ℝ) ^ 2 * ((m + 2 : ℕ) : ℝ) ≤
      72 * ((m + 1 : ℕ) : ℝ) ^ 3 := by
  have hA_nat : m + 6 - b ≤ 6 * (m + 1) := by omega
  have hB_nat : m + 2 ≤ 2 * (m + 1) := by omega
  have hA : ((m + 6 - b : ℕ) : ℝ) ≤
      6 * ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hA_nat
  have hB : ((m + 2 : ℕ) : ℝ) ≤
      2 * ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hB_nat
  calc
    ((m + 6 - b : ℕ) : ℝ) ^ 2 * ((m + 2 : ℕ) : ℝ) ≤
        (6 * ((m + 1 : ℕ) : ℝ)) ^ 2 * ((m + 2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hA 2)
        (by positivity)
    _ ≤ (6 * ((m + 1 : ℕ) : ℝ)) ^ 2 *
        (2 * ((m + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    _ = 72 * ((m + 1 : ℕ) : ℝ) ^ 3 := by ring

private theorem ford33aSmallPolynomialTail_le
    {b : ℕ} (hb : b < 6) (R : ℕ) :
    (∑ m ∈ Finset.range R,
        ((m + 6 - b : ℕ) : ℝ) ^ 2 * ((m + 2 : ℕ) : ℝ) /
          (2 : ℝ) ^ m) ≤ 3744 := by
  calc
    (∑ m ∈ Finset.range R,
        ((m + 6 - b : ℕ) : ℝ) ^ 2 * ((m + 2 : ℕ) : ℝ) /
          (2 : ℝ) ^ m) ≤
        72 * cubicGeometricPartial R := by
      rw [cubicGeometricPartial, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (small_tail_polynomial_le hb m)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m)
    _ ≤ 72 * 52 :=
      mul_le_mul_of_nonneg_left (cubicGeometricPartial_le R) (by norm_num)
    _ = 3744 := by norm_num

theorem ford33aPolynomialTail_le (b R : ℕ) :
    ford33aPolynomialTail b R ≤
      8192 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) := by
  by_cases hb : 6 ≤ b
  · rw [ford33aPolynomialTail, if_pos hb]
    exact (ford33aLargePolynomialTail_le hb R).trans <| by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [show 0 ≤ (b : ℝ) ^ 2 by positivity]
  · have hb' : b < 6 := by omega
    rw [ford33aPolynomialTail, if_neg hb]
    refine (ford33aSmallPolynomialTail_le hb' R).trans ?_
    interval_cases b <;> norm_num

/-- Ford's closed numerical summation (33a), uniformly in the finite tail
cutoff.  The explicit constant `16384` is absolute and deliberately coarse. -/
theorem ford33aNumericalSum_le (b R : ℕ) :
    ford33aNumericalSum b R ≤
      16384 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) := by
  have hhead := ford33aDoubleExponentialHead_le b
  have htail := ford33aPolynomialTail_le b R
  have hmodel : 0 ≤
      (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) := by positivity
  rw [ford33aNumericalSum]
  calc
    ford33aDoubleExponentialHead b + ford33aPolynomialTail b R ≤
        2 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) +
          8192 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) :=
      add_le_add hhead htail
    _ = 8194 * ((1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1)) := by ring
    _ ≤ 16384 * ((1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1)) := by
      nlinarith
    _ = 16384 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) := by ring

end Erdos446
