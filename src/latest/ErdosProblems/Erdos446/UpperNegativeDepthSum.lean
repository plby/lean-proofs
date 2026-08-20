/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperFiniteLayerSum

/-!
# Erdős Problem 446: the numerical layer tail below the central depth

When `k < v`, Ford's signed parameter `b = k-v` is negative.  Writing
`d = v-k`, the second sum in (33a) becomes a polynomially weighted geometric
tail with numerator `(m+6+d)^2 (m+2)`.  This file proves the required
uniform `O(1+d^2)` bound at every finite cutoff.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable def ford33aNegativeDepthTail (d R : ℕ) : ℝ :=
  ∑ m ∈ Finset.range R,
    ((m + 6 + d : ℕ) : ℝ) ^ 2 * ((m + 2 : ℕ) : ℝ) /
      (2 : ℝ) ^ m

private theorem negativeDepthPolynomial_le (d m : ℕ) :
    ((m + 6 + d : ℕ) : ℝ) ^ 2 * ((m + 2 : ℕ) : ℝ) ≤
      144 * (1 + (d : ℝ) ^ 2) * ((m + 1 : ℕ) : ℝ) ^ 3 := by
  have hfirstNat : m + 6 + d ≤ (d + 6) * (m + 1) := by
    nlinarith [Nat.zero_le (d * m)]
  have hsecondNat : m + 2 ≤ 2 * (m + 1) := by omega
  have hfirst : ((m + 6 + d : ℕ) : ℝ) ≤
      ((d + 6 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hfirstNat
  have hsecond : ((m + 2 : ℕ) : ℝ) ≤
      2 * ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hsecondNat
  have hd : (((d + 6 : ℕ) : ℝ) ^ 2) ≤
      72 * (1 + (d : ℝ) ^ 2) := by
    push_cast
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  calc
    ((m + 6 + d : ℕ) : ℝ) ^ 2 * ((m + 2 : ℕ) : ℝ) ≤
        ((((d + 6 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) ^ 2) *
          ((m + 2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hfirst 2)
        (by positivity)
    _ ≤ ((((d + 6 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) ^ 2) *
          (2 * ((m + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsecond (by positivity)
    _ = 2 * (((d + 6 : ℕ) : ℝ) ^ 2) *
          ((m + 1 : ℕ) : ℝ) ^ 3 := by ring
    _ ≤ 2 * (72 * (1 + (d : ℝ) ^ 2)) *
          ((m + 1 : ℕ) : ℝ) ^ 3 := by gcongr
    _ = 144 * (1 + (d : ℝ) ^ 2) *
          ((m + 1 : ℕ) : ℝ) ^ 3 := by ring

theorem ford33aNegativeDepthTail_le (d R : ℕ) :
    ford33aNegativeDepthTail d R ≤ 8192 * (1 + (d : ℝ) ^ 2) := by
  calc
    ford33aNegativeDepthTail d R ≤
        144 * (1 + (d : ℝ) ^ 2) * cubicGeometricPartial R := by
      rw [ford33aNegativeDepthTail, cubicGeometricPartial,
        Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (negativeDepthPolynomial_le d m)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m)
    _ ≤ 144 * (1 + (d : ℝ) ^ 2) * 52 := by
      apply mul_le_mul_of_nonneg_left (cubicGeometricPartial_le R)
      positivity
    _ ≤ 8192 * (1 + (d : ℝ) ^ 2) := by
      have hd : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg _
      nlinarith

end Erdos446
