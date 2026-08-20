/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperFiniteLayers

/-!
# Erdős Problem 446: the numerical dyadic-layer sum

After the layer/barrier inclusion, put `b = k - v` and
`w = m + blockLayerSlack k - b`.  The quantitative Smirnov bound contributes
the polynomial `(b+w+1)(w+1)^2/k`, while the dyadic layer contributes
`2^(blockLayerSlack k-b-w)`.  This file proves, uniformly in every finite
cutoff, that the resulting reindexed sum has Ford's required
`(1+b^2)/(2^b+1)` decay.

The only numerical series used is

`sum_{w>=0} (w+1)^3 / 2^w = 52`.

We prove its finite partial-sum bound by an exact polynomial remainder, so
no infinite-series machinery or hidden analytic assumption is involved.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable def cubicGeometricPartial (R : ℕ) : ℝ :=
  ∑ w ∈ Finset.range R, ((w + 1 : ℕ) : ℝ) ^ 3 / (2 : ℝ) ^ w

noncomputable def cubicGeometricRemainder (R : ℕ) : ℝ :=
  (2 * (R : ℝ) ^ 3 + 12 * (R : ℝ) ^ 2 + 36 * (R : ℝ) + 52) /
    (2 : ℝ) ^ R

private theorem cubicGeometricRemainder_step (R : ℕ) :
    cubicGeometricRemainder R =
      ((R + 1 : ℕ) : ℝ) ^ 3 / (2 : ℝ) ^ R +
        cubicGeometricRemainder (R + 1) := by
  rw [cubicGeometricRemainder, cubicGeometricRemainder, pow_succ]
  push_cast
  field_simp
  ring

theorem cubicGeometricPartial_add_remainder (R : ℕ) :
    cubicGeometricPartial R + cubicGeometricRemainder R = 52 := by
  induction R with
  | zero => norm_num [cubicGeometricPartial, cubicGeometricRemainder]
  | succ R ih =>
      rw [cubicGeometricPartial, Finset.sum_range_succ]
      change cubicGeometricPartial R +
          ((R + 1 : ℕ) : ℝ) ^ 3 / (2 : ℝ) ^ R +
            cubicGeometricRemainder (R + 1) = 52
      calc
        cubicGeometricPartial R +
            ((R + 1 : ℕ) : ℝ) ^ 3 / (2 : ℝ) ^ R +
              cubicGeometricRemainder (R + 1) =
            cubicGeometricPartial R + cubicGeometricRemainder R := by
          have hstep := cubicGeometricRemainder_step R
          linarith
        _ = 52 := ih

theorem cubicGeometricPartial_le (R : ℕ) :
    cubicGeometricPartial R ≤ 52 := by
  have hrem : 0 ≤ cubicGeometricRemainder R := by
    dsimp [cubicGeometricRemainder]
    positivity
  linarith [cubicGeometricPartial_add_remainder R]

/-- The reindexed numerical factor left after applying the quantitative
Smirnov probability estimate to dyadic layers. -/
noncomputable def fordReindexedLayerSum (k b R : ℕ) : ℝ :=
  (2 : ℝ) ^ blockLayerSlack k / ((2 : ℝ) ^ b * (k : ℝ)) *
    ∑ w ∈ Finset.range R,
      ((b + w + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 /
        (2 : ℝ) ^ w

private theorem layerPolynomial_le_cubic (b w : ℕ) :
    ((b + w + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 ≤
      ((b + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 3 := by
  have hbw : (b + w + 1 : ℕ) ≤ (b + 1) * (w + 1) := by
    nlinarith
  have hcast : ((b + w + 1 : ℕ) : ℝ) ≤
      ((b + 1) * (w + 1) : ℕ) := by exact_mod_cast hbw
  calc
    ((b + w + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 ≤
        (((b + 1) * (w + 1) : ℕ) : ℝ) *
          ((w + 1 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = ((b + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 3 := by
      push_cast
      ring

private theorem layerPolynomialSum_le (b R : ℕ) :
    (∑ w ∈ Finset.range R,
        ((b + w + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 /
          (2 : ℝ) ^ w) ≤
      (b + 1 : ℕ) * cubicGeometricPartial R := by
  rw [cubicGeometricPartial, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  simpa only [mul_div_assoc] using
    div_le_div_of_nonneg_right (layerPolynomial_le_cubic b w)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) w)

private theorem layerScale_over_k_le_four {k : ℕ} (hk : 0 < k) :
    (2 : ℝ) ^ blockLayerSlack k / (k : ℝ) ≤ 4 := by
  have hpowN := two_pow_blockLayerSlack_le k
  have hpowR : (2 : ℝ) ^ blockLayerSlack k ≤ 2 * (k + 1 : ℕ) := by
    exact_mod_cast hpowN
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkOneR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  apply (div_le_iff₀ hkR).2
  calc
    (2 : ℝ) ^ blockLayerSlack k ≤ 2 * (k + 1 : ℕ) := hpowR
    _ ≤ 4 * (k : ℝ) := by
      push_cast
      nlinarith

private theorem add_one_div_pow_le_two_model (b : ℕ) :
    ((b + 1 : ℕ) : ℝ) / (2 : ℝ) ^ b ≤
      2 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have hden : (0 : ℝ) < (2 : ℝ) ^ b + 1 := by positivity
  have hpoly : ((b + 1 : ℕ) : ℝ) ≤ 1 + (b : ℝ) ^ 2 := by
    have hnat : b + 1 ≤ 1 + b ^ 2 := by
      cases b with
      | zero => simp
      | succ b =>
          nlinarith
    exact_mod_cast hnat
  have hratio : ((2 : ℝ) ^ b + 1) ≤ 2 * (2 : ℝ) ^ b := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
    linarith
  apply (div_le_div_iff₀ hpow hden).2
  calc
    ((b + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ b + 1) ≤
        (1 + (b : ℝ) ^ 2) * ((2 : ℝ) ^ b + 1) :=
      mul_le_mul_of_nonneg_right hpoly hden.le
    _ ≤ (1 + (b : ℝ) ^ 2) * (2 * (2 : ℝ) ^ b) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 2 * (1 + (b : ℝ) ^ 2) * (2 : ℝ) ^ b := by ring

/-- Closed numerical layer estimate.  The constant is deliberately coarse;
its independence of `k`, `b`, and the finite cutoff is what is used by the
upper-bound assembly. -/
theorem fordReindexedLayerSum_le
    {k : ℕ} (hk : 0 < k) (b R : ℕ) :
    fordReindexedLayerSum k b R ≤
      416 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpowb : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have hsumNonneg :
      0 ≤ ∑ w ∈ Finset.range R,
        ((b + w + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 /
          (2 : ℝ) ^ w := by positivity
  have hpoly := layerPolynomialSum_le b R
  have hcubic := cubicGeometricPartial_le R
  have hscale := layerScale_over_k_le_four hk
  calc
    fordReindexedLayerSum k b R =
        (((2 : ℝ) ^ blockLayerSlack k / (k : ℝ)) /
          (2 : ℝ) ^ b) *
          (∑ w ∈ Finset.range R,
            ((b + w + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 /
              (2 : ℝ) ^ w) := by
      rw [fordReindexedLayerSum]
      field_simp
    _ ≤ (4 / (2 : ℝ) ^ b) *
          (∑ w ∈ Finset.range R,
            ((b + w + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 /
              (2 : ℝ) ^ w) := by
      apply mul_le_mul_of_nonneg_right _ hsumNonneg
      exact div_le_div_of_nonneg_right hscale hpowb.le
    _ ≤ (4 / (2 : ℝ) ^ b) *
          ((b + 1 : ℕ) * cubicGeometricPartial R) := by
      exact mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ ≤ (4 / (2 : ℝ) ^ b) * (((b + 1 : ℕ) : ℝ) * 52) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcubic (by positivity)
    _ = 208 * (((b + 1 : ℕ) : ℝ) / (2 : ℝ) ^ b) := by ring
    _ ≤ 208 *
        (2 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1)) :=
      mul_le_mul_of_nonneg_left (add_one_div_pow_le_two_model b) (by norm_num)
    _ = 416 * (1 + (b : ℝ) ^ 2) / ((2 : ℝ) ^ b + 1) := by ring

end Erdos446
