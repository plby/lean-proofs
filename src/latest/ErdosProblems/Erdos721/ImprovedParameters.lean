/- leanprover/lean4:v4.33.0 -/
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

import ErdosProblems.Erdos721.ImprovedDensityIncrement

/-!
# Explicit parameters for the improved density increment

This file chooses the convolution exponent and the spectral-smoothing
radius used in the improved Bloom--Sisask bootstrapping argument.  The
lemmas below verify the geometric tail and smoothing error with their exact
normalizations.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal Indicator mu NNReal Pointwise

namespace CyclicImprovedParameters

variable {N : ℕ} [NeZero N]

/-- The convolution exponent which makes the spectral tail at `eta = 1/2`
smaller than the density-normalized error budget. -/
noncomputable def improvedExponent (epsilon beta : ℝ) : ℕ :=
  ⌈Real.logb 2 (512 / (epsilon * beta))⌉₊

/-- The smoothing radius which absorbs the exact Chang rank produced by a
Croot--Sisask shift set. -/
noncomputable def improvedRho (epsilon beta : ℝ)
    (X : Finset (ZMod N)) : ℝ :=
  epsilon * beta /
    (256 * ((CyclicChang.changRankBound X (1 / 2) : ℝ) + 1))

lemma improvedExponent_pos {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) :
    0 < improvedExponent epsilon beta := by
  apply Nat.ceil_pos.mpr
  apply Real.logb_pos (by norm_num)
  rw [one_lt_div (mul_pos hepsilon hbeta)]
  nlinarith [mul_le_mul hepsilon1.le hbeta1 hbeta.le zero_le_one]

lemma improvedExponent_ne_zero {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) :
    improvedExponent epsilon beta ≠ 0 :=
  Nat.ne_of_gt (improvedExponent_pos hepsilon hepsilon1 hbeta hbeta1)

lemma improvedExponent_tail {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) :
    (1 / 2 : ℝ) ^ improvedExponent epsilon beta ≤
      epsilon * beta / 512 := by
  let r : ℝ := 512 / (epsilon * beta)
  have hr : 0 < r := div_pos (by norm_num) (mul_pos hepsilon hbeta)
  have hceil : Real.logb 2 r ≤ (improvedExponent epsilon beta : ℝ) := by
    exact_mod_cast Nat.le_ceil (Real.logb 2 r)
  have hrpow : r ≤ (2 : ℝ) ^ (improvedExponent epsilon beta : ℝ) := by
    rw [← Real.logb_le_iff_le_rpow (by norm_num : 1 < (2 : ℝ)) hr]
    exact hceil
  rw [Real.rpow_natCast] at hrpow
  calc
    (1 / 2 : ℝ) ^ improvedExponent epsilon beta =
        ((2 : ℝ) ^ improvedExponent epsilon beta)⁻¹ := by
      rw [one_div, inv_pow]
    _ ≤ r⁻¹ := inv_anti₀ hr hrpow
    _ = epsilon * beta / 512 := by
      dsimp only [r]
      field_simp

/-- The ceiling costs less than one beyond the logarithmic exponent. -/
lemma improvedExponent_lt_logb_add_one {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) :
    (improvedExponent epsilon beta : ℝ) <
      Real.logb 2 (512 / (epsilon * beta)) + 1 := by
  apply Nat.ceil_lt_add_one
  exact (Real.logb_pos (by norm_num) (by
    rw [one_lt_div (mul_pos hepsilon hbeta)]
    nlinarith [mul_le_mul hepsilon1.le hbeta1 hbeta.le zero_le_one])).le

lemma improvedRho_pos {epsilon beta : ℝ}
    (X : Finset (ZMod N)) (hepsilon : 0 < epsilon) (hbeta : 0 < beta) :
    0 < improvedRho epsilon beta X := by
  apply div_pos (mul_pos hepsilon hbeta)
  positivity

/-- With the explicit exponent and radius, the full smoothing error is at
most `epsilon / 64` after conversion from probability normalization to the
relative density `beta`. -/
lemma explicit_improved_smoothing_error_bound
    {epsilon beta : ℝ} (A X : Finset (ZMod N)) (scale : ℕ)
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hA : A.Nonempty)
    (hdensity : beta * scale = A.card) :
    scale *
        (((CyclicChang.changRankBound X (1 / 2) : ℝ) *
            improvedRho epsilon beta X +
          2 * (1 / 2 : ℝ) ^ improvedExponent epsilon beta) *
          (A.card : ℝ)⁻¹) ≤ epsilon / 64 := by
  let d : ℝ := CyclicChang.changRankBound X (1 / 2)
  have hd : 0 ≤ d := by positivity
  have hd1 : 0 < d + 1 := by positivity
  have hdrho : d * improvedRho epsilon beta X ≤ epsilon * beta / 256 := by
    rw [improvedRho]
    calc
      d * (epsilon * beta / (256 * (d + 1))) =
          (epsilon * beta / 256) * (d / (d + 1)) := by field_simp
      _ ≤ (epsilon * beta / 256) * 1 := by
        gcongr
        exact (div_le_one hd1).2 (by linarith)
      _ = epsilon * beta / 256 := by ring
  have htail := improvedExponent_tail hepsilon hbeta
  have htwotail :
      2 * (1 / 2 : ℝ) ^ improvedExponent epsilon beta ≤
        epsilon * beta / 256 := by
    linarith
  have herr :
      d * improvedRho epsilon beta X +
          2 * (1 / 2 : ℝ) ^ improvedExponent epsilon beta ≤
        epsilon * beta / 128 := by
    linarith
  have hcard : 0 < (A.card : ℝ) := by
    exact_mod_cast card_pos.mpr hA
  have hratio : (scale : ℝ) * (A.card : ℝ)⁻¹ = beta⁻¹ := by
    field_simp [hbeta.ne', hcard.ne']
    nlinarith [hdensity]
  change (scale : ℝ) *
      (((d * improvedRho epsilon beta X +
        2 * (1 / 2 : ℝ) ^ improvedExponent epsilon beta) *
        (A.card : ℝ)⁻¹)) ≤ epsilon / 64
  calc
    (scale : ℝ) *
        ((d * improvedRho epsilon beta X +
          2 * (1 / 2 : ℝ) ^ improvedExponent epsilon beta) *
          (A.card : ℝ)⁻¹) =
        (d * improvedRho epsilon beta X +
          2 * (1 / 2 : ℝ) ^ improvedExponent epsilon beta) * beta⁻¹ := by
      rw [← hratio]
      ring
    _ ≤ (epsilon * beta / 128) * beta⁻¹ := by
      exact mul_le_mul_of_nonneg_right herr (inv_nonneg.mpr hbeta.le)
    _ = epsilon / 128 := by field_simp
    _ ≤ epsilon / 64 := by linarith

end CyclicImprovedParameters

end Erdos721
