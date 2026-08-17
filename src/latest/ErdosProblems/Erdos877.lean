/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos877.Resolution

/-!
# Erdős Problem 877

For `n : ℕ`, let `f_m(n)` be the number of maximal sum-free subsets of
`{1, ..., n}`.  Here a finite set `A` is sum-free when there are no
`a, b, c ∈ A` satisfying `a = b + c`; the summands are allowed to coincide.
Maximality is relative to `{1, ..., n}` and is with respect to inclusion.

The definitions are `Erdos877.SumFree`, `Erdos877.MaximalSumFreeIn`, and
`Erdos877.maximalSumFreeCount`.  The theorem `erdos_877` formalizes the
affirmative answer to the question in the problem:

`f_m(n) = o(2^(n/2))`.

The stronger theorem `erdos_877_exponential_bound` records the fixed
exponential saving proved along the way.  Its exponent
`Erdos877.resolutionExponent` is explicitly defined and is strictly less
than `1 / 2`.
-/

open Filter
open scoped Topology

namespace Erdos877

/-- The larger of the two bases controlling the small- and large-cardinality
parts of the maximal sum-free family. -/
private noncomputable def preliminaryBase : ℝ :=
  max (7 / 5 : ℝ) largeBase

/-- A fixed base strictly between both counting bases and `sqrt 2`. -/
noncomputable def resolutionBase : ℝ :=
  (preliminaryBase + Real.sqrt 2) / 2

/-- The base-`2` exponent of `resolutionBase`. -/
noncomputable def resolutionExponent : ℝ :=
  Real.logb 2 resolutionBase

private theorem preliminaryBase_nonneg : 0 ≤ preliminaryBase := by
  rw [preliminaryBase]
  exact (by norm_num : (0 : ℝ) ≤ 7 / 5).trans (le_max_left _ _)

private theorem preliminaryBase_lt_sqrt_two : preliminaryBase < Real.sqrt 2 := by
  rw [preliminaryBase]
  exact max_lt seven_fifths_lt_sqrt_two largeBase_lt_sqrt_two

private theorem preliminaryBase_lt_resolutionBase :
    preliminaryBase < resolutionBase := by
  rw [resolutionBase]
  linarith [preliminaryBase_lt_sqrt_two]

theorem resolutionBase_pos : 0 < resolutionBase := by
  rw [resolutionBase]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  nlinarith [preliminaryBase_nonneg]

theorem resolutionBase_lt_sqrt_two : resolutionBase < Real.sqrt 2 := by
  rw [resolutionBase]
  linarith [preliminaryBase_lt_sqrt_two]

/-- The exponent in the stronger bound is genuinely below `1 / 2`. -/
theorem resolutionExponent_lt_half : resolutionExponent < (1 / 2 : ℝ) := by
  rw [resolutionExponent]
  rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) resolutionBase_pos]
  simpa [Real.sqrt_eq_rpow] using resolutionBase_lt_sqrt_two

private theorem eventually_two_mul_preliminaryBase_pow_le_resolutionBase_pow :
    ∀ᶠ n : ℕ in atTop,
      2 * preliminaryBase ^ n ≤ resolutionBase ^ n := by
  have hlittle :
      (fun n : ℕ ↦ preliminaryBase ^ n) =o[atTop]
        (fun n : ℕ ↦ resolutionBase ^ n) :=
    isLittleO_pow_pow_of_lt_left preliminaryBase_nonneg
      preliminaryBase_lt_resolutionBase
  filter_upwards [hlittle.bound (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  have hn' : preliminaryBase ^ n ≤ (1 / 2 : ℝ) * resolutionBase ^ n := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg preliminaryBase_nonneg n),
      abs_of_nonneg (pow_nonneg (le_of_lt resolutionBase_pos) n)] using hn
  nlinarith

private theorem resolutionBase_pow_eq_rpow (n : ℕ) :
    resolutionBase ^ n =
      Real.rpow 2 (resolutionExponent * (n : ℝ)) := by
  rw [resolutionExponent]
  calc
    resolutionBase ^ n = Real.rpow resolutionBase (n : ℝ) := by
      exact (Real.rpow_natCast resolutionBase n).symm
    _ = Real.rpow (Real.rpow 2 (Real.logb 2 resolutionBase)) (n : ℝ) := by
      congr 1
      exact (Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1) resolutionBase_pos).symm
    _ = Real.rpow 2 (Real.logb 2 resolutionBase * (n : ℝ)) := by
      exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm

/-- Stronger quantitative resolution of Problem 877: the maximal sum-free
count is eventually bounded by a fixed real power `2^(c n)`, where the
explicit constant `c = resolutionExponent` is strictly less than `1 / 2`.
-/
theorem erdos_877_exponential_bound :
    ∀ᶠ n : ℕ in atTop,
      (maximalSumFreeCount n : ℝ) ≤
        Real.rpow 2 (resolutionExponent * (n : ℝ)) := by
  filter_upwards [Enumeration.eventually_sumFreeCount_le_pow,
    eventually_ge_atTop (2 ^ 33),
    eventually_two_mul_preliminaryBase_pow_le_resolutionBase_pow]
      with n hsf hn habsorb
  have hsmall :
      ((smallMaximalSumFreeSets n).card : ℝ) ≤ preliminaryBase ^ n := by
    calc
      ((smallMaximalSumFreeSets n).card : ℝ) ≤ (7 / 5 : ℝ) ^ n :=
        smallMaximalSumFreeSets_card_le_seven_fifths_pow n
      _ ≤ preliminaryBase ^ n := by
        gcongr
        exact (show (7 / 5 : ℝ) ≤ preliminaryBase by
          rw [preliminaryBase]
          exact le_max_left _ _)
  have hlarge :
      ((largeMaximalSumFreeSets n).card : ℝ) ≤ preliminaryBase ^ n := by
    calc
      ((largeMaximalSumFreeSets n).card : ℝ) ≤
          (((2 : ℕ) ^ (n / 2 - n / 2 ^ 26) : ℕ) : ℝ) := by
        exact_mod_cast largeMaximalSumFreeSets_card_le_pow n hn hsf
      _ ≤ largeBase ^ n :=
        cast_pow_deletion_exponent_le_largeBase_pow n hn
      _ ≤ preliminaryBase ^ n := by
        apply pow_le_pow_left₀ largeBase_nonneg
        exact (show largeBase ≤ preliminaryBase from by
          rw [preliminaryBase]
          exact le_max_right _ _)
  calc
    (maximalSumFreeCount n : ℝ) =
        ((smallMaximalSumFreeSets n).card : ℝ) +
          ((largeMaximalSumFreeSets n).card : ℝ) := by
      rw [maximalSumFreeCount_eq_small_add_large, Nat.cast_add]
    _ ≤ 2 * preliminaryBase ^ n := by linarith
    _ ≤ resolutionBase ^ n := habsorb
    _ = Real.rpow 2 (resolutionExponent * (n : ℝ)) :=
      resolutionBase_pow_eq_rpow n

/-- Erdős Problem 877: the number of maximal sum-free subsets of
`{1, ..., n}` is little-o of `2^(n/2)`. -/
theorem erdos_877 :
    (fun n : ℕ ↦ (maximalSumFreeCount n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ Real.rpow 2 ((n : ℝ) / 2)) := by
  change (fun n : ℕ ↦ (maximalSumFreeCount n : ℝ)) =o[atTop] benchmark
  exact maximalSumFreeCount_isLittleO

#print axioms erdos_877

end Erdos877
