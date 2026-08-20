/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.Moment
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Erdős Problem 446: weighted divisor-cluster inequality

The pointwise cluster moment inequality is combined with finite
Cauchy--Schwarz, with reciprocal-integer weights.  This is the exact finite
inequality used in Ford's lower-bound argument.
-/

namespace Erdos446

open Finset Set MeasureTheory Real
open scoped BigOperators ENNReal NNReal Topology

/-- The pointwise cluster inequality after cancelling the positive common
factor `log 2`. -/
theorem card_divisors_sq_mul_log_two_le (a : ℕ) :
    (a.divisors.card : ℝ) ^ 2 * Real.log 2 ≤
      clusterLength a * (closePairCount a : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := divisor_cluster_second_moment a
  have hmul :
      (((a.divisors.card : ℝ) ^ 2 * Real.log 2) * Real.log 2) ≤
        (clusterLength a * (closePairCount a : ℝ)) * Real.log 2 := by
    calc
      ((a.divisors.card : ℝ) ^ 2 * Real.log 2) * Real.log 2 =
          ((a.divisors.card : ℝ) * Real.log 2) ^ 2 := by ring
      _ ≤ clusterLength a * ((closePairCount a : ℝ) * Real.log 2) := h
      _ = (clusterLength a * (closePairCount a : ℝ)) * Real.log 2 := by ring
  exact le_of_mul_le_mul_right hmul hlog

/-- The reciprocal-weight form of the pointwise cluster inequality. -/
theorem weighted_card_divisors_sq_le (a : ℕ) (ha : 0 < a) :
    (Real.sqrt (Real.log 2) * ((a.divisors.card : ℝ) / a)) ^ 2 ≤
      (clusterLength a / a) * ((closePairCount a : ℝ) / a) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haSq : (0 : ℝ) < (a : ℝ) ^ 2 := sq_pos_of_pos haR
  have hbase := card_divisors_sq_mul_log_two_le a
  calc
    (Real.sqrt (Real.log 2) * ((a.divisors.card : ℝ) / a)) ^ 2 =
        ((a.divisors.card : ℝ) ^ 2 * Real.log 2) / (a : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hlog]
      ring
    _ ≤ (clusterLength a * (closePairCount a : ℝ)) / (a : ℝ) ^ 2 :=
      (div_le_div_iff_of_pos_right haSq).mpr hbase
    _ = (clusterLength a / a) * ((closePairCount a : ℝ) / a) := by
      field_simp

/-- Ford's finite weighted Cauchy--Schwarz cluster inequality.  The constant
here is the sharper `log 2`; Ford's displayed constant `1/6` follows by a
harmless numerical relaxation. -/
theorem weighted_cluster_cauchy (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) :
    (∑ a ∈ A, (a.divisors.card : ℝ) / a) ^ 2 * Real.log 2 ≤
      (∑ a ∈ A, clusterLength a / a) *
        (∑ a ∈ A, (closePairCount a : ℝ) / a) := by
  let r : ℕ → ℝ := fun a ↦
    Real.sqrt (Real.log 2) * ((a.divisors.card : ℝ) / a)
  let f : ℕ → ℝ := fun a ↦ clusterLength a / a
  let g : ℕ → ℝ := fun a ↦ (closePairCount a : ℝ) / a
  have hf : ∀ a ∈ A, 0 ≤ f a := by
    intro a ha
    exact div_nonneg (clusterLength_nonneg a) (Nat.cast_nonneg a)
  have hg : ∀ a ∈ A, 0 ≤ g a := by
    intro a ha
    positivity
  have hr : ∀ a ∈ A, r a ^ 2 ≤ f a * g a := by
    intro a ha
    exact weighted_card_divisors_sq_le a (hA a ha)
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul A hf hg hr
  have hsum : (∑ a ∈ A, r a) =
      Real.sqrt (Real.log 2) *
        (∑ a ∈ A, (a.divisors.card : ℝ) / a) := by
    dsimp [r]
    exact (Finset.mul_sum _ _ _).symm
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [hsum] at hcs
  dsimp [f, g] at hcs
  calc
    (∑ a ∈ A, (a.divisors.card : ℝ) / a) ^ 2 * Real.log 2 =
        (Real.sqrt (Real.log 2) *
          (∑ a ∈ A, (a.divisors.card : ℝ) / a)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hlog]
      ring
    _ ≤ (∑ a ∈ A, clusterLength a / a) *
        (∑ a ∈ A, (closePairCount a : ℝ) / a) := hcs

end Erdos446
