/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.PrimeCluster

/-!
# Erdős Problem 446: analytic lower reduction

This file sums the pointwise eligible-prime estimate over a finite family and
combines it with the exact CRT lower bound.  What remains is Ford's finite
prime-block construction, expressed only through reciprocal divisor and
close-pair sums.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Engel's form of Cauchy--Schwarz for the reciprocal close-pair weights. -/
theorem divisor_close_pair_cauchy (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) :
    (∑ a ∈ A, (a.divisors.card : ℝ) / a) ^ 2 ≤
      (∑ a ∈ A,
        (a.divisors.card : ℝ) ^ 2 /
          ((a : ℝ) * (closePairCount a : ℝ))) *
      (∑ a ∈ A, (closePairCount a : ℝ) / a) := by
  let r : ℕ → ℝ := fun a ↦ (a.divisors.card : ℝ) / a
  let f : ℕ → ℝ := fun a ↦
    (a.divisors.card : ℝ) ^ 2 / ((a : ℝ) * (closePairCount a : ℝ))
  let g : ℕ → ℝ := fun a ↦ (closePairCount a : ℝ) / a
  have hW (a : ℕ) (ha : a ∈ A) : (0 : ℝ) < closePairCount a := by
    exact_mod_cast lt_of_lt_of_le
      (Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (hA a ha).ne'⟩)
      (card_divisors_le_closePairCount a)
  have hf : ∀ a ∈ A, 0 ≤ f a := by
    intro a ha
    dsimp [f]
    positivity
  have hg : ∀ a ∈ A, 0 ≤ g a := by
    intro a ha
    dsimp [g]
    positivity
  have hr : ∀ a ∈ A, r a ^ 2 ≤ f a * g a := by
    intro a ha
    have haR : (0 : ℝ) < a := by exact_mod_cast hA a ha
    have hWR := hW a ha
    dsimp [r, f, g]
    field_simp [haR.ne', hWR.ne']
    exact le_rfl
  simpa [r, f, g] using
    (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul A hf hg hr)

/-- Summing the eligible-prime lower bound and applying Engel Cauchy. -/
theorem sum_eligiblePrimeMass_lower
    {N y : ℕ} {A : Finset ℕ} (hN : 3 ≤ N)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
      dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ))
    (hA : ∀ a ∈ A, 0 < a)
    (hscale : ∀ a ∈ A, ∀ d ∈ a.divisors,
      N ≤ y / d ∧ y ≤ (y / d) ^ 2) :
    ((1 / 96 : ℝ) / Real.log (y : ℝ)) *
        (∑ a ∈ A, (a.divisors.card : ℝ) / a) ^ 2 ≤
      (∑ a ∈ A, (1 / (a : ℝ)) * eligiblePrimeMass y a) *
        (∑ a ∈ A, (closePairCount a : ℝ) / a) := by
  by_cases hAempty : A = ∅
  · subst A
    simp
  have hy3 : 3 ≤ y := by
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hAempty
    have hdone : 1 ∈ a.divisors := Nat.one_mem_divisors.mpr (hA a ha).ne'
    have hs := (hscale a ha 1 hdone).1
    exact hN.trans (by simpa using hs)
  have hylog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hpoint : ∀ a ∈ A,
      ((a.divisors.card : ℝ) ^ 2) /
          ((a : ℝ) * (closePairCount a : ℝ)) *
          ((1 / 96 : ℝ) / Real.log (y : ℝ)) ≤
        (1 / (a : ℝ)) * eligiblePrimeMass y a := by
    intro a ha
    have haR : (0 : ℝ) < a := by exact_mod_cast hA a ha
    have hW : (0 : ℝ) < closePairCount a := by
      exact_mod_cast lt_of_lt_of_le
        (Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (hA a ha).ne'⟩)
        (card_divisors_le_closePairCount a)
    have hp := eligiblePrimeMass_lower_of_divisor_scales
      hN hprime (hA a ha) (hscale a ha)
    calc
      ((a.divisors.card : ℝ) ^ 2) /
            ((a : ℝ) * (closePairCount a : ℝ)) *
            ((1 / 96 : ℝ) / Real.log (y : ℝ)) =
          (1 / (a : ℝ)) *
            (((a.divisors.card : ℝ) ^ 2) /
              (96 * (closePairCount a : ℝ) * Real.log (y : ℝ))) := by
                field_simp [haR.ne', hW.ne', hylog.ne']
      _ ≤ (1 / (a : ℝ)) * eligiblePrimeMass y a := by
        exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hsumPoint :
      (∑ a ∈ A,
          (a.divisors.card : ℝ) ^ 2 /
            ((a : ℝ) * (closePairCount a : ℝ))) *
          ((1 / 96 : ℝ) / Real.log (y : ℝ)) ≤
        ∑ a ∈ A, (1 / (a : ℝ)) * eligiblePrimeMass y a := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hpoint
  have hcauchy := divisor_close_pair_cauchy A hA
  have hfactor : 0 ≤ (1 / 96 : ℝ) / Real.log (y : ℝ) := by positivity
  have hWsum : 0 ≤ ∑ a ∈ A, (closePairCount a : ℝ) / a := by
    apply Finset.sum_nonneg
    intro a ha
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    ((1 / 96 : ℝ) / Real.log (y : ℝ)) *
          (∑ a ∈ A, (a.divisors.card : ℝ) / a) ^ 2 ≤
        ((1 / 96 : ℝ) / Real.log (y : ℝ)) *
          ((∑ a ∈ A,
              (a.divisors.card : ℝ) ^ 2 /
                ((a : ℝ) * (closePairCount a : ℝ))) *
            (∑ a ∈ A, (closePairCount a : ℝ) / a)) :=
      mul_le_mul_of_nonneg_left hcauchy hfactor
    _ = ((∑ a ∈ A,
            (a.divisors.card : ℝ) ^ 2 /
              ((a : ℝ) * (closePairCount a : ℝ))) *
          ((1 / 96 : ℝ) / Real.log (y : ℝ))) *
        (∑ a ∈ A, (closePairCount a : ℝ) / a) := by ring
    _ ≤ (∑ a ∈ A, (1 / (a : ℝ)) * eligiblePrimeMass y a) *
        (∑ a ∈ A, (closePairCount a : ℝ) / a) :=
      mul_le_mul_of_nonneg_right hsumPoint hWsum

/-- Ford's lower reduction after the prime and CRT arguments. -/
theorem ford_cluster_lower_reduction
    {N y B : ℕ} {A : Finset ℕ} (hN : 3 ≤ N)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
      dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ))
    (hy : 0 < y) (hBy : B ≤ 2 * y)
    (hA : ∀ a ∈ A, 0 < a) (hbound : ∀ a ∈ A, a ≤ B)
    (hBsq : B * B < y) (hsq : ∀ a ∈ A, Squarefree a)
    (hscale : ∀ a ∈ A, ∀ d ∈ a.divisors,
      N ≤ y / d ∧ y ≤ (y / d) ^ 2) :
    smallPrimeEulerDensity (2 * y) *
        (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
          (∑ a ∈ A, (a.divisors.card : ℝ) / a) ^ 2) ≤
      epsilon y (2 * y) *
        (∑ a ∈ A, (closePairCount a : ℝ) / a) := by
  have hsum := sum_eligiblePrimeMass_lower hN hprime hA hscale
  have hcrt := ford_moduli_lower hy hBy hA hbound hBsq hsq
  have heuler : 0 ≤ smallPrimeEulerDensity (2 * y) :=
    smallPrimeEulerDensity_nonneg _
  have hWsum : 0 ≤ ∑ a ∈ A, (closePairCount a : ℝ) / a := by
    apply Finset.sum_nonneg
    intro a ha
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    smallPrimeEulerDensity (2 * y) *
          (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
            (∑ a ∈ A, (a.divisors.card : ℝ) / a) ^ 2) ≤
        smallPrimeEulerDensity (2 * y) *
          ((∑ a ∈ A, (1 / (a : ℝ)) * eligiblePrimeMass y a) *
            (∑ a ∈ A, (closePairCount a : ℝ) / a)) :=
      mul_le_mul_of_nonneg_left hsum heuler
    _ = (smallPrimeEulerDensity (2 * y) *
          (∑ a ∈ A, (1 / (a : ℝ)) * eligiblePrimeMass y a)) *
        (∑ a ∈ A, (closePairCount a : ℝ) / a) := by ring
    _ ≤ epsilon y (2 * y) *
        (∑ a ∈ A, (closePairCount a : ℝ) / a) :=
      mul_le_mul_of_nonneg_right hcrt hWsum

end Erdos446
