/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SlowCutoffLog
import ErdosProblems.Erdos822.ShiftedMassFirstMoment
import Mathlib.Analysis.PSeries

/-!
# A uniform square-reciprocal prime bound

The finite p-series telescoping bound gives a convenient absolute bound for
the square-reciprocal mass of every sieve-prime interval.
-/

namespace Erdos822

open scoped BigOperators

/-- The square-reciprocal mass of primes in any sieve interval is at most
one. -/
theorem sum_inv_sq_sievePrimes_le_one
    {z y : ℕ} (hy : 1 ≤ y) :
    ∑ p ∈ Erdos851.sievePrimes z y,
        (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
  simp only [one_div]
  calc
    (∑ p ∈ Erdos851.sievePrimes z y,
        ((p : ℝ) ^ 2)⁻¹) ≤
        ∑ n ∈ Finset.Ioc 1 y,
          (((n : ℝ) ^ 2)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Erdos851.mem_sievePrimes] at hp
        rw [Finset.mem_Ioc]
        exact ⟨hp.2.2.one_lt, hp.2.1⟩
      · intro n hn hnot
        positivity
    _ ≤ ((1 : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
      simpa using
        (sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := y)
          (by norm_num) hy)
    _ ≤ 1 := by
      have : 0 ≤ (y : ℝ)⁻¹ := by positivity
      norm_num

/-- A logarithmic fixed-prime incidence estimate gives a logarithmic B5
first moment after the finite Fubini identity and the square-prime bound. -/
theorem shiftedMassFirstMoment_le_log_of_incidence
    (N z y : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hlogN : 0 ≤ Real.log (N : ℝ)) (hy : 1 ≤ y)
    (hinc : ∀ p ∈ Erdos851.sievePrimes z y,
      ∑ m ∈ shiftedDivisibleOddCofactors N p,
        (1 : ℝ) / m ≤ (D * Real.log (N : ℝ)) / p) :
    shiftedMassFirstMoment N z y ≤
      D * Real.log (N : ℝ) := by
  have hfirst :=
    shiftedMassFirstMoment_le_of_incidence N z y
      (D := D * Real.log (N : ℝ)) hinc
  have hsquare :
      ∑ p ∈ Erdos851.sievePrimes z y,
          (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 :=
    sum_inv_sq_sievePrimes_le_one hy
  calc
    shiftedMassFirstMoment N z y ≤
        (D * Real.log (N : ℝ)) *
          ∑ p ∈ Erdos851.sievePrimes z y,
            (1 : ℝ) / (p : ℝ) ^ 2 := hfirst
    _ ≤ (D * Real.log (N : ℝ)) * 1 := by
      exact mul_le_mul_of_nonneg_left hsquare
        (mul_nonneg hD hlogN)
    _ = D * Real.log (N : ℝ) := by ring

/-- The same Fubini argument with the harmless factor 1 + log N. -/
theorem shiftedMassFirstMoment_le_one_add_log_of_incidence
    (N z y : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hL : 0 ≤ 1 + Real.log (N : ℝ)) (hy : 1 ≤ y)
    (hinc : ∀ p ∈ Erdos851.sievePrimes z y,
      ∑ m ∈ shiftedDivisibleOddCofactors N p,
        (1 : ℝ) / m ≤
          (D * (1 + Real.log (N : ℝ))) / p) :
    shiftedMassFirstMoment N z y ≤
      D * (1 + Real.log (N : ℝ)) := by
  have hfirst :=
    shiftedMassFirstMoment_le_of_incidence N z y
      (D := D * (1 + Real.log (N : ℝ))) hinc
  have hsquare :
      ∑ p ∈ Erdos851.sievePrimes z y,
          (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 :=
    sum_inv_sq_sievePrimes_le_one hy
  calc
    shiftedMassFirstMoment N z y ≤
        (D * (1 + Real.log (N : ℝ))) *
          ∑ p ∈ Erdos851.sievePrimes z y,
            (1 : ℝ) / (p : ℝ) ^ 2 := hfirst
    _ ≤ (D * (1 + Real.log (N : ℝ))) * 1 := by
      exact mul_le_mul_of_nonneg_left hsquare
        (mul_nonneg hD hL)
    _ = D * (1 + Real.log (N : ℝ)) := by ring

end Erdos822
