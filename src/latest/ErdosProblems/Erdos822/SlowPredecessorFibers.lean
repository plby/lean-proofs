/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.MiddlePrimeResidueClasses
import ErdosProblems.Erdos822.LargePrimeFactorMass

/-!
# Slow-cutoff predecessor fibers

For a fixed small factor `k`, the conditions that a prime divisor `p > y`
of `k` also divide `r - 1` or `q - 1` put the corresponding structured
prime into the residue class `1 mod p`.  Taking the union over the prime
factors of `k` gives the finite reciprocal-mass bounds below.
-/

namespace Erdos822

open scoped BigOperators

noncomputable def slowSmallMiddlePredFiber (N y k : ℕ) : Finset ℕ := by
  classical
  exact (middlePrimes N).filter fun r =>
    ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ k ∧ p ∣ r - 1

noncomputable def slowSmallLargePredFiber (N y k : ℕ) : Finset ℕ := by
  classical
  exact (largePrimes N).filter fun q =>
    ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ k ∧ p ∣ q - 1

theorem slowSmallMiddlePredFiber_subset_primeFactorResidues
    {N y k : ℕ} (hk : 0 < k) :
    slowSmallMiddlePredFiber N y k ⊆
      (primeFactorsAbove k y).biUnion fun p =>
        middlePrimeResidueClass N p 1 := by
  classical
  intro r hr
  rw [slowSmallMiddlePredFiber] at hr
  obtain ⟨hrMiddle, p, hp, hyp, hpk, hpr⟩ := Finset.mem_filter.mp hr
  rw [Finset.mem_biUnion]
  refine ⟨p, ?_, ?_⟩
  · rw [mem_primeFactorsAbove_iff, Nat.mem_primeFactors]
    exact ⟨⟨hp, hpk, Nat.ne_of_gt hk⟩, hyp⟩
  · rw [mem_middlePrimeResidueClass_iff]
    refine ⟨hrMiddle, ?_⟩
    exact ((Nat.modEq_iff_dvd' (by
      exact (mem_middlePrimes_iff.mp hrMiddle).2.2.pos)).2 hpr).symm

theorem slowSmallLargePredFiber_subset_primeFactorResidues
    {N y k : ℕ} (hk : 0 < k) :
    slowSmallLargePredFiber N y k ⊆
      (primeFactorsAbove k y).biUnion fun p =>
        largePrimeResidueClass N p 1 0 := by
  classical
  intro q hq
  rw [slowSmallLargePredFiber] at hq
  obtain ⟨hqLarge, p, hp, hyp, hpk, hpq⟩ := Finset.mem_filter.mp hq
  rw [Finset.mem_biUnion]
  refine ⟨p, ?_, ?_⟩
  · rw [mem_primeFactorsAbove_iff, Nat.mem_primeFactors]
    exact ⟨⟨hp, hpk, Nat.ne_of_gt hk⟩, hyp⟩
  · rw [mem_largePrimeResidueClass_iff]
    refine ⟨hqLarge, (mem_largePrimes_iff.mp hqLarge).2.2.pos, ?_⟩
    exact ((Nat.modEq_iff_dvd' (by
      exact (mem_largePrimes_iff.mp hqLarge).2.2.pos)).2 hpq).symm

theorem sum_inv_slowSmallMiddlePredFiber_le_primeFactors
    {N y k : ℕ} (hN : 2 ≤ N) (hk : 0 < k) :
    ∑ r ∈ slowSmallMiddlePredFiber N y k, (1 : ℝ) / r ≤
      ((∑ p ∈ primeFactorsAbove k y, (1 : ℝ) / p) +
          ((primeFactorsAbove k y).card : ℝ) / (N ^ 4 : ℕ)) *
        (harmonic N : ℝ) := by
  classical
  calc
    (∑ r ∈ slowSmallMiddlePredFiber N y k, (1 : ℝ) / r) ≤
        ∑ r ∈ (primeFactorsAbove k y).biUnion (fun p =>
          middlePrimeResidueClass N p 1), (1 : ℝ) / r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (slowSmallMiddlePredFiber_subset_primeFactorResidues hk)
      intro r hr hnot
      positivity
    _ ≤ ∑ p ∈ primeFactorsAbove k y,
          ∑ r ∈ middlePrimeResidueClass N p 1, (1 : ℝ) / r := by
      apply sum_biUnion_le_sum
      intro p hp r hr
      positivity
    _ ≤ ∑ p ∈ primeFactorsAbove k y,
          (((1 : ℝ) / p + (1 : ℝ) / (N ^ 4 : ℕ)) *
            (harmonic N : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_inv_middlePrimeResidueClass_le_harmonic_of_pos hN
        (Nat.prime_of_mem_primeFactors
          (mem_primeFactorsAbove_iff.mp hp).1).pos
    _ = ((∑ p ∈ primeFactorsAbove k y, (1 : ℝ) / p) +
          ((primeFactorsAbove k y).card : ℝ) / (N ^ 4 : ℕ)) *
        (harmonic N : ℝ) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_const]
      simp only [one_div, Nat.cast_pow, nsmul_eq_mul]
      have hfactor :
          (∑ p ∈ primeFactorsAbove k y,
              (p : ℝ)⁻¹ * (harmonic N : ℝ)) =
            (∑ p ∈ primeFactorsAbove k y, (p : ℝ)⁻¹) *
              (harmonic N : ℝ) := by
        rw [Finset.sum_mul]
      rw [hfactor]
      ring

theorem sum_inv_slowSmallLargePredFiber_le_primeFactors
    {N y k : ℕ} (hN : 2 ≤ N) (hk : 0 < k) :
    ∑ q ∈ slowSmallLargePredFiber N y k, (1 : ℝ) / q ≤
      ((∑ p ∈ primeFactorsAbove k y, (1 : ℝ) / p) +
          ((primeFactorsAbove k y).card : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ) := by
  classical
  calc
    (∑ q ∈ slowSmallLargePredFiber N y k, (1 : ℝ) / q) ≤
        ∑ q ∈ (primeFactorsAbove k y).biUnion (fun p =>
          largePrimeResidueClass N p 1 0), (1 : ℝ) / q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (slowSmallLargePredFiber_subset_primeFactorResidues hk)
      intro q hq hnot
      positivity
    _ ≤ ∑ p ∈ primeFactorsAbove k y,
          ∑ q ∈ largePrimeResidueClass N p 1 0, (1 : ℝ) / q := by
      apply sum_biUnion_le_sum
      intro p hp q hq
      positivity
    _ ≤ ∑ p ∈ primeFactorsAbove k y,
          (((1 : ℝ) / p + (1 : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_inv_largePrimeResidueClass_le_harmonic_of_pos hN
        (Nat.prime_of_mem_primeFactors
          (mem_primeFactorsAbove_iff.mp hp).1).pos
    _ = ((∑ p ∈ primeFactorsAbove k y, (1 : ℝ) / p) +
          ((primeFactorsAbove k y).card : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_const]
      simp only [one_div, Nat.cast_pow, nsmul_eq_mul]
      have hfactor :
          (∑ p ∈ primeFactorsAbove k y,
              (p : ℝ)⁻¹ * (harmonic N : ℝ)) =
            (∑ p ∈ primeFactorsAbove k y, (p : ℝ)⁻¹) *
              (harmonic N : ℝ) := by
        rw [Finset.sum_mul]
      rw [hfactor]
      ring

theorem sum_inv_slowSmallMiddlePredFiber_le_log
    {N y k : ℕ} (hN : 2 ≤ N) (hk : 0 < k) (hy : 1 ≤ y) :
    ∑ r ∈ slowSmallMiddlePredFiber N y k, (1 : ℝ) / r ≤
      (((Nat.log 2 k : ℝ) / y) +
          (Nat.log 2 k : ℝ) / (N ^ 4 : ℕ)) *
        (harmonic N : ℝ) := by
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  refine (sum_inv_slowSmallMiddlePredFiber_le_primeFactors hN hk).trans ?_
  apply mul_le_mul_of_nonneg_right _ hH
  apply add_le_add
  · exact sum_inv_primeFactorsAbove_le_log_div hk hy
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast card_primeFactorsAbove_le_log hk

theorem sum_inv_slowSmallLargePredFiber_le_log
    {N y k : ℕ} (hN : 2 ≤ N) (hk : 0 < k) (hy : 1 ≤ y) :
    ∑ q ∈ slowSmallLargePredFiber N y k, (1 : ℝ) / q ≤
      (((Nat.log 2 k : ℝ) / y) +
          (Nat.log 2 k : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ) := by
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  refine (sum_inv_slowSmallLargePredFiber_le_primeFactors hN hk).trans ?_
  apply mul_le_mul_of_nonneg_right _ hH
  apply add_le_add
  · exact sum_inv_primeFactorsAbove_le_log_div hk hy
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast card_primeFactorsAbove_le_log hk

end Erdos822
