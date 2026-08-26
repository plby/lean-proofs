/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.InternalTotientChannels
import ErdosProblems.Erdos822.DivisibleSmallMass
import ErdosProblems.Erdos822.ReciprocalSquareTail
import ErdosProblems.Erdos822.FinsetSumUnion

/-!
# Reciprocal mass of the internal square channel
-/

namespace Erdos822

open scoped BigOperators

def internalSquarePrimes (N y : ℕ) : Finset ℕ :=
  (Finset.Ioc y N).filter Nat.Prime

def internalSquareBadSmallFactors (N y : ℕ) : Finset ℕ :=
  (oddSmallFactors N).filter fun k =>
    ∃ p ∈ internalSquarePrimes N y, p ^ 2 ∣ k

theorem internalSquareBadSmallFactors_subset_biUnion
    (N y : ℕ) :
    internalSquareBadSmallFactors N y ⊆
      (internalSquarePrimes N y).biUnion fun p =>
        (oddSmallFactors N).filter fun k => p ^ 2 ∣ k := by
  intro k hk
  rw [internalSquareBadSmallFactors, Finset.mem_filter] at hk
  obtain ⟨p, hp, hpk⟩ := hk.2
  rw [Finset.mem_biUnion]
  exact ⟨p, hp, Finset.mem_filter.mpr ⟨hk.1, hpk⟩⟩

theorem sum_inv_internalSquareBadSmallFactors_le
    {N y : ℕ} (hy : 1 ≤ y) :
    ∑ k ∈ internalSquareBadSmallFactors N y, (1 : ℝ) / k ≤
      (harmonic N : ℝ) / y := by
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  calc
    (∑ k ∈ internalSquareBadSmallFactors N y, (1 : ℝ) / k) ≤
        ∑ k ∈ (internalSquarePrimes N y).biUnion (fun p =>
          (oddSmallFactors N).filter fun k => p ^ 2 ∣ k),
          (1 : ℝ) / k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (internalSquareBadSmallFactors_subset_biUnion N y)
      intro k hk hnot
      positivity
    _ ≤ ∑ p ∈ internalSquarePrimes N y,
          ∑ k ∈ (oddSmallFactors N).filter (fun k => p ^ 2 ∣ k),
            (1 : ℝ) / k := by
      apply sum_biUnion_le_sum
      intro p hp k hk
      positivity
    _ ≤ ∑ p ∈ internalSquarePrimes N y,
          (harmonic N : ℝ) / (p ^ 2 : ℕ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      calc
        (∑ k ∈ (oddSmallFactors N).filter (fun k => p ^ 2 ∣ k),
            (1 : ℝ) / k) ≤
            (harmonic (N / p ^ 2) : ℝ) / ((p ^ 2 : ℕ) : ℝ) :=
          sum_inv_oddSmallFactors_filter_dvd_le_harmonic_div
            (pow_pos hpPrime.pos 2)
        _ ≤ (harmonic N : ℝ) / (p ^ 2 : ℕ) := by
          apply div_le_div_of_nonneg_right
            (harmonic_cast_mono (Nat.div_le_self N (p ^ 2)))
          positivity
    _ = (harmonic N : ℝ) *
          (∑ p ∈ internalSquarePrimes N y,
            (1 : ℝ) / (p ^ 2 : ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (harmonic N : ℝ) * ((1 : ℝ) / y) := by
      apply mul_le_mul_of_nonneg_left _ hH
      apply sum_inv_sq_le_inv_of_subset_Ioc (U := N) hy
      intro p hp
      exact (Finset.mem_filter.mp hp).1
    _ = (harmonic N : ℝ) / y := by ring

end Erdos822
