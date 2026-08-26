/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.InternalSquareMass
import ErdosProblems.Erdos822.PredDivisibleMass

/-!
# Reciprocal mass of the internal shifted-prime channel
-/

namespace Erdos822

open scoped BigOperators

noncomputable def internalShiftedPrimeBadSmallFactors
    (N y : ℕ) : Finset ℕ := by
  classical
  exact (oddSmallFactors N).filter fun k =>
    ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ k ∧
      ∃ l ∈ k.primeFactors, p ∣ l - 1

theorem internalShiftedPrimeBadSmallFactors_subset_biUnion
    (N y : ℕ) :
    internalShiftedPrimeBadSmallFactors N y ⊆
      (internalSquarePrimes N y).biUnion fun p =>
        (predDivisibleUpTo N p).biUnion fun l =>
          (oddSmallFactors N).filter fun k => p * l ∣ k := by
  classical
  intro k hk
  rw [internalShiftedPrimeBadSmallFactors, Finset.mem_filter] at hk
  obtain ⟨p, hp, hyp, hpk, l, hlk, hpl⟩ := hk.2
  have hkpos := oddSmallFactors_pos hk.1
  have hple : p ≤ k := Nat.le_of_dvd hkpos hpk
  have hpN : p ≤ N := hple.trans (oddSmallFactors_le hk.1)
  have hpMem : p ∈ internalSquarePrimes N y := by
    rw [internalSquarePrimes, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hyp, hpN⟩, hp⟩
  have hlPrime := Nat.prime_of_mem_primeFactors hlk
  have hlDiv : l ∣ k := Nat.dvd_of_mem_primeFactors hlk
  have hlN : l ≤ N :=
    (Nat.le_of_dvd hkpos hlDiv).trans (oddSmallFactors_le hk.1)
  have hlMem : l ∈ predDivisibleUpTo N p := by
    rw [predDivisibleUpTo, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hlPrime.two_le, hlN⟩, hpl⟩
  have hplt : p < l := by
    have hlpred : 0 < l - 1 := Nat.sub_pos_of_lt hlPrime.one_lt
    have hple : p ≤ l - 1 := Nat.le_of_dvd hlpred hpl
    exact hple.trans_lt (Nat.sub_lt hlPrime.pos (by norm_num))
  have hmul : p * l ∣ k :=
    hp.dvd_mul_of_dvd_ne (ne_of_lt hplt) hlPrime hpk hlDiv
  rw [Finset.mem_biUnion]
  exact ⟨p, hpMem, Finset.mem_biUnion.mpr
    ⟨l, hlMem, Finset.mem_filter.mpr ⟨hk.1, hmul⟩⟩⟩

theorem sum_inv_internalShiftedPrimeBadSmallFactors_le
    {N y : ℕ} (hy : 1 ≤ y) :
    ∑ k ∈ internalShiftedPrimeBadSmallFactors N y, (1 : ℝ) / k ≤
      (harmonic N : ℝ) ^ 2 / y := by
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  calc
    (∑ k ∈ internalShiftedPrimeBadSmallFactors N y, (1 : ℝ) / k) ≤
        ∑ k ∈ (internalSquarePrimes N y).biUnion (fun p =>
          (predDivisibleUpTo N p).biUnion fun l =>
            (oddSmallFactors N).filter fun k => p * l ∣ k),
          (1 : ℝ) / k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (internalShiftedPrimeBadSmallFactors_subset_biUnion N y)
      intro k hk hnot
      positivity
    _ ≤ ∑ p ∈ internalSquarePrimes N y,
          ∑ l ∈ predDivisibleUpTo N p,
            ∑ k ∈ (oddSmallFactors N).filter (fun k => p * l ∣ k),
              (1 : ℝ) / k := by
      calc
        _ ≤ ∑ p ∈ internalSquarePrimes N y,
              ∑ k ∈ (predDivisibleUpTo N p).biUnion (fun l =>
                (oddSmallFactors N).filter fun k => p * l ∣ k),
                (1 : ℝ) / k := by
          apply sum_biUnion_le_sum
          intro p hp k hk
          positivity
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro p hp
          apply sum_biUnion_le_sum
          intro l hl k hk
          positivity
    _ ≤ ∑ p ∈ internalSquarePrimes N y,
          ∑ l ∈ predDivisibleUpTo N p,
            (harmonic N : ℝ) / (p * l : ℕ) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro l hl
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      have hlpos : 0 < l := by
        have hlData : 2 ≤ l ∧ l ≤ N ∧ p ∣ l - 1 := by
          simpa [predDivisibleUpTo, and_assoc] using hl
        omega
      calc
        (∑ k ∈ (oddSmallFactors N).filter (fun k => p * l ∣ k),
            (1 : ℝ) / k) ≤
            (harmonic (N / (p * l)) : ℝ) / (p * l : ℕ) :=
          sum_inv_oddSmallFactors_filter_dvd_le_harmonic_div
            (Nat.mul_pos hpPrime.pos hlpos)
        _ ≤ (harmonic N : ℝ) / (p * l : ℕ) := by
          apply div_le_div_of_nonneg_right
            (harmonic_cast_mono (Nat.div_le_self N (p * l)))
          positivity
    _ ≤ ∑ p ∈ internalSquarePrimes N y,
          ((harmonic N : ℝ) / p) * ((harmonic N : ℝ) / p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      calc
        (∑ l ∈ predDivisibleUpTo N p,
            (harmonic N : ℝ) / (p * l : ℕ)) =
            ((harmonic N : ℝ) / p) *
              (∑ l ∈ predDivisibleUpTo N p, (1 : ℝ) / l) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          push_cast
          ring
        _ ≤ ((harmonic N : ℝ) / p) * ((harmonic N : ℝ) / p) := by
          apply mul_le_mul_of_nonneg_left
            (sum_inv_predDivisibleUpTo_le hpPrime.pos)
          positivity
    _ = (harmonic N : ℝ) ^ 2 *
          (∑ p ∈ internalSquarePrimes N y,
            (1 : ℝ) / (p ^ 2 : ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      push_cast
      ring
    _ ≤ (harmonic N : ℝ) ^ 2 * ((1 : ℝ) / y) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply sum_inv_sq_le_inv_of_subset_Ioc (U := N) hy
      intro p hp
      exact (Finset.mem_filter.mp hp).1
    _ = (harmonic N : ℝ) ^ 2 / y := by ring

end Erdos822
