/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SlowInternalTotientMass

/-!
# Reciprocal mass assembly for the slow-cutoff B4 deletion
-/

namespace Erdos822

open scoped BigOperators

/-- The fourth channel is exactly a concrete `N^4`-cutoff B4 failure.
Together with the previously proved reverse inclusion, this identifies the
exceptional family used in the old concrete-cutoff estimate. -/
theorem middlePredLargeCofactors_subset_largeCutoffBad
    {N : ℕ} (hN : 2 ≤ N) :
    middlePredLargeCofactors N ⊆ largeCutoffBadOddCofactors N := by
  intro m hm
  rw [mem_middlePredLargeCofactors_iff] at hm
  obtain ⟨k, r, q, ht, hrq, hprod⟩ := hm
  rw [mem_largeCutoffBadOddCofactors_iff]
  refine ⟨?_, r, ?_, ?_, ?_, ?_⟩
  · rw [oddRawCofactors, Finset.mem_image]
    exact ⟨(k, r, q), ht, by simpa [cofactorProduct] using hprod.symm⟩
  · exact (mem_middlePrimes_iff.mp
      (mem_oddCofactorTriples_iff.mp ht).2.1).2.2
  · have hrData := mem_middlePrimes_iff.mp
      (mem_oddCofactorTriples_iff.mp ht).2.1
    have hne : r ≠ N ^ 4 := by
      intro heq
      rw [heq] at hrData
      exact (Nat.Prime.not_prime_pow (by omega : 2 ≤ 4)) hrData.2.2
    omega
  · rw [hprod]
    exact dvd_mul_of_dvd_left (dvd_mul_left r k) q
  · have hqMem := (mem_oddCofactorTriples_iff.mp ht).2.2
    have hqPrime := (mem_largePrimes_iff.mp hqMem).2.2
    have hqdiv : q ∣ m := by
      rw [hprod]
      exact dvd_mul_left q (k * r)
    have htot := Nat.totient_dvd_of_dvd hqdiv
    rw [Nat.totient_prime hqPrime] at htot
    exact hrq.trans htot

theorem sum_inv_middlePredLargeCofactors_le
    {N : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ middlePredLargeCofactors N, (1 : ℝ) / m ≤
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (((1 : ℝ) / (N ^ 4 : ℕ)) * (harmonic N : ℝ) +
          ((1 : ℝ) / (N ^ 21 : ℕ)) *
            (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
              (harmonic N : ℝ)) := by
  calc
    (∑ m ∈ middlePredLargeCofactors N, (1 : ℝ) / m) ≤
        ∑ m ∈ largeCutoffBadOddCofactors N, (1 : ℝ) / m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (middlePredLargeCofactors_subset_largeCutoffBad hN)
      intro m hm hnot
      positivity
    _ ≤ _ := sum_inv_largeCutoffBadOddCofactors_le hN

/-- The reciprocal mass of the slow-cutoff bad family is at most the sum
of the four explicit channel masses. -/
theorem sum_inv_slowCutoffBadOddCofactors_le_four_channels
    {N y : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ slowCutoffBadOddCofactors N y, (1 : ℝ) / m ≤
      (∑ m ∈ slowInternalTotientCofactors N y, (1 : ℝ) / m) +
        (∑ m ∈ slowSmallMiddlePredCofactors N y, (1 : ℝ) / m) +
          (∑ m ∈ slowSmallLargePredCofactors N y, (1 : ℝ) / m) +
            (∑ m ∈ middlePredLargeCofactors N, (1 : ℝ) / m) := by
  calc
    (∑ m ∈ slowCutoffBadOddCofactors N y, (1 : ℝ) / m) ≤
        ∑ m ∈ slowInternalTotientCofactors N y ∪
          (slowSmallMiddlePredCofactors N y ∪
            (slowSmallLargePredCofactors N y ∪
              middlePredLargeCofactors N)), (1 : ℝ) / m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (slowCutoffBadOddCofactors_subset_four_channels hN)
      intro m hm hnot
      positivity
    _ ≤ (∑ m ∈ slowInternalTotientCofactors N y, (1 : ℝ) / m) +
          ((∑ m ∈ slowSmallMiddlePredCofactors N y, (1 : ℝ) / m) +
            ((∑ m ∈ slowSmallLargePredCofactors N y, (1 : ℝ) / m) +
              (∑ m ∈ middlePredLargeCofactors N, (1 : ℝ) / m))) := by
      refine (sum_union_le_add_sum (fun m hm => by positivity)).trans ?_
      gcongr
      refine (sum_union_le_add_sum (fun m hm => by positivity)).trans ?_
      gcongr
      exact sum_union_le_add_sum (fun m hm => by positivity)
    _ = _ := by ring

end Erdos822
