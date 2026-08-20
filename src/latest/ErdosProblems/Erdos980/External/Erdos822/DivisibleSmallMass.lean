/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.FixedPrimeFiber

/-!
# Reciprocal mass of divisible small factors

Positive multiples of p in [1,N] are exactly p*j with
1 <= j <= N/p.  This elementary reindexing supplies the inverse-p factor
for the exceptional small factors divisible by the fixed sieve prime.
-/

namespace Erdos822

open scoped BigOperators

/-- Positive multiples of p in [1,N], reindexed by their quotient. -/
theorem filter_Icc_dvd_eq_image_Icc_div
    {N p : ℕ} (hp : 0 < p) :
    (Finset.Icc 1 N).filter (fun k => p ∣ k) =
      (Finset.Icc 1 (N / p)).image (fun j => p * j) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hk1, hkN⟩, hpk⟩
    refine ⟨k / p, ?_, ?_⟩
    · constructor
      · have hpkle : p ≤ k := Nat.le_of_dvd (by omega) hpk
        exact Nat.div_pos hpkle hp
      · apply (Nat.le_div_iff_mul_le hp).2
        have hmul : p * (k / p) = k := Nat.mul_div_cancel' hpk
        simpa [Nat.mul_comm, hmul] using hkN
    · exact Nat.mul_div_cancel' hpk
  · rintro ⟨j, ⟨hj1, hjN⟩, rfl⟩
    constructor
    · constructor
      · exact Nat.mul_pos hp (by omega)
      · have hmul : j * p ≤ N :=
          (Nat.le_div_iff_mul_le hp).1 hjN
        simpa [Nat.mul_comm] using hmul
    · exact dvd_mul_right p j

/-- The reciprocal mass of positive multiples of p in [1,N] is the
harmonic mass up to N/p divided by p. -/
theorem sum_inv_filter_Icc_dvd_eq_harmonic_div
    {N p : ℕ} (hp : 0 < p) :
    ∑ k ∈ (Finset.Icc 1 N).filter (fun k => p ∣ k),
        (1 : ℝ) / k =
      (harmonic (N / p) : ℝ) / (p : ℝ) := by
  rw [filter_Icc_dvd_eq_image_Icc_div hp]
  rw [Finset.sum_image]
  · rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    ring
  · intro i hi j hj hij
    exact Nat.eq_of_mul_eq_mul_left hp hij

/-- Restricting to odd small factors can only reduce the divisible
reciprocal mass. -/
theorem sum_inv_oddSmallFactors_filter_dvd_le_harmonic_div
    {N p : ℕ} (hp : 0 < p) :
    ∑ k ∈ (oddSmallFactors N).filter (fun k => p ∣ k),
        (1 : ℝ) / k ≤
      (harmonic (N / p) : ℝ) / (p : ℝ) := by
  calc
    (∑ k ∈ (oddSmallFactors N).filter (fun k => p ∣ k),
        (1 : ℝ) / k) ≤
        ∑ k ∈ (Finset.Icc 1 N).filter (fun k => p ∣ k),
          (1 : ℝ) / k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        have hkdata := Finset.mem_filter.mp hk
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨oddSmallFactors_pos hkdata.1,
          oddSmallFactors_le hkdata.1⟩, hkdata.2⟩
      · intro k hk hnot
        positivity
    _ = (harmonic (N / p) : ℝ) / (p : ℝ) :=
      sum_inv_filter_Icc_dvd_eq_harmonic_div hp

end Erdos822
