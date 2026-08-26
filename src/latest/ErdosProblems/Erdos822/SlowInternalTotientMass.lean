/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.InternalShiftedPrimeMass
import ErdosProblems.Erdos822.SlowPredecessorChannelMass

/-!
# Reciprocal mass of the internal slow-B4 channel
-/

namespace Erdos822

open scoped BigOperators

noncomputable def internalTotientBadSmallFactors
    (N y : ℕ) : Finset ℕ := by
  classical
  exact (oddSmallFactors N).filter fun k =>
    ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ k ∧ p ∣ Nat.totient k

theorem internalTotientBadSmallFactors_subset
    (N y : ℕ) :
    internalTotientBadSmallFactors N y ⊆
      internalSquareBadSmallFactors N y ∪
        internalShiftedPrimeBadSmallFactors N y := by
  classical
  intro k hk
  rw [internalTotientBadSmallFactors, Finset.mem_filter] at hk
  obtain ⟨p, hp, hyp, hpk, hpφ⟩ := hk.2
  rcases prime_sq_dvd_or_dvd_primeFactor_pred_of_dvd_totient
      hp hpk hpφ with hsq | hshift
  · apply Finset.mem_union_left
    rw [internalSquareBadSmallFactors, Finset.mem_filter]
    refine ⟨hk.1, p, ?_, hsq⟩
    rw [internalSquarePrimes, Finset.mem_filter, Finset.mem_Ioc]
    have hpN : p ≤ N :=
      (Nat.le_of_dvd (oddSmallFactors_pos hk.1) hpk).trans
        (oddSmallFactors_le hk.1)
    exact ⟨⟨hyp, hpN⟩, hp⟩
  · apply Finset.mem_union_right
    rw [internalShiftedPrimeBadSmallFactors, Finset.mem_filter]
    exact ⟨hk.1, p, hp, hyp, hpk, hshift⟩

theorem sum_inv_internalTotientBadSmallFactors_le
    {N y : ℕ} (hy : 1 ≤ y) :
    ∑ k ∈ internalTotientBadSmallFactors N y, (1 : ℝ) / k ≤
      (harmonic N : ℝ) / y + (harmonic N : ℝ) ^ 2 / y := by
  calc
    (∑ k ∈ internalTotientBadSmallFactors N y, (1 : ℝ) / k) ≤
        ∑ k ∈ internalSquareBadSmallFactors N y ∪
          internalShiftedPrimeBadSmallFactors N y, (1 : ℝ) / k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (internalTotientBadSmallFactors_subset N y)
      intro k hk hnot
      positivity
    _ ≤ (∑ k ∈ internalSquareBadSmallFactors N y, (1 : ℝ) / k) +
          ∑ k ∈ internalShiftedPrimeBadSmallFactors N y, (1 : ℝ) / k := by
      apply sum_union_le_add_sum
      intro k hk
      positivity
    _ ≤ (harmonic N : ℝ) / y + (harmonic N : ℝ) ^ 2 / y :=
      add_le_add (sum_inv_internalSquareBadSmallFactors_le hy)
        (sum_inv_internalShiftedPrimeBadSmallFactors_le hy)

theorem sum_inv_slowInternalTotientCofactors_eq
    {N y : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ slowInternalTotientCofactors N y, (1 : ℝ) / m =
      ∑ k ∈ internalTotientBadSmallFactors N y,
        ∑ r ∈ middlePrimes N,
          ∑ q ∈ largePrimes N, (1 : ℝ) / (k * r * q) := by
  classical
  unfold slowInternalTotientCofactors
  rw [Finset.sum_image
    ((cofactorProduct_injOn_oddCofactorTriples hN).mono
      (Finset.filter_subset _ _))]
  rw [oddCofactorTriples]
  change
    (∑ t ∈ (oddSmallFactors N ×ˢ (middlePrimes N ×ˢ largePrimes N)).filter
        (fun t => ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ t.1 ∧
          p ∣ Nat.totient t.1),
      (1 : ℝ) / cofactorProduct t) = _
  rw [Finset.sum_filter, Finset.sum_product]
  simp_rw [Finset.sum_product]
  rw [internalTotientBadSmallFactors, Finset.sum_filter]
  simp [cofactorProduct]

theorem sum_inv_slowInternalTotientCofactors_le
    {N y : ℕ} (hN : 2 ≤ N) (hy : 1 ≤ y) :
    ∑ m ∈ slowInternalTotientCofactors N y, (1 : ℝ) / m ≤
      ((harmonic N : ℝ) / y + (harmonic N : ℝ) ^ 2 / y) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
  rw [sum_inv_slowInternalTotientCofactors_eq hN]
  calc
    (∑ k ∈ internalTotientBadSmallFactors N y,
        ∑ r ∈ middlePrimes N,
          ∑ q ∈ largePrimes N, (1 : ℝ) / (k * r * q)) =
        ∑ k ∈ internalTotientBadSmallFactors N y,
          (((1 : ℝ) / k) *
            (∑ r ∈ middlePrimes N, (1 : ℝ) / r)) *
              (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ r ∈ middlePrimes N,
            ∑ q ∈ largePrimes N, (1 : ℝ) / (k * r * q)) =
            ∑ r ∈ middlePrimes N,
              (((1 : ℝ) / k) * ((1 : ℝ) / r)) *
                (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          push_cast
          ring
        _ = (((1 : ℝ) / k) *
              (∑ r ∈ middlePrimes N, (1 : ℝ) / r)) *
                (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ =
        (∑ k ∈ internalTotientBadSmallFactors N y, (1 : ℝ) / k) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
            (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ ((harmonic N : ℝ) / y + (harmonic N : ℝ) ^ 2 / y) *
          (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
            (∑ q ∈ largePrimes N, (1 : ℝ) / q) := by
      gcongr
      exact sum_inv_internalTotientBadSmallFactors_le hy

end Erdos822
