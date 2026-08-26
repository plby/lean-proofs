/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CommonDivisorRanges

/-!
# Crude cardinality bounds for cofactor pairs

The unit part of the gcd kernel needs no arithmetic averaging.  Every odd
raw cofactor lies in the interval [1,N^28], so there are at most N^28 of
them and at most N^56 ordered pairs.
-/

namespace Erdos822

open scoped BigOperators

theorem oddRawCofactors_subset_Icc_pow_twenty_eight
    (N : ℕ) :
    oddRawCofactors N ⊆ Finset.Icc 1 (N ^ 28) := by
  intro m hm
  rw [Finset.mem_Icc]
  exact ⟨oddRawCofactors_pos hm, oddRawCofactors_le_pow_twenty_eight hm⟩

theorem oddRawCofactors_card_le_pow_twenty_eight
    (N : ℕ) :
    (oddRawCofactors N).card ≤ N ^ 28 := by
  calc
    (oddRawCofactors N).card ≤ (Finset.Icc 1 (N ^ 28)).card :=
      Finset.card_le_card (oddRawCofactors_subset_Icc_pow_twenty_eight N)
    _ = N ^ 28 := by
      simp

theorem card_le_pow_twenty_eight_of_subset_oddRaw
    {N : ℕ} {B : Finset ℕ} (hB : B ⊆ oddRawCofactors N) :
    B.card ≤ N ^ 28 :=
  (Finset.card_le_card hB).trans
    (oddRawCofactors_card_le_pow_twenty_eight N)

/-- The number of ordered off-diagonal cofactor pairs in any odd-raw
subfamily is at most N^56. -/
theorem sum_card_erase_le_pow_fifty_six_of_subset_oddRaw
    {N : ℕ} {B : Finset ℕ} (hB : B ⊆ oddRawCofactors N) :
    ∑ m ∈ B, (B.erase m).card ≤ N ^ 56 := by
  have hcard : B.card ≤ N ^ 28 :=
    card_le_pow_twenty_eight_of_subset_oddRaw hB
  calc
    ∑ m ∈ B, (B.erase m).card ≤
        ∑ m ∈ B, B.card := by
      apply Finset.sum_le_sum
      intro m hm
      exact Finset.card_erase_le
    _ = B.card * B.card := by simp
    _ ≤ N ^ 28 * N ^ 28 := Nat.mul_le_mul hcard hcard
    _ = N ^ 56 := by ring

/-- Real-valued constant sums over off-diagonal pairs are controlled by
the same N^56 count. -/
theorem sum_const_offDiagonal_le_pow_fifty_six_of_subset_oddRaw
    {N : ℕ} {B : Finset ℕ} {C : ℝ}
    (hB : B ⊆ oddRawCofactors N) (hC : 0 ≤ C) :
    (∑ m ∈ B, ∑ m' ∈ B.erase m, C) ≤
      C * ((N ^ 56 : ℕ) : ℝ) := by
  have hcount := sum_card_erase_le_pow_fifty_six_of_subset_oddRaw hB
  calc
    (∑ m ∈ B, ∑ m' ∈ B.erase m, C) =
        C * ((∑ m ∈ B, (B.erase m).card : ℕ) : ℝ) := by
      simp_rw [Finset.sum_const, nsmul_eq_mul]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ C * ((N ^ 56 : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact_mod_cast hcount

end Erdos822
