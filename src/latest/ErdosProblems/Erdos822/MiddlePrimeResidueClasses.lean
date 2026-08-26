/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.IntegerResidueBlocks
import ErdosProblems.Erdos822.FinsetSumUnion

/-!
# Elementary residue classes in the middle-prime layer

The rough quadratic congruence constrains both structured primes.  The large
prime side already has an arbitrary-modulus reciprocal estimate.  This file
records the identical elementary estimate for the middle interval
`(N^4,N^5]`.
-/

namespace Erdos822

open scoped BigOperators

/-- Middle-layer primes in one residue class modulo an arbitrary positive
modulus. -/
def middlePrimeResidueClass (N d a : ℕ) : Finset ℕ :=
  (middlePrimes N).filter fun r => r % d = a % d

@[simp]
theorem mem_middlePrimeResidueClass_iff
    {N d a r : ℕ} :
    r ∈ middlePrimeResidueClass N d a ↔
      r ∈ middlePrimes N ∧ r % d = a % d := by
  simp [middlePrimeResidueClass]

/-- Every middle prime in one residue class lies in one of the N adjacent
blocks of length N^4. -/
theorem middlePrimeResidueClass_subset_integer_blocks
    {N d a : ℕ} (hN : 2 ≤ N) :
    middlePrimeResidueClass N d a ⊆
      (Finset.Icc 1 N).biUnion fun j =>
        integerResidueInterval d a (j * N ^ 4) ((j + 1) * N ^ 4) := by
  intro r hr
  rw [mem_middlePrimeResidueClass_iff] at hr
  have hrData := mem_middlePrimes_iff.mp hr.1
  have hLpos : 0 < N ^ 4 := by positivity
  have hrgt : N ^ 4 < r := by
    have hne : r ≠ N ^ 4 := by
      intro heq
      rw [heq] at hrData
      exact (Nat.Prime.not_prime_pow (by omega : 2 ≤ 4)) hrData.2.2
    omega
  let j := (r - 1) / (N ^ 4)
  have hjpos : 0 < j := by
    dsimp [j]
    apply Nat.div_pos
    · omega
    · exact hLpos
  have hjle : j ≤ N := by
    dsimp [j]
    apply (Nat.div_le_iff_le_mul hLpos).2
    have hrle : r ≤ N * N ^ 4 := by
      simpa [show N * N ^ 4 = N ^ 5 by ring] using hrData.2.1
    omega
  have hleft : j * N ^ 4 < r := by
    have hmul := Nat.div_mul_le_self (r - 1) (N ^ 4)
    dsimp [j]
    omega
  have hright : r ≤ (j + 1) * N ^ 4 := by
    have hlt : (r - 1) / (N ^ 4) < (r - 1) / (N ^ 4) + 1 := by
      omega
    have hmul :
        r - 1 < ((r - 1) / (N ^ 4) + 1) * N ^ 4 :=
      (Nat.div_lt_iff_lt_mul hLpos).1 hlt
    dsimp [j]
    omega
  rw [Finset.mem_biUnion]
  refine ⟨j, Finset.mem_Icc.mpr ⟨by omega, hjle⟩, ?_⟩
  rw [mem_integerResidueInterval_iff]
  exact ⟨hleft, hright, hr.2⟩

/-- The reciprocal mass of one middle-prime residue class is bounded by
the corresponding integer residue blocks. -/
theorem sum_inv_middlePrimeResidueClass_le_integer_blocks
    {N d a : ℕ} (hN : 2 ≤ N) :
    ∑ r ∈ middlePrimeResidueClass N d a, (1 : ℝ) / r ≤
      ∑ j ∈ Finset.Icc 1 N,
        ∑ r ∈ integerResidueInterval d a
          (j * N ^ 4) ((j + 1) * N ^ 4), (1 : ℝ) / r := by
  calc
    (∑ r ∈ middlePrimeResidueClass N d a, (1 : ℝ) / r) ≤
        ∑ r ∈ (Finset.Icc 1 N).biUnion (fun j =>
          integerResidueInterval d a
            (j * N ^ 4) ((j + 1) * N ^ 4)),
          (1 : ℝ) / r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (middlePrimeResidueClass_subset_integer_blocks hN)
      intro r hr hnot
      positivity
    _ ≤ ∑ j ∈ Finset.Icc 1 N,
          ∑ r ∈ integerResidueInterval d a
            (j * N ^ 4) ((j + 1) * N ^ 4),
            (1 : ℝ) / r := by
      apply sum_biUnion_le_sum
      intro j hj r hr
      positivity

/-- One middle integer residue block has the cardinality-over-endpoint
bound. -/
theorem sum_inv_middle_integerResidueBlock_le
    {N d a j : ℕ} (hd : 0 < d) :
    ∑ r ∈ integerResidueInterval d a
        (j * N ^ 4) ((j + 1) * N ^ 4), (1 : ℝ) / r ≤
      (((N ^ 4 / d + 1 : ℕ) : ℝ) /
        (j * N ^ 4 + 1)) := by
  have hwidth :
      (j + 1) * N ^ 4 - j * N ^ 4 = N ^ 4 := by
    rw [show (j + 1) * N ^ 4 = j * N ^ 4 + N ^ 4 by ring]
    exact Nat.add_sub_cancel_left _ _
  calc
    (∑ r ∈ integerResidueInterval d a
        (j * N ^ 4) ((j + 1) * N ^ 4), (1 : ℝ) / r) ≤
        ((integerResidueInterval d a
          (j * N ^ 4) ((j + 1) * N ^ 4)).card : ℝ) /
          (j * N ^ 4 + 1) := by
      convert sum_inv_integerResidueInterval_le_card_div d a
        (j * N ^ 4) ((j + 1) * N ^ 4) using 1 <;>
        push_cast <;> rfl
    _ ≤ (((N ^ 4 / d + 1 : ℕ) : ℝ) /
        (j * N ^ 4 + 1)) := by
      apply div_le_div_of_nonneg_right
      · have hcard := card_integerResidueInterval_le
            (a := a) (L := j * N ^ 4)
            (U := (j + 1) * N ^ 4) hd
        rw [hwidth] at hcard
        exact_mod_cast hcard
      · positivity

/-- A single middle-prime residue class has the expected
`(1/d+1/N^4)` harmonic reciprocal bound. -/
theorem sum_inv_middlePrimeResidueClass_le_harmonic_of_pos
    {N d a : ℕ} (hN : 2 ≤ N) (hd : 0 < d) :
    ∑ r ∈ middlePrimeResidueClass N d a, (1 : ℝ) / r ≤
      ((1 : ℝ) / d + (1 : ℝ) / (N ^ 4 : ℕ)) *
        (harmonic N : ℝ) := by
  have hL : 0 < N ^ 4 := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLR : (0 : ℝ) < (N ^ 4 : ℕ) := by exact_mod_cast hL
  calc
    (∑ r ∈ middlePrimeResidueClass N d a, (1 : ℝ) / r) ≤
        ∑ j ∈ Finset.Icc 1 N,
          ∑ r ∈ integerResidueInterval d a
            (j * N ^ 4) ((j + 1) * N ^ 4), (1 : ℝ) / r :=
      sum_inv_middlePrimeResidueClass_le_integer_blocks hN
    _ ≤ ∑ j ∈ Finset.Icc 1 N,
          (((N ^ 4 / d + 1 : ℕ) : ℝ) /
            (j * N ^ 4 + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact sum_inv_middle_integerResidueBlock_le hd
    _ ≤ ∑ j ∈ Finset.Icc 1 N,
          (((1 : ℝ) / d + (1 : ℝ) / (N ^ 4 : ℕ)) *
            ((1 : ℝ) / j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjR : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
      have hcast :
          ((N ^ 4 / d + 1 : ℕ) : ℝ) ≤
            ((N ^ 4 : ℕ) : ℝ) / d + 1 := by
        have hdiv :
            ((N ^ 4 / d : ℕ) : ℝ) ≤
              ((N ^ 4 : ℕ) : ℝ) / d :=
          Nat.cast_div_le (α := ℝ) (m := N ^ 4) (n := d)
        push_cast at hdiv ⊢
        linarith
      have hden :
          (j : ℝ) * (N ^ 4 : ℕ) ≤
            ((j * N ^ 4 + 1 : ℕ) : ℝ) := by
        push_cast
        nlinarith
      have hnum0 :
          0 ≤ ((N ^ 4 : ℕ) : ℝ) / d + 1 := by positivity
      calc
        (((N ^ 4 / d + 1 : ℕ) : ℝ) /
            (j * N ^ 4 + 1)) ≤
            (((N ^ 4 : ℕ) : ℝ) / d + 1) /
              (j * N ^ 4 + 1) := by
          exact div_le_div_of_nonneg_right hcast (by positivity)
        _ ≤ (((N ^ 4 : ℕ) : ℝ) / d + 1) /
              ((j : ℝ) * (N ^ 4 : ℕ)) := by
          exact div_le_div_of_nonneg_left hnum0
            (mul_pos hjR hLR) (by
              simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
                Nat.cast_pow] using hden)
        _ = ((1 : ℝ) / d + (1 : ℝ) / (N ^ 4 : ℕ)) *
              ((1 : ℝ) / j) := by
          field_simp
    _ = ((1 : ℝ) / d + (1 : ℝ) / (N ^ 4 : ℕ)) *
        (harmonic N : ℝ) := by
      rw [← Finset.mul_sum]
      simp [harmonic_eq_sum_Icc, one_div]

end Erdos822
