/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.PrimeResidueIntervals

/-!
# Additive blocks for the large prime layer

The large prime interval from N^21 to N^22 is split into N adjacent
blocks of length N^21.  This is the elementary finite partition used to
sum the reciprocal prime-progression estimate with a harmonic weight.
-/

namespace Erdos822

open scoped BigOperators

/-- Large-layer primes in one residue class modulo p. -/
def largePrimeResidueClass (N p a y : ℕ) : Finset ℕ :=
  (largePrimes N).filter fun q => y < q ∧ q % p = a % p

/-- The j-th additive block of a large-layer residue class. -/
def largePrimeResidueBlock (N p a y j : ℕ) : Finset ℕ :=
  primeResidueInterval p a (j * N ^ 21) ((j + 1) * N ^ 21) y

@[simp]
theorem mem_largePrimeResidueClass_iff
    {N p a y q : ℕ} :
    q ∈ largePrimeResidueClass N p a y ↔
      q ∈ largePrimes N ∧ y < q ∧ q % p = a % p := by
  simp [largePrimeResidueClass]

@[simp]
theorem mem_largePrimeResidueBlock_iff
    {N p a y j q : ℕ} :
    q ∈ largePrimeResidueBlock N p a y j ↔
      j * N ^ 21 < q ∧ q ≤ (j + 1) * N ^ 21 ∧
        q.Prime ∧ y < q ∧ q % p = a % p := by
  simp [largePrimeResidueBlock]

/-- Every large prime in a fixed residue class lies in one of the adjacent
positive-index blocks. -/
theorem largePrimeResidueClass_subset_biUnion_blocks
    {N p a y : ℕ} (hN : 2 ≤ N) :
    largePrimeResidueClass N p a y ⊆
      (Finset.Icc 1 N).biUnion fun j =>
        largePrimeResidueBlock N p a y j := by
  intro q hq
  rw [mem_largePrimeResidueClass_iff] at hq
  have hqLarge := mem_largePrimes_iff.mp hq.1
  have hLpos : 0 < N ^ 21 := by positivity
  have hqgt : N ^ 21 < q := by
    have hne : q ≠ N ^ 21 := by
      intro heq
      rw [heq] at hqLarge
      exact (Nat.Prime.not_prime_pow (by omega : 2 ≤ 21)) hqLarge.2.2
    omega
  let j := (q - 1) / (N ^ 21)
  have hjpos : 0 < j := by
    dsimp [j]
    apply Nat.div_pos
    · omega
    · exact hLpos
  have hjle : j ≤ N := by
    dsimp [j]
    apply (Nat.div_le_iff_le_mul hLpos).2
    have hqle : q ≤ N * N ^ 21 := by
      simpa [show N * N ^ 21 = N ^ 22 by ring] using hqLarge.2.1
    omega
  have hleft : j * N ^ 21 < q := by
    have hmul := Nat.div_mul_le_self (q - 1) (N ^ 21)
    dsimp [j]
    omega
  have hright : q ≤ (j + 1) * N ^ 21 := by
    have hlt : (q - 1) / (N ^ 21) < (q - 1) / (N ^ 21) + 1 := by
      omega
    have hmul :
        q - 1 < ((q - 1) / (N ^ 21) + 1) * N ^ 21 :=
      (Nat.div_lt_iff_lt_mul hLpos).1 hlt
    dsimp [j]
    omega
  rw [Finset.mem_biUnion]
  refine ⟨j, Finset.mem_Icc.mpr ⟨by omega, hjle⟩, ?_⟩
  rw [mem_largePrimeResidueBlock_iff]
  exact ⟨hleft, hright, hqLarge.2.2, hq.2.1, hq.2.2⟩

/-- Distinct additive blocks are disjoint. -/
theorem largePrimeResidueBlocks_pairwiseDisjoint
    (N p a y : ℕ) :
    ((↑(Finset.Icc 1 N) : Set ℕ)).PairwiseDisjoint
      (largePrimeResidueBlock N p a y) := by
  intro i hi j hj hij
  change Disjoint (largePrimeResidueBlock N p a y i)
    (largePrimeResidueBlock N p a y j)
  rw [Finset.disjoint_left]
  intro q hqi hqj
  rw [mem_largePrimeResidueBlock_iff] at hqi hqj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hmul : (i + 1) * N ^ 21 ≤ j * N ^ 21 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have hmul : (j + 1) * N ^ 21 ≤ i * N ^ 21 :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- Consequently the reciprocal mass of a large residue class is at most
the sum of the reciprocal masses of its additive blocks. -/
theorem sum_inv_largePrimeResidueClass_le_sum_blocks
    {N p a y : ℕ} (hN : 2 ≤ N) :
    ∑ q ∈ largePrimeResidueClass N p a y, (1 : ℝ) / q ≤
      ∑ j ∈ Finset.Icc 1 N,
        ∑ q ∈ largePrimeResidueBlock N p a y j, (1 : ℝ) / q := by
  let U := (Finset.Icc 1 N).biUnion fun j =>
    largePrimeResidueBlock N p a y j
  calc
    (∑ q ∈ largePrimeResidueClass N p a y, (1 : ℝ) / q) ≤
        ∑ q ∈ U, (1 : ℝ) / q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (largePrimeResidueClass_subset_biUnion_blocks hN)
      intro q hq hnot
      positivity
    _ = ∑ j ∈ Finset.Icc 1 N,
          ∑ q ∈ largePrimeResidueBlock N p a y j,
            (1 : ℝ) / q := by
      dsimp [U]
      rw [Finset.sum_biUnion
        (largePrimeResidueBlocks_pairwiseDisjoint N p a y)]

/-- Summing the one-interval beta-sieve estimate over the additive blocks
gives an explicit reciprocal bound for a large-prime residue class. -/
theorem exists_sum_inv_largePrimeResidueClass_block_upper_bound :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ N p a y S : ℕ,
        2 ≤ N → p.Prime → 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ∑ q ∈ largePrimeResidueClass N p a y, (1 : ℝ) / q ≤
          ∑ j ∈ Finset.Icc 1 N,
            (((N ^ 21 / p + 1 : ℕ) : ℝ) *
                ((1 + eta) *
                  (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
                    Real.exp 3)) +
                ((y ^ S : ℕ) : ℝ) ^ 2) /
              (j * N ^ 21 + 1) := by
  obtain ⟨A, C, hA, hC, hblock⟩ :=
    exists_sum_inv_primeResidueInterval_upper_bound
  refine ⟨A, C, hA, hC, ?_⟩
  intro N p a y S hN hp hy hS hlog
  dsimp only
  calc
    (∑ q ∈ largePrimeResidueClass N p a y, (1 : ℝ) / q) ≤
        ∑ j ∈ Finset.Icc 1 N,
          ∑ q ∈ largePrimeResidueBlock N p a y j,
            (1 : ℝ) / q :=
      sum_inv_largePrimeResidueClass_le_sum_blocks hN
    _ ≤ ∑ j ∈ Finset.Icc 1 N,
          (((N ^ 21 / p + 1 : ℕ) : ℝ) *
              ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
                  Real.exp 3)) +
              ((y ^ S : ℕ) : ℝ) ^ 2) /
            (j * N ^ 21 + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      unfold largePrimeResidueBlock
      have hwidth :
          (j + 1) * N ^ 21 - j * N ^ 21 = N ^ 21 := by
        rw [show (j + 1) * N ^ 21 = j * N ^ 21 + N ^ 21 by ring]
        exact Nat.add_sub_cancel_left _ _
      have hden :
          (((j * N ^ 21 : ℕ) : ℝ)) + 1 =
            (j : ℝ) * (N : ℝ) ^ 21 + 1 := by
        push_cast
        rfl
      rw [← hden]
      have hb := hblock p a (j * N ^ 21) ((j + 1) * N ^ 21) y S
        hp hy hS hlog
      dsimp only at hb
      rw [hwidth] at hb
      exact hb

end Erdos822
