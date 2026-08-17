/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos285.RoughCounts
import ErdosProblems.Erdos387.RoughDivisorBound

/-!
# Repeated large prime factors for Erdős Problem 444

This file formalizes the square-divisor exceptional-set estimate in the
Erdős--Sárközy product argument.  If the multiplicity of prime factors above
`y` exceeds their distinct count by more than `2 * B`, the canonical square
part of the integer is larger than `y ^ B`.  A finite union bound over square
divisors then gives an explicit `U / L` bound for integers up to `U` with a
square divisor larger than `L`.
-/

open scoped BigOperators

namespace Erdos444

noncomputable section

/-- Distinct prime factors of `n` which are larger than `y`. -/
def largePrimeSupport (n y : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p ↦ y < p)

/-- Number of distinct prime factors of `n` which are larger than `y`. -/
def largePrimeDistinctCount (n y : ℕ) : ℕ :=
  (largePrimeSupport n y).card

/-- Number of prime factors of `n` larger than `y`, counted with
multiplicity. -/
def largePrimeMultiplicity (n y : ℕ) : ℕ :=
  ∑ p ∈ largePrimeSupport n y, n.factorization p

/-- Excess multiplicity beyond the number of distinct large prime factors. -/
def repeatedPrimeExcess (n y : ℕ) : ℕ :=
  largePrimeMultiplicity n y - largePrimeDistinctCount n y

/-- Sum of the half-exponents of the large prime factors.  This is the
exponent count contributed to the canonical square-root divisor. -/
def largePrimeHalfExponentSum (n y : ℕ) : ℕ :=
  ∑ p ∈ largePrimeSupport n y, n.factorization p / 2

@[simp] theorem mem_largePrimeSupport {n y p : ℕ} (hn : n ≠ 0) :
    p ∈ largePrimeSupport n y ↔ y < p ∧ p.Prime ∧ p ∣ n := by
  simp only [largePrimeSupport, Finset.mem_filter, Nat.mem_primeFactors]
  aesop

private theorem one_le_factorization_of_mem_largePrimeSupport
    {n y p : ℕ} (hp : p ∈ largePrimeSupport n y) :
    1 ≤ n.factorization p := by
  have hpSupport : p ∈ n.factorization.support := by
    simpa [largePrimeSupport, Nat.support_factorization] using
      (Finset.mem_filter.mp hp).1
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hpSupport)

/-- The excess multiplicity is at most twice the sum of the half-exponents. -/
theorem repeatedPrimeExcess_le_two_mul_halfExponentSum (n y : ℕ) :
    repeatedPrimeExcess n y ≤ 2 * largePrimeHalfExponentSum n y := by
  rw [repeatedPrimeExcess, Nat.sub_le_iff_le_add]
  unfold largePrimeMultiplicity largePrimeDistinctCount
  rw [Finset.card_eq_sum_ones]
  calc
    (∑ p ∈ largePrimeSupport n y, n.factorization p) ≤
        ∑ p ∈ largePrimeSupport n y,
          (1 + 2 * (n.factorization p / 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpos := one_le_factorization_of_mem_largePrimeSupport hp
      omega
    _ = (∑ _p ∈ largePrimeSupport n y, 1) +
        2 * largePrimeHalfExponentSum n y := by
      rw [Finset.sum_add_distrib]
      unfold largePrimeHalfExponentSum
      rw [Finset.mul_sum]
    _ = 2 * largePrimeHalfExponentSum n y +
        ∑ _p ∈ largePrimeSupport n y, 1 := Nat.add_comm _ _

private theorem pow_halfExponent_product_le_squarePart
    (n y : ℕ) :
    (∏ p ∈ largePrimeSupport n y, p ^ (n.factorization p / 2)) ≤
      Erdos387.factorizationSquarePart n := by
  unfold Erdos387.factorizationSquarePart
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · exact Finset.filter_subset _ _
  · intro p hp _
    exact Nat.one_le_pow _ p (Nat.pos_of_mem_primeFactors hp)

private theorem pow_halfExponentSum_le_product
    {n y : ℕ} :
    y ^ largePrimeHalfExponentSum n y ≤
      ∏ p ∈ largePrimeSupport n y, p ^ (n.factorization p / 2) := by
  unfold largePrimeHalfExponentSum
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro p hp
    exact Nat.zero_le _
  · intro p hp
    have hyp : y ≤ p := (Finset.mem_filter.mp hp).2.le
    exact Nat.pow_le_pow_left hyp _

/-- Large excess multiplicity produces a large square divisor.

The integer `j` is the canonical square part formed by taking half of every
prime exponent.  The hypotheses imply `y ^ B < j`, while the standard
square-part factorization gives `j ^ 2 ∣ n`. -/
theorem exists_large_squareDivisor_of_two_mul_lt_repeatedPrimeExcess
    {n y B : ℕ} (hn : n ≠ 0) (hy : 1 < y)
    (hexcess : 2 * B < repeatedPrimeExcess n y) :
    ∃ j : ℕ, y ^ B < j ∧ j ^ 2 ∣ n := by
  let j := Erdos387.factorizationSquarePart n
  refine ⟨j, ?_, ?_⟩
  · have hB : B < largePrimeHalfExponentSum n y := by
      have htwo : 2 * B < 2 * largePrimeHalfExponentSum n y :=
        hexcess.trans_le (repeatedPrimeExcess_le_two_mul_halfExponentSum n y)
      omega
    have hpow : y ^ B < y ^ largePrimeHalfExponentSum n y :=
      Nat.pow_lt_pow_right hy hB
    exact hpow.trans_le
      ((pow_halfExponentSum_le_product (n := n) (y := y)).trans
        (pow_halfExponent_product_le_squarePart n y))
  · refine ⟨Erdos387.factorizationOddPart n, ?_⟩
    dsimp [j]
    exact (Erdos387.factorizationSquarePart_sq_mul_oddPart hn).symm

/-- Positive integers at most `U` which possess a square divisor strictly
larger than `L`. -/
noncomputable def largeSquareDivisorNumbers (L U : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 U).filter fun n ↦ ∃ j : ℕ, L < j ∧ j ^ 2 ∣ n

@[simp] theorem mem_largeSquareDivisorNumbers {L U n : ℕ} :
    n ∈ largeSquareDivisorNumbers L U ↔
      1 ≤ n ∧ n ≤ U ∧ ∃ j : ℕ, L < j ∧ j ^ 2 ∣ n := by
  simp [largeSquareDivisorNumbers, and_assoc]

private theorem largeSquareDivisorNumbers_subset_biUnion
    {L U : ℕ} (hL : 1 ≤ L) :
    largeSquareDivisorNumbers L U ⊆
      (Finset.Icc (L + 1) U).biUnion
        (fun j ↦ Erdos285.RoughCounts.multiplesUpTo U (j ^ 2)) := by
  intro n hn
  obtain ⟨hn1, hnU, j, hLj, hjn⟩ := mem_largeSquareDivisorNumbers.mp hn
  have hjpos : 0 < j := by omega
  have hjSqPos : 0 < j ^ 2 := pow_pos hjpos 2
  have hjSqLeN : j ^ 2 ≤ n := Nat.le_of_dvd (by omega) hjn
  have hjLeSq : j ≤ j ^ 2 := by nlinarith
  have hjU : j ≤ U := hjLeSq.trans (hjSqLeN.trans hnU)
  rw [Finset.mem_biUnion]
  refine ⟨j, Finset.mem_Icc.mpr ⟨by omega, hjU⟩, ?_⟩
  exact Erdos285.RoughCounts.mem_multiplesUpTo.mpr ⟨hn1, hnU, hjn⟩

private theorem card_multiplesUpTo_square (U j : ℕ) (hj : 0 < j) :
    (Erdos285.RoughCounts.multiplesUpTo U (j ^ 2)).card = U / j ^ 2 := by
  exact UnitFractions.count_multiples (pow_pos hj 2)

/-- Square-divisor union bound.  Integers `n ≤ U` divisible by `j²` for
some `j > L` have cardinality at most `U / L`. -/
theorem card_largeSquareDivisorNumbers_le_div
    {L U : ℕ} (hL : 1 ≤ L) :
    ((largeSquareDivisorNumbers L U).card : ℝ) ≤ (U : ℝ) / L := by
  have hcardNat : (largeSquareDivisorNumbers L U).card ≤
      ∑ j ∈ Finset.Icc (L + 1) U, U / j ^ 2 := by
    calc
      (largeSquareDivisorNumbers L U).card ≤
          ((Finset.Icc (L + 1) U).biUnion
            (fun j ↦ Erdos285.RoughCounts.multiplesUpTo U (j ^ 2))).card :=
        Finset.card_le_card (largeSquareDivisorNumbers_subset_biUnion hL)
      _ ≤ ∑ j ∈ Finset.Icc (L + 1) U,
          (Erdos285.RoughCounts.multiplesUpTo U (j ^ 2)).card :=
        Finset.card_biUnion_le
      _ = ∑ j ∈ Finset.Icc (L + 1) U, U / j ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact card_multiplesUpTo_square U j (by
          have := (Finset.mem_Icc.mp hj).1
          omega)
  calc
    ((largeSquareDivisorNumbers L U).card : ℝ) ≤
        ((∑ j ∈ Finset.Icc (L + 1) U, U / j ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    _ = ∑ j ∈ Finset.Icc (L + 1) U, ((U / j ^ 2 : ℕ) : ℝ) := by
      norm_cast
    _ ≤ ∑ j ∈ Finset.Icc (L + 1) U, (U : ℝ) / (j : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Nat.cast_pow] using
        (Nat.cast_div_le :
          ((U / j ^ 2 : ℕ) : ℝ) ≤ (U : ℝ) / (j ^ 2 : ℕ))
    _ = (U : ℝ) *
        ∑ j ∈ Finset.Icc (L + 1) U, ((j : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [div_eq_mul_inv]
    _ ≤ (U : ℝ) * (L : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left
      · exact Erdos285.RoughCounts.sum_Icc_inv_sq_le_inv L U hL
      · positivity
    _ = (U : ℝ) / L := by rw [div_eq_mul_inv]

/-- Integers at most `U` for which the excess multiplicity of primes above
`y` is larger than `2 * B`. -/
def repeatedPrimeExceptionalUpTo (y B U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun n ↦ 2 * B < repeatedPrimeExcess n y

@[simp] theorem mem_repeatedPrimeExceptionalUpTo {y B U n : ℕ} :
    n ∈ repeatedPrimeExceptionalUpTo y B U ↔
      1 ≤ n ∧ n ≤ U ∧ 2 * B < repeatedPrimeExcess n y := by
  simp [repeatedPrimeExceptionalUpTo, and_assoc]

theorem repeatedPrimeExceptionalUpTo_subset_largeSquareDivisorNumbers
    {y B U : ℕ} (hy : 1 < y) :
    repeatedPrimeExceptionalUpTo y B U ⊆
      largeSquareDivisorNumbers (y ^ B) U := by
  intro n hn
  obtain ⟨hn1, hnU, hexcess⟩ := mem_repeatedPrimeExceptionalUpTo.mp hn
  obtain ⟨j, hj, hjdvd⟩ :=
    exists_large_squareDivisor_of_two_mul_lt_repeatedPrimeExcess
      (by omega : n ≠ 0) hy hexcess
  exact mem_largeSquareDivisorNumbers.mpr
    ⟨hn1, hnU, j, hj, hjdvd⟩

/-- Direct cardinality estimate for the repeated-prime exceptional set. -/
theorem card_repeatedPrimeExceptionalUpTo_le_div
    {y B U : ℕ} (hy : 1 < y) :
    ((repeatedPrimeExceptionalUpTo y B U).card : ℝ) ≤
      (U : ℝ) / y ^ B := by
  have hsubset :=
    repeatedPrimeExceptionalUpTo_subset_largeSquareDivisorNumbers
      (y := y) (B := B) (U := U) hy
  calc
    ((repeatedPrimeExceptionalUpTo y B U).card : ℝ) ≤
        ((largeSquareDivisorNumbers (y ^ B) U).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (U : ℝ) / (y ^ B : ℕ) :=
      card_largeSquareDivisorNumbers_le_div
        (Nat.one_le_pow B y (by omega : 0 < y))
    _ = (U : ℝ) / y ^ B := by norm_num

end

end Erdos444
