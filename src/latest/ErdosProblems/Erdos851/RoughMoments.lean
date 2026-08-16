/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.Scales
import ErdosProblems.Erdos851.ShiftCandidates

/-!
# Rough representation counts and their finite moments

This file connects the one- and two-shift sieve counts to the first and
second moments of the number of admissible powers of two.  The identities are
pure finite double-counting and work for an arbitrary interval scale `X` and
an arbitrary exponent cutoff `J`.
-/

open scoped BigOperators

namespace Erdos851

open ShiftSieve

/-- Number of powers `2^k`, `k < J`, for which the residual avoids every
prime in the medium interval `(z,Y)`. -/
noncomputable def roughCount (z Y J a : ℕ) : ℕ := by
  classical
  exact ((powIndices J).filter fun k =>
    Nat.Coprime (a - 2 ^ k) (mediumPrimeProduct z Y)).card

/-- The two definitions of the product of primes in `(z,Y)` used by the
elementary and sieve layers agree. -/
theorem mediumPrimeProduct_eq_sievePrimeProduct (z Y : ℕ) :
    mediumPrimeProduct z Y = Erdos387.sievePrimeProduct z Y := by
  have hprimes : mediumPrimes z Y = Erdos387.sievePrimes z Y := by
    ext p
    simp only [mediumPrimes, Erdos387.sievePrimes, Finset.mem_filter,
      Finset.mem_Ioo, Finset.mem_range]
    tauto
  simp [mediumPrimeProduct, Erdos387.sievePrimeProduct, hprimes]

/-- A positive rough count supplies a representation with a bounded number
of distinct prime factors.  The hypotheses are deliberately stated for an
arbitrary shell `(X,2X]`; in applications `J` is a logarithmic scale for `X`.
-/
theorem mem_twoPowAddSet_of_roughCount_pos
    {z Y J L X a : ℕ} (ha : a ∈ dyadicInterval X)
    (hscale : 2 ^ J ≤ X) (hY : 1 < Y)
    (hsize : 2 * X ≤ Y ^ (L + 1))
    (hrough : 0 < roughCount z Y J a) :
    a ∈ TwoPowAddSet ((primesUpTo z).card + L) := by
  classical
  rw [roughCount, Finset.card_pos] at hrough
  obtain ⟨k, hk⟩ := hrough
  have hk' := Finset.mem_filter.mp hk
  have hkJ : k ∈ powIndices J := hk'.1
  have hkX : 2 ^ k < X :=
    (pow_lt_dyadicScale_of_mem_powIndices hkJ).trans_le hscale
  have hXa : X < a := (Finset.mem_Ioc.mp ha).1
  have hka : 2 ^ k < a := hkX.trans hXa
  have haUpper : a ≤ 2 * X := (Finset.mem_Ioc.mp ha).2
  have hresSize : a - 2 ^ k < Y ^ (L + 1) := by
    exact (Nat.sub_lt (Nat.zero_lt_of_lt hXa) (pow_pos (by norm_num) k)).trans_le
      (haUpper.trans hsize)
  have hresFactors :
      (a - 2 ^ k).primeFactors.card ≤ (primesUpTo z).card + L :=
    rough_residual_primeFactors_card_le hka hY hresSize hk'.2
  rw [mem_twoPowAddSet]
  refine ⟨k, a - 2 ^ k, hresFactors, ?_⟩
  omega

/-- First moment of the rough representation count, as a sum of one-shift
sifted interval counts. -/
theorem sum_roughCount_eq_sum_card_siftedShiftCandidates
    (z Y J X : ℕ) :
    ∑ a ∈ dyadicInterval X, roughCount z Y J a =
      ∑ k ∈ powIndices J,
        (siftedShiftCandidates {2 ^ k} X z Y).card := by
  classical
  simp only [roughCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [siftedShiftCandidates, dyadicInterval, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mediumPrimeProduct_eq_sievePrimeProduct]
  simp [shiftedProduct, Nat.coprime_comm]

/-- Pointwise expansion of the square of `roughCount` as a count of ordered
pairs of admissible exponents. -/
theorem roughCount_sq_eq_pair_sum (z Y J a : ℕ) :
    roughCount z Y J a ^ 2 =
      ∑ k ∈ powIndices J, ∑ l ∈ powIndices J,
        if Nat.Coprime (a - 2 ^ k) (mediumPrimeProduct z Y) ∧
            Nat.Coprime (a - 2 ^ l) (mediumPrimeProduct z Y) then 1 else 0 := by
  classical
  let F := (powIndices J).filter fun k =>
    Nat.Coprime (a - 2 ^ k) (mediumPrimeProduct z Y)
  have hproduct : F ×ˢ F =
      ((powIndices J) ×ˢ (powIndices J)).filter fun kl =>
        Nat.Coprime (a - 2 ^ kl.1) (mediumPrimeProduct z Y) ∧
          Nat.Coprime (a - 2 ^ kl.2) (mediumPrimeProduct z Y) := by
    ext kl
    simp [F]
    tauto
  calc
    roughCount z Y J a ^ 2 = F.card ^ 2 := by
      simp only [roughCount, F]
    _ = (F ×ˢ F).card := by simp [pow_two]
    _ = (((powIndices J) ×ˢ (powIndices J)).filter fun kl =>
        Nat.Coprime (a - 2 ^ kl.1) (mediumPrimeProduct z Y) ∧
          Nat.Coprime (a - 2 ^ kl.2) (mediumPrimeProduct z Y)).card := by
      rw [hproduct]
    _ = ∑ kl ∈ (powIndices J) ×ˢ (powIndices J),
        if Nat.Coprime (a - 2 ^ kl.1) (mediumPrimeProduct z Y) ∧
            Nat.Coprime (a - 2 ^ kl.2) (mediumPrimeProduct z Y) then 1 else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ k ∈ powIndices J, ∑ l ∈ powIndices J,
        if Nat.Coprime (a - 2 ^ k) (mediumPrimeProduct z Y) ∧
            Nat.Coprime (a - 2 ^ l) (mediumPrimeProduct z Y) then 1 else 0 := by
      simp only [Finset.sum_product]

/-- Second moment of the rough representation count, as a double sum of
two-shift sifted interval counts. -/
theorem sum_roughCount_sq_eq_sum_card_siftedShiftCandidates
    (z Y J X : ℕ) :
    ∑ a ∈ dyadicInterval X, roughCount z Y J a ^ 2 =
      ∑ k ∈ powIndices J, ∑ l ∈ powIndices J,
        (siftedShiftCandidates {2 ^ k, 2 ^ l} X z Y).card := by
  classical
  simp_rw [roughCount_sq_eq_pair_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [siftedShiftCandidates, dyadicInterval]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mediumPrimeProduct_eq_sievePrimeProduct]
  by_cases hkl : 2 ^ k = 2 ^ l
  · simp [shiftedProduct, hkl, Nat.coprime_comm]
  · have hprod : shiftedProduct {2 ^ k, 2 ^ l} a =
        (a - 2 ^ k) * (a - 2 ^ l) := by
      simp [shiftedProduct, hkl]
    rw [hprod]
    simp only [Nat.coprime_mul_iff_right]
    simp [Nat.coprime_comm]

end Erdos851
