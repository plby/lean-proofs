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

import ErdosProblems.Erdos444.Basic

/-!
# Erdős Problem 444: the finite tuple moment

This file formalizes the exact finite double count used in the
Erdős--Sárközy large-values argument.  For a finite set `Astar`, an ordered
`r`-tuple is represented by `n` when the product of its entries divides `n`.
The total number of representations up to `U ^ r` has a reciprocal-mass
lower bound, while each pointwise representation count is bounded by the
`r`-th power of `divisorCount`.
-/

open scoped BigOperators

namespace Erdos444

/-- The finite set of ordered `r`-tuples with every coordinate in
`Astar`. -/
def orderedTuples (Astar : Finset ℕ) (r : ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset fun _ : Fin r ↦ Astar

@[simp]
theorem mem_orderedTuples_iff {Astar : Finset ℕ} {r : ℕ}
    {a : Fin r → ℕ} :
    a ∈ orderedTuples Astar r ↔ ∀ i, a i ∈ Astar := by
  simp [orderedTuples, Fintype.mem_piFinset]

/-- Product of the coordinates of an ordered tuple. -/
def tupleProduct {r : ℕ} (a : Fin r → ℕ) : ℕ :=
  ∏ i, a i

/-- Number of ordered tuples from `Astar ^ r` whose coordinate product
divides `n`. -/
def representationCount (Astar : Finset ℕ) (r n : ℕ) : ℕ :=
  ((orderedTuples Astar r).filter fun a ↦ tupleProduct a ∣ n).card

/-- Positive integers at most `N` which represent at least one ordered
tuple. -/
def representationSupport (Astar : Finset ℕ) (r N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter fun n ↦ 0 < representationCount Astar r n

@[simp]
theorem mem_representationSupport_iff {Astar : Finset ℕ} {r N n : ℕ} :
    n ∈ representationSupport Astar r N ↔
      0 < n ∧ n ≤ N ∧ 0 < representationCount Astar r n := by
  simp [representationSupport, and_assoc]

/-- Exact finite double count: first sum over represented integers, or first
choose a tuple and then count the multiples of its product. -/
theorem sum_representationCount_eq_sum_div
    (Astar : Finset ℕ) (r N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, representationCount Astar r n =
      ∑ a ∈ orderedTuples Astar r, N / tupleProduct a := by
  classical
  calc
    ∑ n ∈ Finset.Ioc 0 N, representationCount Astar r n =
        ∑ n ∈ Finset.Ioc 0 N,
          ∑ a ∈ orderedTuples Astar r,
            if tupleProduct a ∣ n then 1 else 0 := by
      simp only [representationCount, Finset.card_filter]
    _ = ∑ a ∈ orderedTuples Astar r,
          ∑ n ∈ Finset.Ioc 0 N,
            if tupleProduct a ∣ n then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a ∈ orderedTuples Astar r,
          ((Finset.Ioc 0 N).filter fun n ↦ tupleProduct a ∣ n).card := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.card_filter]
    _ = ∑ a ∈ orderedTuples Astar r, N / tupleProduct a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Nat.Ioc_filter_dvd_card_eq_div N (tupleProduct a)

/-- The product of a positive tuple is positive. -/
theorem tupleProduct_pos
    {Astar : Finset ℕ} {r : ℕ} {a : Fin r → ℕ}
    (ha : a ∈ orderedTuples Astar r)
    (hpos : ∀ m ∈ Astar, 0 < m) :
    0 < tupleProduct a := by
  unfold tupleProduct
  exact Finset.prod_pos fun i hi ↦ hpos (a i) (mem_orderedTuples_iff.mp ha i)

/-- If every entry of `Astar` is at most `U`, every `r`-fold tuple product
is at most `U ^ r`. -/
theorem tupleProduct_le_pow
    {Astar : Finset ℕ} {r U : ℕ} {a : Fin r → ℕ}
    (ha : a ∈ orderedTuples Astar r)
    (hle : ∀ m ∈ Astar, m ≤ U) :
    tupleProduct a ≤ U ^ r := by
  unfold tupleProduct
  calc
    ∏ i, a i ≤ ∏ _i : Fin r, U := by
      exact Finset.prod_le_prod (fun i hi ↦ Nat.zero_le (a i))
        (fun i hi ↦ hle (a i) (mem_orderedTuples_iff.mp ha i))
    _ = U ^ r := by simp

/-- The reciprocal weights of all ordered tuples factor as the `r`-th power
of the reciprocal mass of `Astar`. -/
theorem sum_tupleProduct_inv_eq_sum_inv_pow
    (Astar : Finset ℕ) (r : ℕ) :
    ∑ a ∈ orderedTuples Astar r, ((tupleProduct a : ℝ)⁻¹) =
      (∑ m ∈ Astar, ((m : ℝ)⁻¹)) ^ r := by
  classical
  rw [Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro a ha
  simp [tupleProduct, Finset.prod_inv_distrib]

/-- For `0 < p ≤ N`, the number `N / p` of positive multiples of `p` up
to `N` is at least half of the real quotient `N / p`.

This is the only floor loss in the finite moment lower bound. -/
theorem half_real_div_le_nat_div
    {N p : ℕ} (hp : 0 < p) (hpN : p ≤ N) :
    (N : ℝ) / (2 * (p : ℝ)) ≤ (N / p : ℕ) := by
  have hqpos : 0 < N / p := Nat.div_pos hpN hp
  have hq : N / p + 1 ≤ 2 * (N / p) := by omega
  have hN : N ≤ 2 * (N / p) * p := by
    calc
      N ≤ p * (N / p + 1) := (Nat.lt_mul_div_succ N hp).le
      _ ≤ p * (2 * (N / p)) := Nat.mul_le_mul_left p hq
      _ = 2 * (N / p) * p := by ring
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (p : ℝ))]
  have hN' : N ≤ (N / p) * (2 * p) := by
    nlinarith [hN]
  exact_mod_cast hN'

/-- The total tuple representation count up to `U ^ r` is at least
`(U ^ r) / 2` times the `r`-th power of the reciprocal mass of `Astar`. -/
theorem half_pow_mul_sum_inv_pow_le_sum_representationCount
    (Astar : Finset ℕ) (r U : ℕ)
    (hpos : ∀ m ∈ Astar, 0 < m)
    (hle : ∀ m ∈ Astar, m ≤ U) :
    ((U : ℝ) ^ r / 2) *
        (∑ m ∈ Astar, ((m : ℝ)⁻¹)) ^ r ≤
      ∑ n ∈ Finset.Ioc 0 (U ^ r),
        (representationCount Astar r n : ℝ) := by
  classical
  rw [← sum_tupleProduct_inv_eq_sum_inv_pow Astar r]
  rw [Finset.mul_sum]
  calc
    ∑ a ∈ orderedTuples Astar r,
          (U : ℝ) ^ r / 2 * (tupleProduct a : ℝ)⁻¹ ≤
        ∑ a ∈ orderedTuples Astar r,
          ((U ^ r) / tupleProduct a : ℕ) := by
      rw [Nat.cast_sum]
      apply Finset.sum_le_sum
      intro a ha
      have hp := tupleProduct_pos ha hpos
      have hpU := tupleProduct_le_pow ha hle
      have hfloor := half_real_div_le_nat_div hp hpU
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
        Nat.cast_pow] using hfloor
    _ = ∑ n ∈ Finset.Ioc 0 (U ^ r),
          (representationCount Astar r n : ℝ) := by
      rw [← Nat.cast_sum, sum_representationCount_eq_sum_div]

/-- Every represented tuple gives `r` (not necessarily distinct) members of
`A` dividing `n`.  Consequently the representation count is at most the
`r`-th power of `divisorCount A n`. -/
theorem representationCount_le_divisorCount_pow
    {Astar : Finset ℕ} {A : Set ℕ} {r n : ℕ}
    (hsub : ∀ m ∈ Astar, m ∈ A) (hn : n ≠ 0) :
    representationCount Astar r n ≤ divisorCount A n ^ r := by
  classical
  let divisorsInA : Finset ℕ := n.divisors.filter fun m ↦ m ∈ A
  have hsubset :
      (orderedTuples Astar r).filter (fun a ↦ tupleProduct a ∣ n) ⊆
        Fintype.piFinset (fun _ : Fin r ↦ divisorsInA) := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    rw [Fintype.mem_piFinset]
    intro i
    have hmemAstar := mem_orderedTuples_iff.mp ha'.1 i
    have hcoordProd : a i ∣ tupleProduct a := by
      unfold tupleProduct
      exact Finset.dvd_prod_of_mem a (Finset.mem_univ i)
    exact Finset.mem_filter.mpr ⟨
      Nat.mem_divisors.mpr ⟨hcoordProd.trans ha'.2, hn⟩,
      hsub (a i) hmemAstar⟩
  calc
    representationCount Astar r n ≤
        (Fintype.piFinset (fun _ : Fin r ↦ divisorsInA)).card :=
      Finset.card_le_card hsubset
    _ = divisorsInA.card ^ r := by
      simp
    _ = divisorCount A n ^ r := by
      rfl

/-- Restricting a sum to the representation support changes no terms. -/
theorem sum_representationCount_eq_sum_support
    (Astar : Finset ℕ) (r N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, representationCount Astar r n =
      ∑ n ∈ representationSupport Astar r N,
        representationCount Astar r n := by
  classical
  rw [representationSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : 0 < representationCount Astar r n
  · simp [h]
  · have hz : representationCount Astar r n = 0 := Nat.eq_zero_of_not_pos h
    simp [hz]

/-- Support/cardinality upper bound for the total moment.  On the support,
the pointwise representation estimate is controlled by the maximum divisor
count below the strict cutoff `N + 1`. -/
theorem sum_representationCount_le_support_card_mul_maxDivisorCount_pow
    {Astar : Finset ℕ} {A : Set ℕ} (r N : ℕ)
    (hsub : ∀ m ∈ Astar, m ∈ A) :
    ∑ n ∈ Finset.Ioc 0 N, representationCount Astar r n ≤
      (representationSupport Astar r N).card *
        maxDivisorCountNat A (N + 1) ^ r := by
  rw [sum_representationCount_eq_sum_support]
  calc
    ∑ n ∈ representationSupport Astar r N,
          representationCount Astar r n ≤
        (representationSupport Astar r N).card •
          maxDivisorCountNat A (N + 1) ^ r := by
      apply Finset.sum_le_card_nsmul
      intro n hn
      have hmem := mem_representationSupport_iff.mp hn
      have hpoint := representationCount_le_divisorCount_pow (r := r) hsub
        (Nat.ne_of_gt hmem.1)
      have hmax : divisorCount A n ≤ maxDivisorCountNat A (N + 1) :=
        divisorCount_le_maxDivisorCountNat hmem.1
          (Nat.lt_succ_of_le hmem.2.1)
      exact hpoint.trans (Nat.pow_le_pow_left hmax r)
    _ = (representationSupport Astar r N).card *
          maxDivisorCountNat A (N + 1) ^ r := by
      rw [Nat.nsmul_eq_mul]

/-- The form of the support/cardinality comparison at the product cutoff
`U ^ r`. -/
theorem sum_representationCount_powCutoff_le
    {Astar : Finset ℕ} {A : Set ℕ} (r U : ℕ)
    (hsub : ∀ m ∈ Astar, m ∈ A) :
    ∑ n ∈ Finset.Ioc 0 (U ^ r), representationCount Astar r n ≤
      (representationSupport Astar r (U ^ r)).card *
        maxDivisorCountNat A (U ^ r + 1) ^ r :=
  sum_representationCount_le_support_card_mul_maxDivisorCount_pow r (U ^ r) hsub

end Erdos444
