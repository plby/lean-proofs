/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.ElementaryMass

/-!
# Erdős Problem 446: first estimates for vector block families

This module specializes the weighted without-replacement inequality to the
reciprocal-prime blocks and identifies the divisor-count weight of every
vector family exactly.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem blockElementaryMass_eq_elementaryMass (j r : ℕ) :
    blockElementaryMass j r =
      elementaryMass (primeBlock j) (fun p : ℕ ↦ 1 / (p : ℝ)) r := by
  rfl

theorem primeBlock_weight_nonneg_le_endpoint_inv {j p : ℕ}
    (hp : p ∈ primeBlock j) :
    0 ≤ (1 / (p : ℝ)) ∧
      1 / (p : ℝ) ≤ 1 / (blockEndpoint j : ℝ) := by
  have hpData := mem_primeBlock.mp hp
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpData.1.pos
  have hendpointPos : (0 : ℝ) < blockEndpoint j := by
    exact_mod_cast blockEndpoint_pos j
  constructor
  · positivity
  · exact one_div_le_one_div_of_le hendpointPos
      (by exact_mod_cast hpData.2.1.le)

theorem primeBlockMass_eq_weight_sum (j : ℕ) :
    primeBlockMass j = ∑ p ∈ primeBlock j, 1 / (p : ℝ) := by
  rfl

/-- Distinct-prime selection in one block costs at most the explicit
factorial and `2^r` losses. -/
theorem blockElementaryMass_lower {j r : ℕ}
    (hsmall : (r : ℝ) * (1 / (blockEndpoint j : ℝ)) ≤
      primeBlockMass j / 2) :
    (primeBlockMass j / 2) ^ r / (r.factorial : ℝ) ≤
      blockElementaryMass j r := by
  rw [blockElementaryMass_eq_elementaryMass]
  apply half_total_pow_div_factorial_le_elementaryMass
    (primeBlock j) (fun p : ℕ ↦ 1 / (p : ℝ))
    (primeBlockMass_eq_weight_sum j)
    (fun p hp ↦ primeBlock_weight_nonneg_le_endpoint_inv hp)
    hsmall

/-- Sharp distinct-prime selection bound in one reciprocal-prime block. -/
theorem blockElementaryMass_falling_lower {j r : ℕ}
    (hsmall : (r : ℝ) * (1 / (blockEndpoint j : ℝ)) ≤
      primeBlockMass j) :
    (∏ t ∈ Finset.range r,
        (primeBlockMass j - (t : ℝ) / (blockEndpoint j : ℝ))) /
        (r.factorial : ℝ) ≤ blockElementaryMass j r := by
  rw [blockElementaryMass_eq_elementaryMass]
  simpa only [div_eq_mul_inv, one_mul] using
    fallingMass_div_factorial_le_elementaryMass
      (primeBlock j) (fun p : ℕ ↦ 1 / (p : ℝ))
      (primeBlockMass_eq_weight_sum j)
      (fun p hp ↦ primeBlock_weight_nonneg_le_endpoint_inv hp)
      (by positivity : 0 ≤ (1 / (blockEndpoint j : ℝ))) r
      (by simpa only [div_eq_mul_inv] using hsmall)

theorem card_divisors_eq_two_pow_primeFactors_card {n : ℕ}
    (hn : 0 < n) (hsq : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Nat.card_divisors hn.ne']
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p + 1)) =
        ∏ _p ∈ n.primeFactors, 2 := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hsq
        (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)]
    _ = 2 ^ n.primeFactors.card := by
      simp

theorem blockFamily_divisors_card {M k : ℕ} {b : ℕ → ℕ}
    {a : ℕ} (ha : a ∈ blockFamily M k b) :
    a.divisors.card = 2 ^ (∑ i ∈ Finset.range k, b i) := by
  obtain ⟨S, hS, rfl⟩ := mem_blockFamily.mp ha
  rw [card_divisors_eq_two_pow_primeFactors_card
    (selectionProduct_pos hS) (selectionProduct_squarefree hS),
    selectionProduct_primeFactors hS, card_selection_eq_sum hS]

theorem blockFamily_divisor_reciprocal_sum
    (M k : ℕ) (b : ℕ → ℕ) :
    (∑ a ∈ blockFamily M k b, (a.divisors.card : ℝ) / a) =
      (2 : ℝ) ^ (∑ i ∈ Finset.range k, b i) *
        ∏ i : Fin k, blockElementaryMass (M + i) (b i) := by
  calc
    (∑ a ∈ blockFamily M k b, (a.divisors.card : ℝ) / a) =
        (2 : ℝ) ^ (∑ i ∈ Finset.range k, b i) *
          ∑ a ∈ blockFamily M k b, 1 / (a : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [blockFamily_divisors_card ha]
      push_cast
      ring
    _ = (2 : ℝ) ^ (∑ i ∈ Finset.range k, b i) *
        ∏ i : Fin k, blockElementaryMass (M + i) (b i) := by
      rw [blockFamily_reciprocal_sum_factorization]

theorem blockFamily_reciprocal_sum_lower
    {M k : ℕ} {b : ℕ → ℕ}
    (hsmall : ∀ i : Fin k,
      (b i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
        primeBlockMass (M + i) / 2) :
    (∏ i : Fin k,
        (primeBlockMass (M + i) / 2) ^ (b i) /
          ((b i).factorial : ℝ)) ≤
      ∑ a ∈ blockFamily M k b, 1 / (a : ℝ) := by
  rw [blockFamily_reciprocal_sum_factorization]
  apply Finset.prod_le_prod
  · intro i hi
    apply div_nonneg
    · apply pow_nonneg
      apply div_nonneg
      · rw [primeBlockMass_eq_weight_sum]
        exact Finset.sum_nonneg fun p hp ↦
          (primeBlock_weight_nonneg_le_endpoint_inv hp).1
      · norm_num
    · positivity
  · intro i hi
    exact blockElementaryMass_lower (hsmall i)

/-- Product form of the sharp falling-mass lower bound for a vector class. -/
theorem blockFamily_reciprocal_sum_falling_lower
    {M k : ℕ} {b : ℕ → ℕ}
    (hsmall : ∀ i : Fin k,
      (b i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
        primeBlockMass (M + i)) :
    (∏ i : Fin k,
        (∏ t ∈ Finset.range (b i),
          (primeBlockMass (M + i) -
            (t : ℝ) / (blockEndpoint (M + i) : ℝ))) /
          ((b i).factorial : ℝ)) ≤
      ∑ a ∈ blockFamily M k b, 1 / (a : ℝ) := by
  rw [blockFamily_reciprocal_sum_factorization]
  apply Finset.prod_le_prod
  · intro i hi
    apply div_nonneg
    · apply Finset.prod_nonneg
      intro t ht
      apply sub_nonneg.mpr
      have htlt : t < b i := Finset.mem_range.mp ht
      have hm : 0 ≤ (1 / (blockEndpoint (M + i) : ℝ)) := by positivity
      calc
        (t : ℝ) / (blockEndpoint (M + i) : ℝ) ≤
            (b i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) := by
          rw [div_eq_mul_inv]
          have htb : (t : ℝ) ≤ (b i : ℝ) := by exact_mod_cast htlt.le
          simpa only [one_div] using mul_le_mul_of_nonneg_right htb hm
        _ ≤ primeBlockMass (M + i) := hsmall i
    · positivity
  · intro i hi
    exact blockElementaryMass_falling_lower (hsmall i)

end Erdos446
