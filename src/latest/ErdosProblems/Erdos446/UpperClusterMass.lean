/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperElementaryMass
import ErdosProblems.Erdos446.SieveDensity

/-!
# Erdős Problem 446: the squarefree cluster mass by prime-factor count

Ford's upper reduction leaves the reciprocal cluster mass of squarefree
integers composed of primes at most a cutoff.  This file defines that finite
mass directly as a sum over prime subsets, decomposes it exactly according to
the number of selected primes, and proves the elementary high-cardinality
majorant used for the tail.

The low-cardinality layers are the quantities to which the ordered-simplex
estimate applies.  Thus the interface here is independent of the particular
formalization of the Smirnov bound.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Prime subsets of cardinality `k` below the cutoff `P`. -/
def smoothPrimeSubsets (P k : ℕ) : Finset (Finset ℕ) :=
  (primesUpTo P).powersetCard k

/-- The squarefree integers all of whose prime factors are at most `P`. -/
def smoothSquarefreeNumbers (P : ℕ) : Finset ℕ :=
  (primesUpTo P).powerset.image fun S ↦ S.prod id

/-- Ford's `T_k(P)`: reciprocal cluster mass in the `k`th squarefree layer. -/
noncomputable def squarefreeClusterLayer (P k : ℕ) : ℝ :=
  ∑ S ∈ smoothPrimeSubsets P k,
    clusterLength (S.prod id) / ((S.prod id : ℕ) : ℝ)

/-- Total reciprocal cluster mass of squarefree `P`-smooth integers. -/
noncomputable def squarefreeClusterMass (P : ℕ) : ℝ :=
  ∑ a ∈ smoothSquarefreeNumbers P, clusterLength a / (a : ℝ)

theorem prime_of_mem_primesUpTo {P p : ℕ} (hp : p ∈ primesUpTo P) :
    p.Prime :=
  (Finset.mem_filter.mp hp).2

theorem primeProduct_primeFactors {P : ℕ} {S : Finset ℕ}
    (hS : S ⊆ primesUpTo P) :
    (S.prod id).primeFactors = S := by
  exact Nat.primeFactors_prod fun p hp ↦ prime_of_mem_primesUpTo (hS hp)

theorem primeProduct_pos {P : ℕ} {S : Finset ℕ}
    (hS : S ⊆ primesUpTo P) :
    0 < S.prod id := by
  apply Finset.prod_pos
  intro p hp
  exact (prime_of_mem_primesUpTo (hS hp)).pos

theorem primeProduct_squarefree {P : ℕ} {S : Finset ℕ}
    (hS : S ⊆ primesUpTo P) :
    Squarefree (S.prod id) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_
    (fun p hp ↦ (prime_of_mem_primesUpTo (hS hp)).squarefree)
  intro p hp q hq hpq
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes
    (prime_of_mem_primesUpTo (hS hp))
    (prime_of_mem_primesUpTo (hS hq))).mpr hpq

theorem primeProduct_injOn (P : ℕ) :
    Set.InjOn (fun S : Finset ℕ ↦ S.prod id) (primesUpTo P).powerset := by
  intro S hS T hT hprod
  have hSp : (S.prod id).primeFactors = S :=
    primeProduct_primeFactors (Finset.mem_powerset.mp hS)
  have hTp : (T.prod id).primeFactors = T :=
    primeProduct_primeFactors (Finset.mem_powerset.mp hT)
  calc
    S = (S.prod id).primeFactors := hSp.symm
    _ = (T.prod id).primeFactors := congrArg Nat.primeFactors hprod
    _ = T := hTp

set_option backward.isDefEq.respectTransparency false in
/-- The total smooth squarefree mass is the sum of its cardinality layers. -/
lemma squarefreeClusterMass_eq_sum_layers (P : ℕ) :
    squarefreeClusterMass P =
      ∑ k ∈ Finset.range ((primesUpTo P).card + 1),
        squarefreeClusterLayer P k := by
  rw [squarefreeClusterMass, smoothSquarefreeNumbers,
    Finset.sum_image (primeProduct_injOn P)]
  rw [Finset.powerset_card_disjiUnion]
  rw [sum_disjiUnion]
  rfl

theorem squarefreeClusterLayer_nonneg (P k : ℕ) :
    0 ≤ squarefreeClusterLayer P k := by
  apply Finset.sum_nonneg
  intro S hS
  exact div_nonneg (clusterLength_nonneg _) (Nat.cast_nonneg _)

private theorem clusterTerm_le_elementaryTerm
    {P k : ℕ} {S : Finset ℕ} (hS : S ∈ smoothPrimeSubsets P k) :
    clusterLength (S.prod id) / ((S.prod id : ℕ) : ℝ) ≤
      ((2 : ℝ) ^ k * Real.log 2) *
        subsetWeight (fun p : ℕ ↦ 1 / (p : ℝ)) S := by
  have hsubset : S ⊆ primesUpTo P :=
    (Finset.mem_powersetCard.mp hS).1
  have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
  have hpos : 0 < S.prod id := primeProduct_pos hsubset
  have hsq : Squarefree (S.prod id) := primeProduct_squarefree hsubset
  have hpf : (S.prod id).primeFactors = S := primeProduct_primeFactors hsubset
  have hdivCard : (S.prod id).divisors.card = 2 ^ k := by
    rw [card_divisors_eq_two_pow_primeFactors_card hpos hsq, hpf, hcard]
  have hcluster := clusterLength_le_card_divisors_mul_log_two (S.prod id)
  rw [hdivCard] at hcluster
  have hden : (0 : ℝ) < (S.prod id : ℕ) := by exact_mod_cast hpos
  have hweight :
      subsetWeight (fun p : ℕ ↦ 1 / (p : ℝ)) S =
        1 / ((S.prod id : ℕ) : ℝ) := by
    change selectionWeight S = _
    exact selectionWeight_eq_inv_product S
  rw [hweight, div_eq_mul_inv, one_div]
  exact mul_le_mul_of_nonneg_right (by simpa using hcluster)
    (inv_nonneg.mpr hden.le)

/-- The elementary pointwise envelope for a fixed prime-factor layer. -/
theorem squarefreeClusterLayer_le_elementaryMass (P k : ℕ) :
    squarefreeClusterLayer P k ≤
      ((2 : ℝ) ^ k * Real.log 2) *
        elementaryMass (primesUpTo P) (fun p : ℕ ↦ 1 / (p : ℝ)) k := by
  rw [squarefreeClusterLayer, elementaryMass, smoothPrimeSubsets,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun S hS ↦ clusterTerm_le_elementaryTerm hS

/-- Sampling the selected primes with replacement gives Ford's elementary
exponential-tail bound. -/
theorem factorial_mul_squarefreeClusterLayer_le (P k : ℕ) :
    (k.factorial : ℝ) * squarefreeClusterLayer P k ≤
      Real.log 2 *
        (2 * (∑ p ∈ primesUpTo P, 1 / (p : ℝ))) ^ k := by
  let E := elementaryMass (primesUpTo P)
    (fun p : ℕ ↦ 1 / (p : ℝ)) k
  have hfac :
      (k.factorial : ℝ) * E ≤
        (∑ p ∈ primesUpTo P, 1 / (p : ℝ)) ^ k := by
    exact factorial_mul_elementaryMass_le_pow_sum
      (primesUpTo P) (fun p : ℕ ↦ 1 / (p : ℝ))
      (fun p hp ↦ by positivity) k
  have hkfac : (0 : ℝ) ≤ k.factorial := by positivity
  have hscale : 0 ≤ (2 : ℝ) ^ k * Real.log 2 := by positivity
  calc
    (k.factorial : ℝ) * squarefreeClusterLayer P k ≤
        (k.factorial : ℝ) * (((2 : ℝ) ^ k * Real.log 2) * E) :=
      mul_le_mul_of_nonneg_left
        (squarefreeClusterLayer_le_elementaryMass P k) hkfac
    _ = ((2 : ℝ) ^ k * Real.log 2) * ((k.factorial : ℝ) * E) := by
      ring
    _ ≤ ((2 : ℝ) ^ k * Real.log 2) *
        (∑ p ∈ primesUpTo P, 1 / (p : ℝ)) ^ k :=
      mul_le_mul_of_nonneg_left hfac hscale
    _ = Real.log 2 *
        (2 * (∑ p ∈ primesUpTo P, 1 / (p : ℝ))) ^ k := by
      rw [mul_pow]
      ring

/-- Division by the positive factorial puts the high-cardinality majorant in
the usual exponential-series form. -/
theorem squarefreeClusterLayer_le_poissonTerm (P k : ℕ) :
    squarefreeClusterLayer P k ≤
      Real.log 2 *
        (2 * (∑ p ∈ primesUpTo P, 1 / (p : ℝ))) ^ k /
          (k.factorial : ℝ) := by
  have hfac : (0 : ℝ) < k.factorial := by positivity
  exact (le_div_iff₀ hfac).2 (by
    simpa only [mul_comm] using
      factorial_mul_squarefreeClusterLayer_le P k)

end Erdos446
