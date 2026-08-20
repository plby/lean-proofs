/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FordPowersetMoments
import ErdosProblems.Erdos446.ClusterProductSharp
import ErdosProblems.Erdos446.PrimeLogMoments

/-!
# Erdős Problem 446: the cubic logarithmic cluster moment

This file formalizes the `log^3 a` expansion in Ford--Koukoulopoulos
Lemma 3.3.  Marking one prime factor and deleting it costs exactly the
factor `2/p`; the abstract powerset moment inequality therefore reduces the
cubic logarithmic moment to the first three prime-log moments.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Reciprocal cluster weight attached directly to a finite prime set. -/
noncomputable def primeSubsetClusterTerm (S : Finset ℕ) : ℝ :=
  clusterLength (S.prod id) / ((S.prod id : ℕ) : ℝ)

/-- The cubic logarithmic cluster moment over squarefree `P`-smooth numbers. -/
noncomputable def squarefreeClusterLogMoment (P : ℕ) : ℝ :=
  ∑ S ∈ (primesUpTo P).powerset,
    primeSubsetClusterTerm S * Real.log ((S.prod id : ℕ) : ℝ) ^ 3

theorem primeSubsetClusterTerm_nonneg (S : Finset ℕ) :
    0 ≤ primeSubsetClusterTerm S := by
  exact div_nonneg (clusterLength_nonneg _) (Nat.cast_nonneg _)

theorem primeSubset_product_pos {P : ℕ} {S : Finset ℕ}
    (hSP : S ⊆ primesUpTo P) :
    0 < S.prod id :=
  primeProduct_pos hSP

theorem log_primeSubset_product {P : ℕ} {S : Finset ℕ}
    (hSP : S ⊆ primesUpTo P) :
    Real.log ((S.prod id : ℕ) : ℝ) =
      ∑ p ∈ S, Real.log (p : ℝ) := by
  rw [Nat.cast_prod, Real.log_prod]
  · simp only [id_eq]
  · intro p hp
    exact_mod_cast (prime_of_mem_primesUpTo (hSP hp)).ne_zero

/-- Deleting a marked prime costs at most `2/p` in reciprocal cluster
weight. -/
theorem primeSubsetClusterTerm_le_delete
    {P : ℕ} {S : Finset ℕ} (hSP : S ⊆ primesUpTo P)
    {p : ℕ} (hpS : p ∈ S) :
    primeSubsetClusterTerm S ≤
      (2 / (p : ℝ)) * primeSubsetClusterTerm (S.erase p) := by
  let T := S.erase p
  have hpPrime : p.Prime := prime_of_mem_primesUpTo (hSP hpS)
  have hTsub : T ⊆ primesUpTo P :=
    (Finset.erase_subset p S).trans hSP
  have hTpos : 0 < T.prod id := primeSubset_product_pos hTsub
  have hprod : p * T.prod id = S.prod id := by
    simpa only [T, id_eq] using Finset.mul_prod_erase S id hpS
  have hcluster :
      clusterLength (p * T.prod id) ≤ 2 * clusterLength (T.prod id) :=
    clusterLength_prime_mul_le_two_mul hpPrime hTpos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hTR : (0 : ℝ) < T.prod id := by exact_mod_cast hTpos
  change clusterLength (S.prod id) / ((S.prod id : ℕ) : ℝ) ≤
    (2 / (p : ℝ)) *
      (clusterLength (T.prod id) / ((T.prod id : ℕ) : ℝ))
  rw [← hprod, Nat.cast_mul]
  calc
    clusterLength (p * T.prod id) /
        ((p : ℝ) * ((T.prod id : ℕ) : ℝ)) ≤
        (2 * clusterLength (T.prod id)) /
          ((p : ℝ) * ((T.prod id : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_right hcluster (mul_nonneg hpR.le hTR.le)
    _ = (2 / (p : ℝ)) *
        (clusterLength (T.prod id) / ((T.prod id : ℕ) : ℝ)) := by
      field_simp [hpR.ne', hTR.ne']

theorem squarefreeClusterLogMoment_eq_powersetMoment (P : ℕ) :
    squarefreeClusterLogMoment P =
      powersetAdditiveMoment (primesUpTo P) primeSubsetClusterTerm
        (fun p ↦ Real.log (p : ℝ)) 3 := by
  rw [squarefreeClusterLogMoment, powersetAdditiveMoment]
  apply Finset.sum_congr rfl
  intro S hS
  rw [log_primeSubset_product (Finset.mem_powerset.mp hS)]

theorem squarefreeClusterMass_eq_powersetMoment_zero (P : ℕ) :
    squarefreeClusterMass P =
      powersetAdditiveMoment (primesUpTo P) primeSubsetClusterTerm
        (fun p ↦ Real.log (p : ℝ)) 0 := by
  rw [squarefreeClusterMass, smoothSquarefreeNumbers,
    Finset.sum_image (primeProduct_injOn P)]
  simp only [powersetAdditiveMoment, pow_zero, mul_one,
    primeSubsetClusterTerm]

/-- Exact finite cubic-moment estimate before applying Mertens.  The three
summands correspond to three distinct marked primes, exactly two equal, and
all three equal. -/
theorem squarefreeClusterLogMoment_le_primeMoments (P : ℕ) :
    squarefreeClusterLogMoment P ≤
      ((2 * weightedPrimeLogMass P) ^ 3 +
          3 * (2 * weightedPrimeLogMass P) *
            (2 * primeLogMoment 2 P) +
          2 * primeLogMoment 3 P) * squarefreeClusterMass P := by
  rw [squarefreeClusterLogMoment_eq_powersetMoment,
    squarefreeClusterMass_eq_powersetMoment_zero]
  have h := powersetAdditiveMoment_three_le
    (primesUpTo P) primeSubsetClusterTerm
    (fun p ↦ Real.log (p : ℝ)) (fun p ↦ 2 / (p : ℝ))
    (fun S hS ↦ primeSubsetClusterTerm_nonneg S)
    (fun p hp ↦ Real.log_nonneg (by
      exact_mod_cast (prime_of_mem_primesUpTo hp).one_le))
    (fun p hp ↦ by positivity)
    (fun S hSP p hpS ↦ primeSubsetClusterTerm_le_delete hSP hpS)
  have hA :
      (∑ p ∈ primesUpTo P, (2 / (p : ℝ)) * Real.log (p : ℝ)) =
        2 * weightedPrimeLogMass P := by
    rw [weightedPrimeLogMass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hB :
      (∑ p ∈ primesUpTo P,
          (2 / (p : ℝ)) * Real.log (p : ℝ) ^ 2) =
        2 * primeLogMoment 2 P := by
    rw [primeLogMoment, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hC :
      (∑ p ∈ primesUpTo P,
          (2 / (p : ℝ)) * Real.log (p : ℝ) ^ 3) =
        2 * primeLogMoment 3 P := by
    rw [primeLogMoment, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hA, hB, hC] at h
  exact h

/-- Ford's cubic moment is `O(log^3 P)` times the unweighted cluster mass,
with one absolute constant and no analytic assumptions left open. -/
theorem exists_pos_squarefreeClusterLogMoment_le :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℕ, 2 ≤ P →
      squarefreeClusterLogMoment P ≤
        C * Real.log (P : ℝ) ^ 3 * squarefreeClusterMass P := by
  obtain ⟨K, hK, hmass⟩ := exists_pos_weightedPrimeLogMass_le_log
  let C : ℝ := 8 * K ^ 3 + 12 * K ^ 2 + 2 * K
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, fun P hP ↦ ?_⟩
  let W := weightedPrimeLogMass P
  let L := Real.log (P : ℝ)
  have hL : 0 ≤ L := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ P by omega))
  have hW : 0 ≤ W := weightedPrimeLogMass_nonneg P
  have hWL : W ≤ K * L := hmass P hP
  have hM2 : primeLogMoment 2 P ≤ L * W := by
    simpa only [L, Nat.reduceSubDiff, pow_one] using primeLogMoment_two_le P
  have hM3 : primeLogMoment 3 P ≤ L ^ 2 * W := by
    simpa only [L, Nat.reduceSubDiff] using primeLogMoment_three_le P
  have hMass : 0 ≤ squarefreeClusterMass P := by
    rw [squarefreeClusterMass_eq_powersetMoment_zero]
    apply Finset.sum_nonneg
    intro S hS
    simpa [powersetAdditiveMoment] using primeSubsetClusterTerm_nonneg S
  have hpoly :
      (2 * W) ^ 3 + 3 * (2 * W) * (2 * primeLogMoment 2 P) +
          2 * primeLogMoment 3 P ≤ C * L ^ 3 := by
    have hK0 : 0 ≤ K := hK.le
    have hM20 : 0 ≤ primeLogMoment 2 P := by
      unfold primeLogMoment
      exact Finset.sum_nonneg fun p hp ↦ by positivity
    have hM30 : 0 ≤ primeLogMoment 3 P := by
      unfold primeLogMoment
      exact Finset.sum_nonneg fun p hp ↦ by positivity
    calc
      (2 * W) ^ 3 + 3 * (2 * W) * (2 * primeLogMoment 2 P) +
          2 * primeLogMoment 3 P ≤
          (2 * (K * L)) ^ 3 +
            3 * (2 * (K * L)) * (2 * (L * W)) +
            2 * (L ^ 2 * W) := by
        gcongr
      _ ≤ (2 * (K * L)) ^ 3 +
            3 * (2 * (K * L)) * (2 * (L * (K * L))) +
            2 * (L ^ 2 * (K * L)) := by
        gcongr
      _ = C * L ^ 3 := by
        dsimp [C]
        ring
  calc
    squarefreeClusterLogMoment P ≤
        ((2 * W) ^ 3 + 3 * (2 * W) * (2 * primeLogMoment 2 P) +
          2 * primeLogMoment 3 P) * squarefreeClusterMass P := by
      simpa only [W] using squarefreeClusterLogMoment_le_primeMoments P
    _ ≤ (C * L ^ 3) * squarefreeClusterMass P :=
      mul_le_mul_of_nonneg_right hpoly hMass
    _ = C * Real.log (P : ℝ) ^ 3 * squarefreeClusterMass P := by
      simp only [L]

end Erdos446
