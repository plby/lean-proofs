/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.ClosePrimeCandidates
import ErdosProblems.Erdos387.BrunSieve

/-!
# Erdős Problem 446: squarefree divisors as prime subsets

For a product of distinct primes, divisors are products of unique prime
subsets.  Consequently Ford's close-divisor count is exactly a count of
ordered pairs of subsets satisfying the logarithmic closeness condition.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable def subsetClosePairs (S : Finset ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  (S.powerset ×ˢ S.powerset).filter fun DE ↦
    |Real.log ((DE.1.prod id : ℕ) : ℝ) -
      Real.log ((DE.2.prod id : ℕ) : ℝ)| ≤ Real.log 2

theorem mem_subsetClosePairs {S D E : Finset ℕ} :
    (D, E) ∈ subsetClosePairs S ↔
      D ⊆ S ∧ E ⊆ S ∧
        |Real.log ((D.prod id : ℕ) : ℝ) -
          Real.log ((E.prod id : ℕ) : ℝ)| ≤ Real.log 2 := by
  simp [subsetClosePairs, and_assoc]

theorem primeSubsetProduct_injOn {S : Finset ℕ}
    (hSprime : ∀ p ∈ S, p.Prime) :
    Set.InjOn (fun T : Finset ℕ ↦ T.prod id) S.powerset := by
  intro A hA B hB hprod
  have hAprime : ∀ p ∈ A, p.Prime := fun p hp ↦
    hSprime p ((Finset.mem_powerset.mp hA) hp)
  have hBprime : ∀ p ∈ B, p.Prime := fun p hp ↦
    hSprime p ((Finset.mem_powerset.mp hB) hp)
  rw [← Nat.primeFactors_prod hAprime,
    ← Nat.primeFactors_prod hBprime]
  exact congrArg Nat.primeFactors hprod

theorem divisors_primeSelectionProduct {S : Finset ℕ}
    (hSprime : ∀ p ∈ S, p.Prime) :
    (S.prod id).divisors =
      S.powerset.image (fun T : Finset ℕ ↦ T.prod id) := by
  have hsq : Squarefree (S.prod id) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_
      (fun p hp ↦ (hSprime p hp).squarefree)
    intro p hp q hq hpq
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hSprime p hp) (hSprime q hq)).mpr hpq
  have hpf : (S.prod id).primeFactors = S := by
    exact Nat.primeFactors_prod hSprime
  rw [Erdos387.divisors_eq_image_prod_primeFactorSubsets hsq, hpf]
  simp

theorem closePairCount_primeSelectionProduct {S : Finset ℕ}
    (hSprime : ∀ p ∈ S, p.Prime) :
    closePairCount (S.prod id) = (subsetClosePairs S).card := by
  classical
  rw [closePairCount]
  symm
  apply Finset.card_bij
      (fun DE _ ↦ (DE.1.prod id, DE.2.prod id))
  · intro DE hDE
    rw [closeDivisorPairs, Finset.mem_filter]
    have hmem := mem_subsetClosePairs.mp hDE
    rw [divisors_primeSelectionProduct hSprime]
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨DE.1, Finset.mem_powerset.mpr hmem.1, rfl⟩,
       Finset.mem_image.mpr ⟨DE.2, Finset.mem_powerset.mpr hmem.2.1, rfl⟩⟩,
      hmem.2.2⟩
  · intro A hA B hB hEq
    apply Prod.ext
    · apply primeSubsetProduct_injOn hSprime
        (Finset.mem_powerset.mpr (mem_subsetClosePairs.mp hA).1)
        (Finset.mem_powerset.mpr (mem_subsetClosePairs.mp hB).1)
      exact congrArg Prod.fst hEq
    · apply primeSubsetProduct_injOn hSprime
        (Finset.mem_powerset.mpr (mem_subsetClosePairs.mp hA).2.1)
        (Finset.mem_powerset.mpr (mem_subsetClosePairs.mp hB).2.1)
      exact congrArg Prod.snd hEq
  · intro de hde
    rw [closeDivisorPairs, Finset.mem_filter] at hde
    rcases hde with ⟨hdiv, hclose⟩
    rw [divisors_primeSelectionProduct hSprime] at hdiv
    obtain ⟨D, hD, hDprod⟩ := Finset.mem_image.mp
      (Finset.mem_product.mp hdiv).1
    obtain ⟨E, hE, hEprod⟩ := Finset.mem_image.mp
      (Finset.mem_product.mp hdiv).2
    refine ⟨(D, E), ?_, ?_⟩
    · apply mem_subsetClosePairs.mpr
      refine ⟨Finset.mem_powerset.mp hD,
        Finset.mem_powerset.mp hE, ?_⟩
      simpa only [hDprod, hEprod] using hclose
    · exact Prod.ext hDprod hEprod

end Erdos446
