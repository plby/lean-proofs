/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.ExactMultiplicityConstruction
import ErdosProblems.Erdos446.ExactValuationFamily
import ErdosProblems.Erdos446.IsolatedPrimeSelection
import ErdosProblems.Erdos446.FixedMultiplicityModuliMass

/-!
# Erdős Problem 446: the exact fixed-multiplicity modulus family

This file assembles the elementary arithmetic part of Ford's prescribed
multiplicity construction.  For every small factor `a`, choose `r` primes
from the disjoint dyadic windows indexed by the `log 2`-isolated divisors of
`a`.  Under `2a² < y`, the resulting modulus has exactly `r` divisors in
`(y,2y]`.  A common prime cutoff gives unique small/outer factorization, so
the reciprocal mass of these moduli is exactly the elementary prime-selection
mass, with no overcounting loss.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The exact-multiplicity moduli generated from a finite small-factor
family. -/
noncomputable def isolatedExactModuli
    (y r : ℕ) (A : Finset ℕ) : Finset ℕ :=
  smallOuterModuli A (fun a ↦ isolatedOuterPrimeSets y a r)

/-- Every admissible outer-prime set gives exactly the prescribed number of
dyadic divisors. -/
theorem divisorCountIoc_smallOuterModulus_eq
    {y a r : ℕ} {P : Finset ℕ}
    (hy : 0 < y) (ha : 0 < a) (hasmall : 2 * a * a < y)
    (hP : P ∈ isolatedOuterPrimeSets y a r) :
    divisorCountIoc y (2 * y) (a * ∏ p ∈ P, p) = r := by
  obtain ⟨hPsub, hPcard⟩ := mem_isolatedOuterPrimeSets.mp hP
  have haa : a * a < y := by
    calc
      a * a ≤ 2 * (a * a) :=
        Nat.le_mul_of_pos_left (a * a) (by omega : 0 < 2)
      _ = 2 * a * a := by ring
      _ < y := hasmall
  have hay : a ≤ y := by
    have hle : a ≤ a * a := Nat.le_mul_of_pos_right a ha
    omega
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_isolatedDyadicPrimeSupport (hPsub hp)
  have hlarge : ∀ p ∈ P, a < p := by
    intro p hp
    exact smallFactor_lt_of_mem_isolatedDyadicPrimeSupport
      ha haa (hPsub hp)
  have hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * y < p * q := by
    intro p hp q hq hpq
    exact two_mul_y_lt_mul_of_mem_isolatedDyadicPrimeSupport
      ha hy hasmall (hPsub hp) (hPsub hq)
  have hiso : ∀ p ∈ P, ∃ d,
      d ∈ sigmaIsolatedDivisors a (Real.log 2) ∧
        y < d * p ∧ d * p ≤ 2 * y := by
    intro p hp
    obtain ⟨d, hdIso, hdLower, hdUpper, hdUnique⟩ :=
      exists_unique_eligible_isolated_divisor ha (hPsub hp)
    exact ⟨d, hdIso, hdLower, hdUpper⟩
  rw [divisorCountIoc_mul_primeProd_eq_card_of_sigmaIsolated
    hy ha hay hprime hlarge hsep hiso, hPcard]

/-- Every modulus in the assembled family has exact multiplicity `r`. -/
theorem divisorCountIoc_eq_of_mem_isolatedExactModuli
    {y r : ℕ} {A : Finset ℕ}
    (hy : 0 < y)
    (hApos : ∀ a ∈ A, 0 < a)
    (hAsmall : ∀ a ∈ A, 2 * a * a < y) :
    ∀ c ∈ isolatedExactModuli y r A,
      divisorCountIoc y (2 * y) c = r := by
  apply property_of_mem_smallOuterModuli
  intro a ha P hP
  exact divisorCountIoc_smallOuterModulus_eq
    hy (hApos a ha) (hAsmall a ha) hP

/-- A modulus in the family is squarefree when the small factor is
squarefree and a cutoff separates all its prime factors from the isolated
prime support. -/
theorem squarefree_of_mem_isolatedExactModuli
    {y r L : ℕ} {A : Finset ℕ}
    (hAsq : ∀ a ∈ A, Squarefree a)
    (hAcut : ∀ a ∈ A, ∀ p ∈ a.primeFactors, p ≤ L)
    (houter : ∀ a ∈ A, ∀ p ∈ isolatedDyadicPrimeSupport y a,
      L < p) :
    ∀ c ∈ isolatedExactModuli y r A, Squarefree c := by
  apply property_of_mem_smallOuterModuli
  intro a ha P hP
  obtain ⟨hPsub, hPcard⟩ := mem_isolatedOuterPrimeSets.mp hP
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_isolatedDyadicPrimeSupport (hPsub hp)
  have hprodSq : Squarefree (∏ p ∈ P, p) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_
      (fun p hp ↦ (hprime p hp).squarefree)
    intro p hp q hq hpq
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq
  have hcop : a.Coprime (∏ p ∈ P, p) := by
    rw [Nat.coprime_prod_right_iff]
    intro p hp
    have hpPrime := hprime p hp
    have hpNotDvd : ¬p ∣ a := by
      intro hpDvd
      have hpPF : p ∈ a.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpPrime, hpDvd, (hAsq a ha).ne_zero⟩
      have hpLe := hAcut a ha p hpPF
      have hpGt := houter a ha p (hPsub hp)
      omega
    exact (hpPrime.coprime_iff_not_dvd.mpr hpNotDvd).symm
  exact (Nat.squarefree_mul hcop).mpr ⟨hAsq a ha, hprodSq⟩

/-- If every small factor is at most `2y`, then every prime factor of every
constructed exact modulus is at most `2y`.  The outer-prime part needs no
extra hypothesis: it is built from dyadic intervals ending at `2y/d`. -/
theorem primeFactorsAtMost_two_mul_y_of_mem_isolatedExactModuli
    {y r : ℕ} {A : Finset ℕ}
    (hApos : ∀ a ∈ A, 0 < a)
    (hAbound : ∀ a ∈ A, a ≤ 2 * y) :
    ∀ c ∈ isolatedExactModuli y r A,
      PrimeFactorsAtMost (2 * y) c := by
  apply property_of_mem_smallOuterModuli
  intro a ha P hP
  obtain ⟨hPsub, hPcard⟩ := mem_isolatedOuterPrimeSets.mp hP
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_isolatedDyadicPrimeSupport (hPsub hp)
  have hprodPos : 0 < ∏ p ∈ P, p := by
    apply Finset.prod_pos
    intro p hp
    exact (hprime p hp).pos
  intro q hq
  rw [Nat.primeFactors_mul (hApos a ha).ne' hprodPos.ne',
    Nat.primeFactors_prod hprime] at hq
  rcases Finset.mem_union.mp hq with hqa | hqP
  · exact (Nat.le_of_dvd (hApos a ha)
      (Nat.dvd_of_mem_primeFactors hqa)).trans (hAbound a ha)
  · exact le_two_mul_y_of_mem_isolatedDyadicPrimeSupport (hPsub hqP)

/-- Direct exact-valuation CRT lower bound for the assembled isolated-prime
family. -/
theorem isolatedExactModuli_density_lower
    {y r L : ℕ} (A : Finset ℕ)
    (hy : 0 < y)
    (hApos : ∀ a ∈ A, 0 < a)
    (hAsq : ∀ a ∈ A, Squarefree a)
    (hAsmall : ∀ a ∈ A, 2 * a * a < y)
    (hAbound : ∀ a ∈ A, a ≤ 2 * y)
    (hAcut : ∀ a ∈ A, ∀ p ∈ a.primeFactors, p ≤ L)
    (houter : ∀ a ∈ A, ∀ p ∈ isolatedDyadicPrimeSupport y a,
      L < p) :
    smallPrimeEulerDensity (2 * y) *
        (∑ c ∈ isolatedExactModuli y r A, 1 / (c : ℝ)) ≤
      epsilonR r y (2 * y) := by
  apply exactMultiplicity_squarefree_family_lower_bound
    hy le_rfl
  · intro c hc
    change c ∈ smallOuterModuli A
      (fun a ↦ isolatedOuterPrimeSets y a r) at hc
    obtain ⟨a, ha, P, hP, rfl⟩ := mem_smallOuterModuli.mp hc
    apply Nat.mul_pos (hApos a ha)
    apply Finset.prod_pos
    intro p hp
    exact (prime_of_mem_isolatedDyadicPrimeSupport
      ((mem_isolatedOuterPrimeSets.mp hP).1 hp)).pos
  · exact squarefree_of_mem_isolatedExactModuli hAsq hAcut houter
  · exact primeFactorsAtMost_two_mul_y_of_mem_isolatedExactModuli
      hApos hAbound
  · exact divisorCountIoc_eq_of_mem_isolatedExactModuli hy hApos hAsmall

/-- The common cutoff separation makes the small/outer representation
injective on the exact-multiplicity construction. -/
theorem isolatedExactModuli_factorization_injective
    (y r L : ℕ) (A : Finset ℕ)
    (hApos : ∀ a ∈ A, 0 < a)
    (hAsq : ∀ a ∈ A, Squarefree a)
    (hAcut : ∀ a ∈ A, ∀ p ∈ a.primeFactors, p ≤ L)
    (houter : ∀ a ∈ A, ∀ p ∈ isolatedDyadicPrimeSupport y a,
      L < p) :
    Set.InjOn smallOuterModulus
      (smallOuterPairs A (fun a ↦ isolatedOuterPrimeSets y a r)) := by
  apply smallOuterModulus_injOn_of_prime_separation L A
    (fun a ↦ isolatedOuterPrimeSets y a r) hApos hAsq hAcut
  · intro a ha P hP p hp
    exact prime_of_mem_isolatedDyadicPrimeSupport
      ((mem_isolatedOuterPrimeSets.mp hP).1 hp)
  · intro a ha P hP p hp
    exact houter a ha p ((mem_isolatedOuterPrimeSets.mp hP).1 hp)

/-- Exact reciprocal-mass lower bound for the assembled squarefree family.
This is the finite bridge from the isolated-divisor moment to the
exact-multiplicity CRT sieve. -/
theorem sum_isolatedCount_mass_le_reciprocal_isolatedExactModuli
    {N y r L : ℕ} (A : Finset ℕ)
    (hN : 3 ≤ N)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x)
    (hApos : ∀ a ∈ A, 0 < a)
    (hAsq : ∀ a ∈ A, Squarefree a)
    (hAcut : ∀ a ∈ A, ∀ p ∈ a.primeFactors, p ≤ L)
    (houter : ∀ a ∈ A, ∀ p ∈ isolatedDyadicPrimeSupport y a,
      L < p)
    (hscale : ∀ a ∈ A, ∀ d ∈ a.divisors,
      N ≤ y / d ∧ y ≤ (y / d) ^ 2)
    (hatom : ∀ a ∈ A,
      (r : ℝ) * ((a : ℝ) / (y : ℝ)) ≤
        isolatedDyadicPrimeMass y a / 2) :
    (∑ a ∈ A,
        (((sigmaIsolatedCount a (Real.log 2) : ℝ) *
          ((1 / 4 : ℝ) / Real.log (y : ℝ))) / 2) ^ r /
          (r.factorial : ℝ) / (a : ℝ)) ≤
      ∑ c ∈ isolatedExactModuli y r A, 1 / (c : ℝ) := by
  let F : ℕ → Finset (Finset ℕ) :=
    fun a ↦ isolatedOuterPrimeSets y a r
  have hinj : Set.InjOn smallOuterModulus (smallOuterPairs A F) := by
    exact isolatedExactModuli_factorization_injective
      y r L A hApos hAsq hAcut houter
  change (∑ a ∈ A,
      (((sigmaIsolatedCount a (Real.log 2) : ℝ) *
        ((1 / 4 : ℝ) / Real.log (y : ℝ))) / 2) ^ r /
        (r.factorial : ℝ) / (a : ℝ)) ≤
    ∑ c ∈ smallOuterModuli A F, 1 / (c : ℝ)
  apply sum_smallFactorMass_le_sum_reciprocal_smallOuterModuli
    A F
      (fun a ↦ (((sigmaIsolatedCount a (Real.log 2) : ℝ) *
        ((1 / 4 : ℝ) / Real.log (y : ℝ))) / 2) ^ r /
          (r.factorial : ℝ))
      hinj hApos
  intro a ha
  exact isolatedCount_pow_mass_lower hN hprime (hApos a ha)
    (hscale a ha) (hatom a ha)

/-- Full density-level arithmetic bridge.  The isolated-divisor moment on a
finite squarefree block family, the reciprocal-prime selection estimate, the
small/outer factorization, and the exact-valuation CRT sieve are all combined
here.  Only the later block-asymptotic lower bound for the displayed finite
sum remains. -/
theorem isolatedCount_mass_density_lower
    {N y r L : ℕ} (A : Finset ℕ)
    (hy : 0 < y)
    (hN : 3 ≤ N)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x)
    (hApos : ∀ a ∈ A, 0 < a)
    (hAsq : ∀ a ∈ A, Squarefree a)
    (hAsmall : ∀ a ∈ A, 2 * a * a < y)
    (hAbound : ∀ a ∈ A, a ≤ 2 * y)
    (hAcut : ∀ a ∈ A, ∀ p ∈ a.primeFactors, p ≤ L)
    (houter : ∀ a ∈ A, ∀ p ∈ isolatedDyadicPrimeSupport y a,
      L < p)
    (hscale : ∀ a ∈ A, ∀ d ∈ a.divisors,
      N ≤ y / d ∧ y ≤ (y / d) ^ 2)
    (hatom : ∀ a ∈ A,
      (r : ℝ) * ((a : ℝ) / (y : ℝ)) ≤
        isolatedDyadicPrimeMass y a / 2) :
    smallPrimeEulerDensity (2 * y) *
        (∑ a ∈ A,
          (((sigmaIsolatedCount a (Real.log 2) : ℝ) *
            ((1 / 4 : ℝ) / Real.log (y : ℝ))) / 2) ^ r /
            (r.factorial : ℝ) / (a : ℝ)) ≤
      epsilonR r y (2 * y) := by
  have hmass := sum_isolatedCount_mass_le_reciprocal_isolatedExactModuli
    A hN hprime hApos hAsq hAcut houter hscale hatom
  have heuler : 0 ≤ smallPrimeEulerDensity (2 * y) :=
    smallPrimeEulerDensity_nonneg _
  calc
    smallPrimeEulerDensity (2 * y) *
        (∑ a ∈ A,
          (((sigmaIsolatedCount a (Real.log 2) : ℝ) *
            ((1 / 4 : ℝ) / Real.log (y : ℝ))) / 2) ^ r /
            (r.factorial : ℝ) / (a : ℝ)) ≤
      smallPrimeEulerDensity (2 * y) *
        (∑ c ∈ isolatedExactModuli y r A, 1 / (c : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass heuler
    _ ≤ epsilonR r y (2 * y) :=
      isolatedExactModuli_density_lower A hy hApos hAsq hAsmall
        hAbound hAcut houter

end Erdos446
