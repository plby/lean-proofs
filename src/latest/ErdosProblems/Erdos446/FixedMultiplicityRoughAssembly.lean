/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedMultiplicityExactFamily
import ErdosProblems.Erdos446.FixedMultiplicityRoughReduction

/-!
# Erdős Problem 446: assembling isolated primes with the rough sieve

The exact moduli constructed from isolated divisors have all prime factors
at most `2y`.  We can therefore feed the whole family into the exact rough
factor sieve at cutoff `2y`.  This produces a genuine lower bound for
`epsilonR`, with no abstract finite-count hypothesis between the isolated
divisor moment and the exact-multiplicity density.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Complete finite form of the initial exact-multiplicity reduction:
isolated-divisor mass, `r` distinguished primes, unique smooth/rough
factorization, and the lower rough-number sieve are combined in one
inequality for `epsilonR`. -/
theorem epsilonR_lower_of_isolatedExactModuli
    {N y r L : ℕ} (A : Finset ℕ)
    (hN : 3 ≤ N) (hy : 0 < y)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x)
    (hApos : ∀ a ∈ A, 0 < a)
    (hAsq : ∀ a ∈ A, Squarefree a)
    (hAcut : ∀ a ∈ A, ∀ p ∈ a.primeFactors, p ≤ L)
    (houter : ∀ a ∈ A, ∀ p ∈ isolatedDyadicPrimeSupport y a,
      L < p)
    (hAsmall : ∀ a ∈ A, 2 * a * a < y)
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
  let C : Finset ℕ := isolatedExactModuli y r A
  have hCmass :
      (∑ a ∈ A,
          (((sigmaIsolatedCount a (Real.log 2) : ℝ) *
            ((1 / 4 : ℝ) / Real.log (y : ℝ))) / 2) ^ r /
            (r.factorial : ℝ) / (a : ℝ)) ≤
        ∑ c ∈ C, 1 / (c : ℝ) := by
    exact sum_isolatedCount_mass_le_reciprocal_isolatedExactModuli A hN
      hprime hApos hAsq hAcut houter hscale hatom
  have hCsq : ∀ c ∈ C, Squarefree c := by
    exact squarefree_of_mem_isolatedExactModuli hAsq hAcut houter
  have hCpos : ∀ c ∈ C, 0 < c := by
    intro c hc
    exact Nat.pos_of_ne_zero ((hCsq c hc).ne_zero)
  have hCcut : ∀ c ∈ C, PrimeFactorsAtMost (2 * y) c := by
    have hAbound : ∀ a ∈ A, a ≤ 2 * y := by
      intro a ha
      have haa : a ≤ a * a := Nat.le_mul_of_pos_right a (hApos a ha)
      have haaY : a * a < y := by
        calc
          a * a ≤ 2 * (a * a) :=
            Nat.le_mul_of_pos_left (a * a) (by omega : 0 < 2)
          _ = 2 * a * a := by ring
          _ < y := hAsmall a ha
      have hay : a ≤ y := haa.trans haaY.le
      omega
    exact primeFactorsAtMost_two_mul_y_of_mem_isolatedExactModuli
      hApos hAbound
  have hCexact : ∀ c ∈ C, divisorCountIoc y (2 * y) c = r := by
    exact divisorCountIoc_eq_of_mem_isolatedExactModuli hy hApos hAsmall
  have hsieve :
      smallPrimeEulerDensity (2 * y) * (∑ c ∈ C, 1 / (c : ℝ)) ≤
        epsilonR r y (2 * y) :=
    exactMultiplicity_roughFamily_lower hy le_rfl hCpos hCcut hCexact
  exact (mul_le_mul_of_nonneg_left hCmass
    (smallPrimeEulerDensity_nonneg (2 * y))).trans hsieve

end Erdos446
